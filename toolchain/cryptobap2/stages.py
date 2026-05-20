from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
from pathlib import Path
from typing import Any

from .binary_model import BINARY_MODEL_SCHEMA, binary_model_path, finalize_binary_model
from .config import CaseConfig
from .manifest import BuildLayout, case_config_sha256, ensure_layout, load_manifest, sha256_file, update_manifest
from .hol_support import (
    HolSupportError,
    clear_legacy_case_source_view,
    holmake_includes,
    stage_hol_sources as _stage_hol_sources,
)
from .paths import DEFAULT_HOLBA_DIR, DEFAULT_HOLMAKE
from .sapic_format import format_sapic_text
from .stage_coverage import parse_lifted_labels, sapic_translation_coverage, validate_fragment_labels
from .source_segments import write_source_segment_files


class StageError(RuntimeError):
    pass


def stage_hol_sources(
    layout: BuildLayout,
    *,
    holmake: Path = DEFAULT_HOLMAKE,
    holba: Path = DEFAULT_HOLBA_DIR,
) -> Path:
    try:
        return _stage_hol_sources(layout, holmake=holmake, holba=holba)
    except HolSupportError as exc:
        raise StageError(str(exc)) from exc


def _quote_sml(value: str | Path) -> str:
    text = str(value)
    escapes = {
        "\\": "\\\\",
        '"': '\\"',
        "\n": "\\n",
        "\r": "\\r",
        "\t": "\\t",
    }
    return '"' + "".join(escapes.get(char, char) for char in text) + '"'


def _safe_identifier(value: str) -> str:
    name = re.sub(r"[^A-Za-z0-9_]", "_", value)
    if not name or name[0].isdigit():
        name = "CryptoBAP2_" + name
    return name


def _yaml_scalar(value: object) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int):
        return str(value)
    if value is None:
        return "null"
    escapes = {
        "\\": "\\\\",
        '"': '\\"',
        "\n": "\\n",
        "\r": "\\r",
        "\t": "\\t",
    }
    return '"' + "".join(escapes.get(char, char) for char in str(value)) + '"'


def _label_term(value: int, arch: str) -> str:
    bit = "32" if arch.lower() in {"m0", "m0_mod", "arm-m0", "cortex-m0"} else "64"
    return f"``BL_Address (Imm{bit} {value}w)``"


def _sml_bool(value: bool) -> str:
    return "true" if value else "false"


def _case_uses_wildcard_symbols(case: CaseConfig) -> bool:
    return case.symbols == ["*"]


def _looks_local_label(name: str) -> bool:
    return name.startswith(("LAB_", ".L", "loc_"))


def _fragment_ranges(case: CaseConfig) -> list[tuple[int, int]]:
    ranges: list[tuple[int, int]] = []
    for fragment in case.fragments:
        if not isinstance(fragment, dict) or fragment.get("end_label") is None:
            continue
        try:
            start = int(fragment["entry_label"])
            end = int(fragment["end_label"])
        except (KeyError, TypeError, ValueError):
            continue
        if end > start:
            ranges.append((start, end))
    return ranges


def _lift_symbols_for_case(case: CaseConfig) -> list[str]:
    """Include Ghidra local labels that belong to configured fragments."""

    symbols: list[str] = []
    seen: set[str] = set()

    def add_symbol(name: str) -> None:
        if name not in seen:
            seen.add(name)
            symbols.append(name)

    for symbol in case.symbols:
        add_symbol(symbol)

    if _case_uses_wildcard_symbols(case) or case.input_da is None or not case.input_da.exists():
        return symbols

    ranges = _fragment_ranges(case)
    if not ranges:
        return symbols

    for raw in case.input_da.read_text(encoding="utf-8", errors="replace").splitlines():
        header = _DA_FUNCTION_HEADER_RE.match(raw.strip())
        if header is None:
            continue
        label = int(header.group(1), 16)
        name = header.group(2)
        if _looks_local_label(name) and any(start < label < end for start, end in ranges):
            add_symbol(name)

    return symbols


def _execution_bool_flag(case: CaseConfig, name: str) -> bool:
    value = case.execution.get(name, False)
    if not isinstance(value, bool):
        raise StageError(f"execution.{name} must be a boolean")
    return value


def _stub_unclassified_calls(case: CaseConfig) -> bool:
    return _execution_bool_flag(case, "stub_unclassified_calls")


def _allow_unmapped_memory_overapprox(case: CaseConfig) -> bool:
    return _execution_bool_flag(case, "allow_unmapped_memory_overapprox")


def _write_json(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _write_log(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _json_literal_for_sml(data: Any) -> str:
    return _quote_sml(json.dumps(data, sort_keys=True, default=str))


def _artifact_hash_matches(manifest: dict[str, Any], name: str, path: Path) -> bool:
    record = manifest.get("artifacts", {}).get(name)
    if not isinstance(record, dict) or not path.exists():
        return False
    expected = record.get("sha256")
    return isinstance(expected, str) and sha256_file(path) == expected


def _lift_fingerprint(
    case: CaseConfig,
    *,
    holmake: Path = DEFAULT_HOLMAKE,
    holba: Path = DEFAULT_HOLBA_DIR,
) -> dict[str, Any]:
    return {
        "arch": case.arch,
        "theory": _safe_identifier(case.theory),
        "input_da": str(case.input_da) if case.input_da else None,
        "input_sha256": sha256_file(case.input_da) if case.input_da and case.input_da.exists() else None,
        "symbols": _lift_symbols_for_case(case),
        "sections": case.disassembly_sections,
        "holmake": str(holmake),
        "holba": str(holba),
    }


def lift_stage_is_current(
    case: CaseConfig,
    layout: BuildLayout,
    *,
    holmake: Path = DEFAULT_HOLMAKE,
    holba: Path = DEFAULT_HOLBA_DIR,
) -> bool:
    theory_obj = layout.work / ".hol" / "objs" / f"{_safe_identifier(case.theory)}Theory.uo"
    if not theory_obj.exists():
        return False
    manifest = load_manifest(layout.manifest_path)
    stage = manifest.get("stages", {}).get("lift") if manifest else None
    if not isinstance(stage, dict) or stage.get("status") != "generated_unchecked":
        return False
    for key, expected in _lift_fingerprint(case, holmake=holmake, holba=holba).items():
        if stage.get(key) != expected:
            return False
    return _artifact_hash_matches(manifest, "lifted_theory_uo", theory_obj)


_DA_FUNCTION_HEADER_RE = re.compile(r"^([0-9A-Fa-f]+)\s+<([^>]+)>:")


def _yaml_named_list(indent: int, name: str, values: list[str]) -> list[str]:
    pad = " " * indent
    if not values:
        return [f"{pad}{name}: []"]
    return [f"{pad}{name}:", *[f"{pad}  - {_yaml_scalar(value)}" for value in values]]


def _write_symexec_pipeline_yaml(case: CaseConfig, layout: BuildLayout, sapic_output: Path) -> Path:
    functions = case.raw.get("functions", {}) if isinstance(case.raw.get("functions"), dict) else {}
    library = [str(item) for item in functions.get("library", [])] if isinstance(functions.get("library", []), list) else []
    adversary = [str(item) for item in functions.get("adversary", [])] if isinstance(functions.get("adversary", []), list) else []
    crypto = functions.get("crypto", {}) if isinstance(functions.get("crypto", {}), dict) else {}
    callsite_crypto = (
        functions.get("crypto_callsite_labels", {})
        if isinstance(functions.get("crypto_callsite_labels", {}), dict)
        else {}
    )
    extra_variables = case.execution.get("extra_variables", [])
    extra_lines: list[str] = []
    if isinstance(extra_variables, list) and extra_variables:
        for variable in extra_variables:
            if isinstance(variable, dict):
                extra_lines.extend(
                    [
                        f"    - name: {_yaml_scalar(variable.get('name', ''))}",
                        f"      type: {_yaml_scalar(variable.get('type', 'Imm'))}",
                        f"      width: {int(variable.get('width', 64))}",
                    ]
                )
    extra_block = ["  extra_variables:", *extra_lines] if extra_lines else ["  extra_variables: []"]
    crypto_lines = [
        f"  {_yaml_scalar(name)}: {_yaml_scalar(label)}"
        for name, label in sorted((str(k), str(v)) for k, v in crypto.items())
    ]
    crypto_block = ["cryptographic_functions:", *crypto_lines] if crypto_lines else ["cryptographic_functions: {}"]
    callsite_crypto_lines = [
        f"  {_yaml_scalar(int(label))}: {_yaml_scalar(crypto_label)}"
        for label, crypto_label in sorted((int(k), str(v)) for k, v in callsite_crypto.items())
    ]
    callsite_crypto_block = (
        ["cryptographic_callsite_labels:", *callsite_crypto_lines]
        if callsite_crypto_lines
        else ["cryptographic_callsite_labels: {}"]
    )
    fragment = case.fragments[0] if case.fragments else {"entry_label": 0, "exit_labels": []}
    first_exits = [int(label) for label in fragment.get("exit_labels", [])]
    exit_block = ["  exit_labels:", *[f"    - {label}" for label in first_exits]] if first_exits else ["  exit_labels: []"]
    fragment_lines: list[str] = []
    for item in case.fragments:
        if not isinstance(item, dict):
            continue
        fragment_lines.extend(
            [
                f"    - name: {_yaml_scalar(item.get('name', 'fragment'))}",
                f"      entry_label: {int(item.get('entry_label', 0))}",
            ]
        )
        if item.get("end_label") is not None:
            fragment_lines.append(f"      end_label: {int(item.get('end_label', 0))}")
        exits = [int(label) for label in item.get("exit_labels", [])]
        if exits:
            fragment_lines.append("      exit_labels:")
            fragment_lines.extend(f"        - {label}" for label in exits)
        else:
            fragment_lines.append("      exit_labels: []")
    if not fragment_lines:
        fragment_lines.append("    []")
    yaml_text = "\n".join(
        [
            "pipeline:",
            f"  theory: {_yaml_scalar(_safe_identifier(case.theory))}",
            f"  entry_label: {int(fragment['entry_label'])}",
            *exit_block,
            *extra_block,
            f"  stub_unclassified_calls: {_sml_bool(_stub_unclassified_calls(case))}",
            f"  allow_unmapped_memory_overapprox: {_sml_bool(_allow_unmapped_memory_overapprox(case))}",
            f"  output_file: {_yaml_scalar(sapic_output.resolve())}",
            "  fragments:",
            *fragment_lines,
            "functions:",
            *_yaml_named_list(2, "library", library),
            *_yaml_named_list(2, "adversary", adversary),
            *crypto_block,
            *callsite_crypto_block,
            "arities:",
            "  library: 2",
            "  adversary: 1",
            "events: []",
            "",
        ]
    )
    path = layout.work / "pipeline.yaml"
    path.write_text(yaml_text, encoding="utf-8")
    return path


def _holmakefile_content(layout: BuildLayout, source_root: Path | None = None) -> str:
    source_setting = ""
    if source_root is not None:
        source_setting = f"CRYPTOBAP2_SRC = {source_root.resolve()}\n"
    return f"""HOLBA_ROOT = $(if $(HOLBADIR),$(HOLBADIR),$(HOLBA_DIR))
{source_setting}
{holmake_includes(source_root)}

OPTIONS = QUIT_ON_FAILURE

all: $(DEFAULT_TARGETS)
.PHONY: all
"""


def _lifter_function(arch: str) -> str:
    lowered = arch.lower()
    if lowered in {"arm8", "aarch64"}:
        return "bmil_arm8.bir_lift_prog_gen"
    if lowered in {"m0", "m0_mod", "arm-m0", "cortex-m0"}:
        return "bmil_m0_mod_LittleEnd_Process.bir_lift_prog_gen"
    raise StageError(f"unsupported architecture for generated HOL lift runner: {arch}")


def generate_lift_runner(case: CaseConfig, layout: BuildLayout) -> dict[str, Path | None]:
    ensure_layout(layout)
    clear_legacy_case_source_view(layout)
    if case.input_da is None:
        raise StageError("case has no input.da")
    theory = _safe_identifier(case.theory)
    script = layout.work / f"{theory}Script.sml"
    holmakefile = layout.work / "Holmakefile"
    holmakefile_snapshot = layout.work / "Holmakefile.lift"
    label_dump = layout.bir / "lifted-program-labels.txt"
    lift_symbols = _lift_symbols_for_case(case)
    symbol_lines = ",\n".join(f"  {_quote_sml(symbol)}" for symbol in lift_symbols)
    section_lines = ",\n".join(f"  {_quote_sml(section)}" for section in case.disassembly_sections)
    lifter = _lifter_function(case.arch)
    content = f"""open HolKernel Parse
open PPBackEnd;
open bir_update_blockTheory;
open bir_inst_liftingTheory;

open bir_inst_liftingLib;
open bir_inst_liftingHelpersLib;
open bir_lifter_simple_interfaceLib;
open gcc_supportLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;

val _ = new_theory {_quote_sml(theory)};

val arch_str = {_quote_sml(case.arch)};
val dafilename = {_quote_sml(case.input_da.resolve())};
val symbs_sec_text = [
{symbol_lines}
  ];
val selected_sections = [
{section_lines}
  ];
val lift_all_symbols = {_sml_bool(_case_uses_wildcard_symbols(case))};

fun list_has value items = List.exists (fn x => x = value) items;

val symb_filter_lift = fn secname =>
  if list_has "*" selected_sections orelse list_has secname selected_sections
  then (fn symbname => lift_all_symbols orelse list_has symbname symbs_sec_text)
  else (K false);

val (region_map, sections) = read_disassembly_file_regions_filter symb_filter_lift dafilename;
val prog_range = da_sections_minmax sections;
val (thm, errors) = {lifter} prog_range sections;
val _ = save_thm ({_quote_sml(theory + "_thm")}, thm);
val _ =
  let
    val (_, _, _, prog_tm) = (dest_bir_is_lifted_prog o concl) thm;
    val out_stream = TextIO.openOut {_quote_sml(label_dump.resolve())};
  in
    (TextIO.output (out_stream, term_to_string prog_tm); TextIO.closeOut out_stream)
  end;
val _ = export_theory();
"""
    holmake_text = _holmakefile_content(layout)
    holmakefile.write_text(holmake_text, encoding="utf-8")
    holmakefile_snapshot.write_text(holmake_text, encoding="utf-8")
    script.write_text(content, encoding="utf-8")
    return {"runner": script, "holmakefile": holmakefile_snapshot, "label_dump": label_dump, "hol_source_root": None}


def _run_holmake(layout: BuildLayout, target: str, log_path: Path, *, holmake: Path, holba: Path) -> subprocess.CompletedProcess[str]:
    if not holmake.exists():
        raise StageError(f"Holmake not found: {holmake}")
    env = os.environ.copy()
    env["HOLBA_DIR"] = str(holba)
    env["HOLBADIR"] = str(holba)
    result = subprocess.run(
        [str(holmake), target],
        cwd=str(layout.work.resolve()),
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    _write_log(log_path, result.stdout)
    return result


def run_lift_stage(
    case: CaseConfig,
    layout: BuildLayout,
    *,
    execute: bool = True,
    holmake: Path = DEFAULT_HOLMAKE,
    holba: Path = DEFAULT_HOLBA_DIR,
) -> dict[str, Any]:
    artifacts = generate_lift_runner(case, layout)
    theory = _safe_identifier(case.theory)
    hol_source_root = artifacts["hol_source_root"]
    request = {
        "stage": "lift",
        "status": "configured",
        **_lift_fingerprint(case, holmake=holmake, holba=holba),
        "runner": str(artifacts["runner"]),
        "hol_source_root": str(hol_source_root) if hol_source_root is not None else None,
        "case_config_sha256": case_config_sha256(case),
    }
    request_path = layout.bir / "lift-request.json"
    _write_json(request_path, request)
    stage_data = dict(request)
    stage_data["runner_sha256"] = sha256_file(artifacts["runner"])
    stage_data["holmakefile_sha256"] = sha256_file(artifacts["holmakefile"])
    stage_data["holmake"] = str(holmake)
    stage_data["holba"] = str(holba)
    artifact_map = {
        "lift_request": request_path,
        "lift_runner": artifacts["runner"],
        "lift_holmakefile": artifacts["holmakefile"],
        "lifted_label_dump": artifacts["label_dump"],
    }
    if execute:
        log_path = layout.logs / "lift-holmake.log"
        result = _run_holmake(layout, f"{theory}Theory.uo", log_path, holmake=holmake, holba=holba)
        stage_data["status"] = "generated_unchecked" if result.returncode == 0 else "validation_failed"
        stage_data["exit_code"] = result.returncode
        stage_data["log"] = str(log_path)
        theory_obj = layout.work / ".hol" / "objs" / f"{theory}Theory.uo"
        artifact_map.update({"lift_log": log_path, "lifted_theory_uo": theory_obj})
        if result.returncode != 0:
            update_manifest(case, layout, command="lift", stage="lift", stage_data=stage_data, artifacts=artifact_map)
            raise StageError(f"HOL lift failed for {case.name}; see {log_path}")
        if not theory_obj.exists():
            stage_data["status"] = "validation_failed"
            stage_data.setdefault("diagnostics", []).append(
                {
                    "severity": "error",
                    "code": "missing_hol_artifact",
                    "message": f"HOL lift completed but did not produce {theory_obj}",
                }
            )
            update_manifest(case, layout, command="lift", stage="lift", stage_data=stage_data, artifacts=artifact_map)
            raise StageError(f"HOL lift did not produce expected theory object for {case.name}: {theory_obj}")
        if artifacts["label_dump"].exists():
            labels = sorted(parse_lifted_labels(artifacts["label_dump"].read_text(encoding="utf-8", errors="replace")))
            label_metadata = {
                "source": str(artifacts["label_dump"]),
                "source_sha256": sha256_file(artifacts["label_dump"]),
                "labels": labels,
            }
            label_metadata_path = layout.bir / "lifted-labels.json"
            _write_json(label_metadata_path, label_metadata)
            stage_data["label_count"] = len(labels)
            artifact_map["lifted_label_metadata"] = label_metadata_path

    artifact_map.update(write_source_segment_files(case, layout, folders=("bir",)))
    update_manifest(case, layout, command="lift", stage="lift", stage_data=stage_data, artifacts=artifact_map)
    return {"request": request_path, **artifacts, "stage": stage_data}


def _extra_var_terms(case: CaseConfig, base_vars: str = "prog_vars") -> str:
    terms: list[str] = []
    for variable in case.execution.get("extra_variables", []):
        if not isinstance(variable, dict):
            continue
        name = variable.get("name")
        kind = str(variable.get("type", "Imm")).lower()
        width = int(variable.get("width", 64))
        if not name:
            continue
        if kind == "imm":
            terms.append(
                f"bir_envSyntax.mk_BVar_string ({_quote_sml(str(name))}, ``BType_Imm Bit{width}``)"
            )
        elif kind == "mem":
            cell_width = int(variable.get("cell_width", variable.get("value_width", 8)))
            terms.append(
                f"bir_envSyntax.mk_BVar_string ({_quote_sml(str(name))}, ``BType_Mem Bit{width} Bit{cell_width}``)"
            )
    if not terms:
        return base_vars
    return "[" + ", ".join(terms) + f"] @ {base_vars}"


def _case_model_metadata(case: CaseConfig) -> dict[str, Any]:
    functions = case.raw.get("functions", {})
    if not isinstance(functions, dict):
        functions = {}
    extra_variables = case.execution.get("extra_variables", [])
    if not isinstance(extra_variables, list):
        extra_variables = []
    return {
        "name": case.name,
        "theory": case.theory,
        "arch": case.arch,
        "channel": case.channel,
        "symbols": case.symbols,
        "functions": functions,
        "extra_variables": extra_variables,
    }


def _initial_model_provenance(case: CaseConfig, sapic_output: Path) -> dict[str, Any]:
    return {
        "input_da": str(case.input_da) if case.input_da is not None else None,
        "input_da_sha256": sha256_file(case.input_da) if case.input_da is not None and case.input_da.exists() else None,
        "sapic": str(sapic_output),
        "sapic_sha256": None,
    }


def _model_proof_status(case: CaseConfig) -> dict[str, str]:
    proof_status = dict(case.proof_status)
    proof_status.setdefault("binary_model", "generated_unchecked")
    return proof_status


def _fragment_specs_sml(case: CaseConfig) -> str:
    entries: list[str] = []
    for index, fragment in enumerate(case.fragments):
        name = str(fragment.get("name") or f"fragment_{index}")
        entry = int(fragment["entry_label"])
        exits = [int(value) for value in fragment.get("exit_labels", [])]
        stop_terms = ", ".join(_label_term(value, case.arch) for value in exits)
        exit_texts = ", ".join(_quote_sml(str(value)) for value in exits)
        end_label = fragment.get("end_label")
        end_term = f"SOME (IntInf.fromInt {int(end_label)})" if end_label is not None else "NONE"
        entries.append(
            "  {"
            + ", ".join(
                [
                    f"name = {_quote_sml(name)}",
                    f"entry_label_text = {_quote_sml(str(entry))}",
                    f"exit_label_texts = [{exit_texts}]",
                    f"lbl_tm = {_label_term(entry, case.arch)}",
                    f"stop_lbl_tms = [{stop_terms}]",
                    f"start_label = IntInf.fromInt {entry}",
                    f"end_label = {end_term}",
                ]
            )
            + "}"
        )
    return "[\n" + ",\n".join(entries) + "\n]"


def generate_symexec_runner(
    case: CaseConfig,
    layout: BuildLayout,
    *,
    holmake: Path = DEFAULT_HOLMAKE,
    holba: Path = DEFAULT_HOLBA_DIR,
) -> dict[str, Path]:
    ensure_layout(layout)
    hol_source_root = stage_hol_sources(layout, holmake=holmake, holba=holba)
    theory = _safe_identifier(case.theory)
    runner_theory = f"CryptoBAP2Symexec_{_safe_identifier(case.name)}"
    runner_name = f"{runner_theory}Script.sml"
    runner = layout.work / runner_name
    holmakefile = layout.work / "Holmakefile"
    holmakefile_snapshot = layout.work / "Holmakefile.symexec"
    fragment_specs = _fragment_specs_sml(case)
    sapic_output = layout.sapic / f"{case.name}.sapic"
    model_output = binary_model_path(case, layout)
    pipeline_yaml = _write_symexec_pipeline_yaml(case, layout, sapic_output)
    case_metadata_json = _json_literal_for_sml(_case_model_metadata(case))
    provenance_json = _json_literal_for_sml(_initial_model_provenance(case, sapic_output))
    proof_status_json = _json_literal_for_sml(_model_proof_status(case))
    content = f"""open HolKernel Parse

open {theory}Theory;
open yamlLib;
open pipelineConfigLib;
open bir_envSyntax;
open bir_symbexec_stateLib;
open bir_symbexec_coreLib;
open bir_symbexec_compLib;
open bir_symbexec_stepLib;
open bir_symbexec_sumLib;
open bir_block_collectionLib;
open bir_programSyntax;
open bir_valuesSyntax;
open bir_immSyntax;
open bir_expSyntax;
open bir_exp_immSyntax;
open bir_exec_typingLib;
open bir_inst_liftingHelpersLib;
open HolBACoreSimps;
open HolBASimps;
open bslSyntax;
open bir_smtLib;
open bir_exp_to_wordsLib;
open Z3_SAT_modelLib;
open bir_exp_substitutionsSyntax;
open binariesLib;
open bir_auxiliaryLib;
open bir_constpropLib;
val _ = pipelineConfigLib.load_config {_quote_sml(pipeline_yaml.resolve())};
open commonBalrobScriptLib;
open bir_cfgLib;
open Redblackmap;
open bir_symbexec_oracleLib;
open sbir_treeLib;
open sapicplusTheory;
open sapicplusSyntax;
open translate_to_sapicTheory;
open rich_listTheory;
open translate_to_sapicLib;
open messagesTheory;
open messagesSyntax;
open tree_to_processLib;
open sapic_to_fileLib;
open CryptoBAP2Pipeline;

val _ = new_theory {_quote_sml(runner_theory)};

val (_, _, _, prog_tm) =
  (dest_bir_is_lifted_prog o concl) (DB.fetch {_quote_sml(theory)} {_quote_sml(theory + "_thm")});
val bl_dict_ = gen_block_dict prog_tm;
val prog_lbl_tms_ = get_block_dict_keys bl_dict_;
val _ = binariesLib.set_prog_lbl_tms prog_lbl_tms_;
val prog_vars_base = gen_vars_of_prog prog_tm;
val prog_vars = {_extra_var_terms(case, "prog_vars_base")};
val n_dict = bir_cfgLib.cfg_build_node_dict bl_dict_ prog_lbl_tms_;
val adr_dict = bir_symbexec_PreprocessLib.fun_addresses_dict bl_dict_ prog_lbl_tms_;

val binary_model_schema = {_quote_sml(BINARY_MODEL_SCHEMA)};
val case_metadata_json = {case_metadata_json};
val provenance_json = {provenance_json};
val proof_status_json = {proof_status_json};

fun term_name tm =
  (fst (bir_envSyntax.dest_BVar_string tm)) handle _ => term_to_string tm;

fun state_status_json syst =
  json_string (term_to_string (SYST_get_status syst));

fun path_predicates_json preds =
  json_list (List.map (fn pred => json_string (term_name pred)) preds);

fun symbolic_value_json (bv, symbv) =
  json_object [
    ("name", json_string (term_name bv)),
    ("term", json_string (term_to_string bv)),
    ("value", json_string (symbv_to_string symbv))
  ];

type fragment_spec = {{
  name : string,
  entry_label_text : string,
  exit_label_texts : string list,
  lbl_tm : term,
  stop_lbl_tms : term list,
  start_label : IntInf.int,
  end_label : IntInf.int option
}};

val fragment_specs : fragment_spec list = {fragment_specs};

val _ = set_stub_unclassified_calls (pipelineConfigLib.get_stub_unclassified_calls ());
val _ = set_allow_unmapped_memory_overapprox (pipelineConfigLib.get_allow_unmapped_memory_overapprox ());

fun configure_fragment_range (spec : fragment_spec) =
  case #end_label spec of
      SOME stop_label => set_active_fragment_range (#start_label spec, stop_label)
    | NONE => clear_active_fragment_range ();

fun run_fragment (spec : fragment_spec) =
  let
    val _ = configure_fragment_range spec;
    val lbl_tm = #lbl_tm spec;
    val stop_lbl_tms = #stop_lbl_tms spec;
    val syst = init_state lbl_tm prog_vars;
    val syst = state_add_preds "init_pred" [``bir_exp_true``] syst;
    val systs = symb_exec_to_stop (abpfun false) n_dict bl_dict_ [syst] stop_lbl_tms adr_dict [];
    val (systs_noassertfailed, _) =
      List.partition (fn syst => not (identical (SYST_get_status syst) BST_AssertionViolated_tm)) systs;
    val predlists = List.map (fn syst => ((rev o SYST_get_pred) syst)) systs_noassertfailed;
    val predlists_refined = List.map (fn lst => bir_symbexec_sortLib.removeDuplicates lst) predlists;
    val tree = predlist_to_tree predlists_refined;
    val vals_list = bir_symbexec_treeLib.symb_execs_vals_term systs_noassertfailed [];
    val sort_vals = bir_symbexec_sortLib.refine_symb_val_list vals_list;
    val valtr = tree_with_value tree sort_vals;
    val sapic_process = sbir_tree_sapic_process sort_vals (purge_tree valtr);
    val refined_process = refine_process sapic_process;
    val sapic_text = process_to_string refined_process;
    val model_json =
      json_object [
        ("name", json_string (#name spec)),
        ("entry_label", #entry_label_text spec),
        ("exit_labels", json_list (#exit_label_texts spec)),
        ("total_states", json_int (List.length systs)),
        ("assertion_clean_states", json_int (List.length systs_noassertfailed)),
        ("final_statuses", json_list (List.map state_status_json systs)),
        ("path_predicates", json_list (List.map path_predicates_json predlists_refined)),
        ("symbolic_values", json_list (List.map symbolic_value_json sort_vals)),
        ("sapic", json_string sapic_text)
      ];
  in
    (#name spec, sapic_text, model_json)
  end;

fun append_text (path, content) =
  let
    val out_stream = TextIO.openAppend path;
  in
    (TextIO.output (out_stream, content); TextIO.closeOut out_stream)
  end;

fun is_empty_sapic_process text =
  text = "0";

val model_prefix =
  "{{" ^ String.concatWith "," [
    json_field ("schema", json_string binary_model_schema),
    json_field ("case", case_metadata_json),
    json_field ("provenance", provenance_json),
    json_field ("proof_status", proof_status_json)
  ] ^ "," ^ json_string "fragments" ^ ":[";

fun write_fragment_outputs [] _ _ = ()
  | write_fragment_outputs (spec :: rest) sapic_first model_first =
      let
        val (_, sapic_text, model_json) = run_fragment spec;
        val emit_sapic = not (is_empty_sapic_process sapic_text);
        val sapic_prefix = if sapic_first then "" else "\\n\\n";
        val model_prefix = if model_first then "" else ",";
        val next_sapic_first = if emit_sapic then false else sapic_first;
      in
        if emit_sapic then
          append_text ({_quote_sml(sapic_output.resolve())}, sapic_prefix ^ sapic_text)
        else
          ();
        append_text ({_quote_sml(model_output.resolve())}, model_prefix ^ model_json);
        write_fragment_outputs rest next_sapic_first false
      end;

val _ = write_sapic_text ({_quote_sml(sapic_output.resolve())}, "");
val _ = write_binary_model_text ({_quote_sml(model_output.resolve())}, model_prefix);
val _ = write_fragment_outputs fragment_specs true true;
val _ = append_text ({_quote_sml(model_output.resolve())}, "]}}\\n");
val _ = export_theory();
"""
    holmake_text = _holmakefile_content(layout, hol_source_root)
    holmakefile.write_text(holmake_text, encoding="utf-8")
    holmakefile_snapshot.write_text(holmake_text, encoding="utf-8")
    runner.write_text(content, encoding="utf-8")
    return {
        "runner": runner,
        "holmakefile": holmakefile_snapshot,
        "sapic": sapic_output,
        "model": model_output,
        "pipeline_yaml": pipeline_yaml,
        "runner_theory": layout.work / ".hol" / "objs" / f"{runner_theory}Theory.uo",
        "hol_source_root": hol_source_root,
    }


def write_lift_descriptor(case: CaseConfig, layout: BuildLayout) -> Path:
    return run_lift_stage(case, layout, execute=False)["request"]


def write_symexec_descriptor(case: CaseConfig, layout: BuildLayout) -> Path:
    return run_symexec_stage(case, layout, execute=False)["request"]


def _format_sapic_artifact(path: Path) -> None:
    if not path.exists():
        return
    text = path.read_text(encoding="utf-8")
    formatted = format_sapic_text(text)
    if formatted != text:
        path.write_text(formatted, encoding="utf-8")


def run_symexec_stage(
    case: CaseConfig,
    layout: BuildLayout,
    *,
    execute: bool = True,
    allow_fixture_fallback: bool = False,
    holmake: Path = DEFAULT_HOLMAKE,
    holba: Path = DEFAULT_HOLBA_DIR,
) -> dict[str, Any]:
    artifacts = generate_symexec_runner(case, layout, holmake=holmake, holba=holba)
    request = {
        "stage": "symexec",
        "status": "configured",
        "fragments": case.fragments,
        "extra_variables": case.execution.get("extra_variables", []),
        "runner": str(artifacts["runner"]),
        "hol_source_root": str(artifacts["hol_source_root"]),
        "pipeline_yaml": str(artifacts["pipeline_yaml"]),
        "model_output": str(artifacts["model"]),
        "case_config_sha256": case_config_sha256(case),
    }
    request_path = layout.tree / "symexec-request.json"
    _write_json(request_path, request)
    stage_data = dict(request)
    stage_data["runner_sha256"] = sha256_file(artifacts["runner"])
    stage_data["holmakefile_sha256"] = sha256_file(artifacts["holmakefile"])
    stage_data["pipeline_yaml_sha256"] = sha256_file(artifacts["pipeline_yaml"])
    stage_data["label_diagnostics"] = validate_fragment_labels(case, layout)
    artifact_map = {
        "symexec_request": request_path,
        "symexec_runner": artifacts["runner"],
        "symexec_holmakefile": artifacts["holmakefile"],
        "symexec_pipeline_yaml": artifacts["pipeline_yaml"],
    }

    if execute:
        log_path = layout.logs / "symexec-holmake.log"
        target = artifacts["runner_theory"].name
        result = _run_holmake(layout, target, log_path, holmake=holmake, holba=holba)
        stage_data["status"] = "generated_unchecked" if result.returncode == 0 else "validation_failed"
        stage_data["exit_code"] = result.returncode
        stage_data["log"] = str(log_path)
        artifact_map["symexec_log"] = log_path
        artifact_map["symexec_theory_uo"] = artifacts["runner_theory"]
        if result.returncode != 0:
            sapic_source = case.artifacts.get("sapic_source")
            if allow_fixture_fallback and sapic_source and sapic_source.exists():
                shutil.copyfile(sapic_source, artifacts["sapic"])
                stage_data["status"] = "backend_partial"
                stage_data["fallback_sapic_source"] = str(sapic_source)
                stage_data.setdefault("diagnostics", []).append(
                    {
                        "severity": "warning",
                        "code": "migration_sapic_source",
                        "message": f"symexec runner failed; copied checked-in Sapic fixture {sapic_source}",
                    }
                )
                artifact_map["sapic"] = artifacts["sapic"]
            else:
                update_manifest(case, layout, command="symexec", stage="symexec", stage_data=stage_data, artifacts=artifact_map)
                hint = ""
                if sapic_source and sapic_source.exists():
                    hint = "; pass --allow-fixture-fallback to copy artifacts.sapic_source instead"
                raise StageError(f"HOL symbolic execution failed for {case.name}; see {log_path}{hint}")
        elif not artifacts["runner_theory"].exists():
            stage_data["status"] = "validation_failed"
            stage_data.setdefault("diagnostics", []).append(
                {
                    "severity": "error",
                    "code": "missing_hol_artifact",
                    "message": f"HOL symbolic execution completed but did not produce {artifacts['runner_theory']}",
                }
            )
            update_manifest(case, layout, command="symexec", stage="symexec", stage_data=stage_data, artifacts=artifact_map)
            raise StageError(
                f"HOL symbolic execution did not produce expected theory object for {case.name}: "
                f"{artifacts['runner_theory']}"
            )
        elif artifacts["sapic"].exists():
            _format_sapic_artifact(artifacts["sapic"])
            artifact_map["sapic"] = artifacts["sapic"]
        if result.returncode == 0:
            model_diagnostics, model_metadata = finalize_binary_model(
                case,
                layout,
                model_path=artifacts["model"],
                sapic_path=artifacts["sapic"],
            )
            stage_data.update(model_metadata)
            if model_diagnostics:
                stage_data.setdefault("diagnostics", []).extend(model_diagnostics)
            if any(item.get("severity") == "error" for item in model_diagnostics):
                stage_data["status"] = "validation_failed"
            artifact_map["binary_model"] = artifacts["model"]
            coverage = sapic_translation_coverage(case, layout, artifacts["sapic"])
            stage_data["translation_coverage"] = coverage
            coverage_diagnostics = coverage.get("diagnostics", [])
            if coverage_diagnostics:
                stage_data.setdefault("diagnostics", []).extend(coverage_diagnostics)
            if any(item.get("severity") == "error" for item in coverage_diagnostics):
                stage_data["status"] = "validation_failed"

    artifact_map.update(write_source_segment_files(case, layout, folders=("tree", "model", "sapic")))
    update_manifest(case, layout, command="symexec", stage="symexec", stage_data=stage_data, artifacts=artifact_map)
    return {"request": request_path, **artifacts, "stage": stage_data}
