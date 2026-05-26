from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
from dataclasses import dataclass
from string import Template
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
from .yaml_emit import yaml_named_list, yaml_scalar

SML_TEMPLATE_DIR = Path(__file__).with_name("sml_templates")


class StageError(RuntimeError):
    pass


@dataclass(frozen=True)
class LiftArtifacts:
    runner: Path
    holmakefile: Path
    label_dump: Path
    hol_source_root: Path | None = None

    def as_dict(self) -> dict[str, Path | None]:
        return {
            "runner": self.runner,
            "holmakefile": self.holmakefile,
            "label_dump": self.label_dump,
            "hol_source_root": self.hol_source_root,
        }


@dataclass(frozen=True)
class SymexecArtifacts:
    runner: Path
    holmakefile: Path
    sapic: Path
    model: Path
    run_sapic: Path
    run_model: Path
    pipeline_yaml: Path
    runner_theory: Path
    hol_source_root: Path

    def as_dict(self) -> dict[str, Path]:
        return {
            "runner": self.runner,
            "holmakefile": self.holmakefile,
            "sapic": self.sapic,
            "model": self.model,
            "run_sapic": self.run_sapic,
            "run_model": self.run_model,
            "pipeline_yaml": self.pipeline_yaml,
            "runner_theory": self.runner_theory,
            "hol_source_root": self.hol_source_root,
        }


SML_TEMPLATE_FIELDS = {
    "lift_runner.sml": {
        "theory",
        "arch",
        "dafilename",
        "symbol_lines",
        "section_lines",
        "lift_all_symbols",
        "lifter",
        "theorem_name",
        "label_dump",
    },
    "symexec_runner.sml": {
        "theory",
        "pipeline_yaml",
        "runner_theory",
        "theory_db",
        "theorem_name",
        "prog_vars",
        "binary_model_schema",
        "case_metadata_json",
        "provenance_json",
        "proof_status_json",
        "fragment_specs",
        "sapic_output",
        "model_output",
    },
}


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


def _render_sml_template(name: str, **values: object) -> str:
    template_path = SML_TEMPLATE_DIR / name
    template_text = template_path.read_text(encoding="utf-8")
    template = Template(template_text)
    if not template.is_valid():
        raise StageError(f"SML template has invalid Template syntax: {template_path}")

    expected = SML_TEMPLATE_FIELDS.get(name)
    placeholders = set(template.get_identifiers())
    if expected is None:
        raise StageError(f"SML template has no placeholder contract: {template_path}")
    if placeholders != expected:
        missing = sorted(expected - placeholders)
        extra = sorted(placeholders - expected)
        details = []
        if missing:
            details.append("missing " + ", ".join(missing))
        if extra:
            details.append("unexpected " + ", ".join(extra))
        raise StageError(f"SML template placeholders do not match contract for {name}: {'; '.join(details)}")

    supplied = set(values)
    if supplied != expected:
        missing = sorted(expected - supplied)
        extra = sorted(supplied - expected)
        details = []
        if missing:
            details.append("missing " + ", ".join(missing))
        if extra:
            details.append("unexpected " + ", ".join(extra))
        raise StageError(f"SML template render arguments do not match contract for {name}: {'; '.join(details)}")

    return template.substitute({key: str(value) for key, value in values.items()})


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
    label_metadata = layout.bir / "lifted-labels.json"
    if not theory_obj.exists():
        return False
    if not label_metadata.exists():
        return False
    manifest = load_manifest(layout.manifest_path)
    stage = manifest.get("stages", {}).get("lift") if manifest else None
    if not isinstance(stage, dict) or stage.get("status") != "generated_unchecked":
        return False
    for key, expected in _lift_fingerprint(case, holmake=holmake, holba=holba).items():
        if stage.get(key) != expected:
            return False
    return (
        _artifact_hash_matches(manifest, "lifted_theory_uo", theory_obj)
        and _artifact_hash_matches(manifest, "lifted_label_metadata", label_metadata)
    )


_DA_FUNCTION_HEADER_RE = re.compile(r"^([0-9A-Fa-f]+)\s+<([^>]+)>:")


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
                        f"    - name: {yaml_scalar(variable.get('name', ''))}",
                        f"      type: {yaml_scalar(variable.get('type', 'Imm'))}",
                        f"      width: {int(variable.get('width', 64))}",
                    ]
                )
    extra_block = ["  extra_variables:", *extra_lines] if extra_lines else ["  extra_variables: []"]
    crypto_lines = [
        f"  {yaml_scalar(name)}: {yaml_scalar(label)}"
        for name, label in sorted((str(k), str(v)) for k, v in crypto.items())
    ]
    crypto_block = ["cryptographic_functions:", *crypto_lines] if crypto_lines else ["cryptographic_functions: {}"]
    callsite_crypto_lines = [
        f"  {yaml_scalar(int(label))}: {yaml_scalar(crypto_label)}"
        for label, crypto_label in sorted((int(k), str(v)) for k, v in callsite_crypto.items())
    ]
    callsite_crypto_block = (
        ["cryptographic_callsite_labels:", *callsite_crypto_lines]
        if callsite_crypto_lines
        else ["cryptographic_callsite_labels: {}"]
    )
    fragment_lines: list[str] = []
    for item in case.fragments:
        if not isinstance(item, dict):
            continue
        fragment_lines.extend(
            [
                f"    - name: {yaml_scalar(item.get('name', 'fragment'))}",
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
            f"  theory: {yaml_scalar(_safe_identifier(case.theory))}",
            f"  channel: {yaml_scalar(case.channel)}",
            *extra_block,
            f"  stub_unclassified_calls: {_sml_bool(_stub_unclassified_calls(case))}",
            f"  allow_unmapped_memory_overapprox: {_sml_bool(_allow_unmapped_memory_overapprox(case))}",
            f"  output_file: {yaml_scalar(sapic_output.resolve())}",
            "  fragments:",
            *fragment_lines,
            "functions:",
            *yaml_named_list(2, "library", library),
            *yaml_named_list(2, "adversary", adversary),
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


def generate_lift_runner(case: CaseConfig, layout: BuildLayout) -> LiftArtifacts:
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
    content = _render_sml_template(
        "lift_runner.sml",
        theory=_quote_sml(theory),
        arch=_quote_sml(case.arch),
        dafilename=_quote_sml(case.input_da.resolve()),
        symbol_lines=symbol_lines,
        section_lines=section_lines,
        lift_all_symbols=_sml_bool(_case_uses_wildcard_symbols(case)),
        lifter=lifter,
        theorem_name=_quote_sml(theory + "_thm"),
        label_dump=_quote_sml(label_dump.resolve()),
    )
    holmake_text = _holmakefile_content(layout)
    holmakefile.write_text(holmake_text, encoding="utf-8")
    holmakefile_snapshot.write_text(holmake_text, encoding="utf-8")
    script.write_text(content, encoding="utf-8")
    return LiftArtifacts(runner=script, holmakefile=holmakefile_snapshot, label_dump=label_dump)


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


def _remove_stale_artifact(path: Path | None) -> None:
    if path is not None and path.exists():
        path.unlink()


def _symexec_attempt_artifacts(case: CaseConfig, layout: BuildLayout) -> tuple[Path, Path]:
    stem = _safe_identifier(case.name)
    return (
        layout.work / f".{stem}.sapic.attempt",
        layout.work / f".{stem}.binary-model.json.attempt",
    )


def _replace_artifact(source: Path, target: Path) -> bool:
    if not source.exists():
        return False
    target.parent.mkdir(parents=True, exist_ok=True)
    os.replace(source, target)
    return True


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
    request = {
        "stage": "lift",
        "status": "configured",
        **_lift_fingerprint(case, holmake=holmake, holba=holba),
        "runner": str(artifacts.runner),
        "hol_source_root": str(artifacts.hol_source_root) if artifacts.hol_source_root is not None else None,
        "case_config_sha256": case_config_sha256(case),
    }
    request_path = layout.bir / "lift-request.json"
    _write_json(request_path, request)
    stage_data = dict(request)
    stage_data["runner_sha256"] = sha256_file(artifacts.runner)
    stage_data["holmakefile_sha256"] = sha256_file(artifacts.holmakefile)
    stage_data["holmake"] = str(holmake)
    stage_data["holba"] = str(holba)
    artifact_map = {
        "lift_request": request_path,
        "lift_runner": artifacts.runner,
        "lift_holmakefile": artifacts.holmakefile,
        "lifted_label_dump": artifacts.label_dump,
    }
    if execute:
        log_path = layout.logs / "lift-holmake.log"
        theory_obj = layout.work / ".hol" / "objs" / f"{theory}Theory.uo"
        _remove_stale_artifact(artifacts.label_dump)
        _remove_stale_artifact(theory_obj)
        result = _run_holmake(layout, f"{theory}Theory.uo", log_path, holmake=holmake, holba=holba)
        stage_data["status"] = "generated_unchecked" if result.returncode == 0 else "validation_failed"
        stage_data["exit_code"] = result.returncode
        stage_data["log"] = str(log_path)
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
        if not artifacts.label_dump.exists():
            stage_data["status"] = "validation_failed"
            stage_data.setdefault("diagnostics", []).append(
                {
                    "severity": "error",
                    "code": "missing_label_dump",
                    "message": f"HOL lift completed but did not produce {artifacts.label_dump}",
                }
            )
            update_manifest(case, layout, command="lift", stage="lift", stage_data=stage_data, artifacts=artifact_map)
            raise StageError(f"HOL lift did not produce expected label dump for {case.name}: {artifacts.label_dump}")
        labels = sorted(parse_lifted_labels(artifacts.label_dump.read_text(encoding="utf-8", errors="replace")))
        label_metadata = {
            "source": str(artifacts.label_dump),
            "source_sha256": sha256_file(artifacts.label_dump),
            "labels": labels,
        }
        label_metadata_path = layout.bir / "lifted-labels.json"
        _write_json(label_metadata_path, label_metadata)
        stage_data["label_count"] = len(labels)
        artifact_map["lifted_label_metadata"] = label_metadata_path

    artifact_map.update(write_source_segment_files(case, layout, folders=("bir",)))
    update_manifest(case, layout, command="lift", stage="lift", stage_data=stage_data, artifacts=artifact_map)
    return {"request": request_path, **artifacts.as_dict(), "stage": stage_data}


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
    sapic_output: Path | None = None,
    model_output: Path | None = None,
) -> SymexecArtifacts:
    ensure_layout(layout)
    hol_source_root = stage_hol_sources(layout, holmake=holmake, holba=holba)
    theory = _safe_identifier(case.theory)
    runner_theory = f"CryptoBAP2Symexec_{_safe_identifier(case.name)}"
    runner_name = f"{runner_theory}Script.sml"
    runner = layout.work / runner_name
    holmakefile = layout.work / "Holmakefile"
    holmakefile_snapshot = layout.work / "Holmakefile.symexec"
    fragment_specs = _fragment_specs_sml(case)
    final_sapic_output = layout.sapic / f"{case.name}.sapic"
    final_model_output = binary_model_path(case, layout)
    run_sapic_output = sapic_output or final_sapic_output
    run_model_output = model_output or final_model_output
    pipeline_yaml = _write_symexec_pipeline_yaml(case, layout, run_sapic_output)
    case_metadata_json = _json_literal_for_sml(_case_model_metadata(case))
    provenance_json = _json_literal_for_sml(_initial_model_provenance(case, run_sapic_output))
    proof_status_json = _json_literal_for_sml(_model_proof_status(case))
    content = _render_sml_template(
        "symexec_runner.sml",
        theory=theory,
        pipeline_yaml=_quote_sml(pipeline_yaml.resolve()),
        runner_theory=_quote_sml(runner_theory),
        theory_db=_quote_sml(theory),
        theorem_name=_quote_sml(theory + "_thm"),
        prog_vars=_extra_var_terms(case, "prog_vars_base"),
        binary_model_schema=_quote_sml(BINARY_MODEL_SCHEMA),
        case_metadata_json=case_metadata_json,
        provenance_json=provenance_json,
        proof_status_json=proof_status_json,
        fragment_specs=fragment_specs,
        sapic_output=_quote_sml(run_sapic_output.resolve()),
        model_output=_quote_sml(run_model_output.resolve()),
    )
    holmake_text = _holmakefile_content(layout, hol_source_root)
    holmakefile.write_text(holmake_text, encoding="utf-8")
    holmakefile_snapshot.write_text(holmake_text, encoding="utf-8")
    runner.write_text(content, encoding="utf-8")
    return SymexecArtifacts(
        runner=runner,
        holmakefile=holmakefile_snapshot,
        sapic=final_sapic_output,
        model=final_model_output,
        run_sapic=run_sapic_output,
        run_model=run_model_output,
        pipeline_yaml=pipeline_yaml,
        runner_theory=layout.work / ".hol" / "objs" / f"{runner_theory}Theory.uo",
        hol_source_root=hol_source_root,
    )


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
    attempt_sapic: Path | None = None
    attempt_model: Path | None = None
    if execute:
        attempt_sapic, attempt_model = _symexec_attempt_artifacts(case, layout)
    artifacts = generate_symexec_runner(
        case,
        layout,
        holmake=holmake,
        holba=holba,
        sapic_output=attempt_sapic,
        model_output=attempt_model,
    )
    request = {
        "stage": "symexec",
        "status": "configured",
        "fragments": case.fragments,
        "extra_variables": case.execution.get("extra_variables", []),
        "runner": str(artifacts.runner),
        "hol_source_root": str(artifacts.hol_source_root),
        "pipeline_yaml": str(artifacts.pipeline_yaml),
        "sapic_output": str(artifacts.sapic),
        "run_sapic_output": str(artifacts.run_sapic),
        "model_output": str(artifacts.model),
        "run_model_output": str(artifacts.run_model),
        "case_config_sha256": case_config_sha256(case),
    }
    request_path = layout.tree / "symexec-request.json"
    _write_json(request_path, request)
    stage_data = dict(request)
    stage_data["runner_sha256"] = sha256_file(artifacts.runner)
    stage_data["holmakefile_sha256"] = sha256_file(artifacts.holmakefile)
    stage_data["pipeline_yaml_sha256"] = sha256_file(artifacts.pipeline_yaml)
    label_diagnostics = validate_fragment_labels(case, layout, require_metadata=execute)
    stage_data["label_diagnostics"] = label_diagnostics
    if label_diagnostics:
        stage_data.setdefault("diagnostics", []).extend(label_diagnostics)
    artifact_map = {
        "symexec_request": request_path,
        "symexec_runner": artifacts.runner,
        "symexec_holmakefile": artifacts.holmakefile,
        "symexec_pipeline_yaml": artifacts.pipeline_yaml,
    }

    if execute:
        if any(item.get("severity") == "error" for item in label_diagnostics):
            stage_data["status"] = "validation_failed"
            update_manifest(case, layout, command="symexec", stage="symexec", stage_data=stage_data, artifacts=artifact_map)
            raise StageError(f"symbolic execution labels failed validation for {case.name}; see {layout.manifest_path}")
        log_path = layout.logs / "symexec-holmake.log"
        target = artifacts.runner_theory.name
        _remove_stale_artifact(artifacts.runner_theory)
        _remove_stale_artifact(artifacts.run_sapic)
        _remove_stale_artifact(artifacts.run_model)
        result = _run_holmake(layout, target, log_path, holmake=holmake, holba=holba)
        stage_data["status"] = "generated_unchecked" if result.returncode == 0 else "validation_failed"
        stage_data["exit_code"] = result.returncode
        stage_data["log"] = str(log_path)
        artifact_map["symexec_log"] = log_path
        artifact_map["symexec_theory_uo"] = artifacts.runner_theory
        if result.returncode != 0:
            sapic_source = case.artifacts.get("sapic_source")
            if allow_fixture_fallback and sapic_source and sapic_source.exists():
                copied_fixture = False
                if artifacts.sapic.exists():
                    stage_data["fallback_preserved_existing_sapic"] = str(artifacts.sapic)
                    stage_data.setdefault("diagnostics", []).append(
                        {
                            "severity": "warning",
                            "code": "migration_sapic_source_preserved_existing",
                            "message": (
                                "symexec runner failed; kept existing generated Sapic artifact "
                                f"{artifacts.sapic} instead of overwriting it with {sapic_source}"
                            ),
                        }
                    )
                else:
                    shutil.copyfile(sapic_source, artifacts.sapic)
                    copied_fixture = True
                if artifacts.model.exists():
                    stage_data["fallback_preserved_existing_binary_model"] = str(artifacts.model)
                stage_data["status"] = "backend_partial"
                stage_data["fallback_sapic_source"] = str(sapic_source)
                fallback_message = (
                    f"symexec runner failed; copied checked-in Sapic fixture {sapic_source}"
                    if copied_fixture
                    else f"symexec runner failed; fixture Sapic source is available at {sapic_source}"
                )
                stage_data.setdefault("diagnostics", []).append(
                    {
                        "severity": "warning",
                        "code": "migration_sapic_source",
                        "message": fallback_message,
                    }
                )
                artifact_map["sapic"] = artifacts.sapic
                if artifacts.model.exists():
                    artifact_map["binary_model"] = artifacts.model
            else:
                update_manifest(case, layout, command="symexec", stage="symexec", stage_data=stage_data, artifacts=artifact_map)
                hint = ""
                if sapic_source and sapic_source.exists():
                    hint = "; pass --allow-fixture-fallback to copy artifacts.sapic_source instead"
                raise StageError(f"HOL symbolic execution failed for {case.name}; see {log_path}{hint}")
        elif not artifacts.runner_theory.exists():
            stage_data["status"] = "validation_failed"
            stage_data.setdefault("diagnostics", []).append(
                {
                    "severity": "error",
                    "code": "missing_hol_artifact",
                    "message": f"HOL symbolic execution completed but did not produce {artifacts.runner_theory}",
                }
            )
            update_manifest(case, layout, command="symexec", stage="symexec", stage_data=stage_data, artifacts=artifact_map)
            raise StageError(
                f"HOL symbolic execution did not produce expected theory object for {case.name}: "
                f"{artifacts.runner_theory}"
            )
        elif artifacts.run_sapic.exists():
            _format_sapic_artifact(artifacts.run_sapic)
        if result.returncode == 0:
            model_diagnostics, model_metadata = finalize_binary_model(
                case,
                layout,
                model_path=artifacts.run_model,
                sapic_path=artifacts.run_sapic,
            )
            stage_data.update(model_metadata)
            if model_diagnostics:
                stage_data.setdefault("diagnostics", []).extend(model_diagnostics)
            if any(item.get("severity") == "error" for item in model_diagnostics):
                stage_data["status"] = "validation_failed"
            coverage = sapic_translation_coverage(case, layout, artifacts.run_sapic)
            stage_data["translation_coverage"] = coverage
            coverage_diagnostics = coverage.get("diagnostics", [])
            if coverage_diagnostics:
                stage_data.setdefault("diagnostics", []).extend(coverage_diagnostics)
            if any(item.get("severity") == "error" for item in coverage_diagnostics):
                stage_data["status"] = "validation_failed"
            if _replace_artifact(artifacts.run_sapic, artifacts.sapic):
                artifact_map["sapic"] = artifacts.sapic
            if _replace_artifact(artifacts.run_model, artifacts.model):
                artifact_map["binary_model"] = artifacts.model

    artifact_map.update(write_source_segment_files(case, layout, folders=("tree", "model", "sapic")))
    update_manifest(case, layout, command="symexec", stage="symexec", stage_data=stage_data, artifacts=artifact_map)
    return {"request": request_path, **artifacts.as_dict(), "stage": stage_data}
