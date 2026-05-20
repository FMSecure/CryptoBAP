from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from . import __version__
from .autocase import ScaffoldError, default_case_name, scaffold_case_from_da
from .checks import Finding, check_case_config, check_failed, check_source_trust, run_checks
from .config import CaseConfig, CaseConfigError, load_case, load_yaml_subset, render_case_template, resolve_case
from .disassembly import (
    DEFAULT_GHIDRA_SHA256,
    DEFAULT_GHIDRA_VERSION,
    DisassemblyError,
    ghidra_status,
    install_ghidra,
    java_status,
    prepare_case_disassembly,
    resolve_ghidra_headless,
    run_ghidra_disassembly,
)
from .inference import (
    case_needs_inference,
    default_theory_name,
    inferred_case_raw,
    merge_missing_inferred_fields,
    render_case_yaml,
    sanitize_case_name,
)
from .manifest import BuildLayout, DEFAULT_BUILD_ROOT, case_config_sha256, ensure_layout, layout_for_case, update_manifest
from .paths import (
    DEFAULT_CASE_DIR,
    DEFAULT_GHIDRA_HEADLESS,
    DEFAULT_HOLBA_DIR,
    DEFAULT_HOLMAKE,
    DEFAULT_SQUIRREL,
    DEFAULT_TAMARIN,
    executable_status,
)
from .squirrel_backend import BackendError, export_squirrel, stage_spthy
from .stages import StageError, lift_stage_is_current, run_lift_stage, run_symexec_stage


def _print_findings(findings: list[Finding]) -> None:
    if not findings:
        print("ok: no diagnostics")
        return
    for finding in findings:
        location = ""
        if finding.path:
            location = finding.path
            if finding.line is not None:
                location += f":{finding.line}"
            location += ": "
        print(f"{finding.severity}: {location}{finding.code}: {finding.message}")


def _tool_paths(args: argparse.Namespace) -> dict[str, object]:
    ghidra = resolve_ghidra_headless(getattr(args, "ghidra", None)) or getattr(args, "ghidra", None) or DEFAULT_GHIDRA_HEADLESS
    return {
        "holba": str(getattr(args, "holba", DEFAULT_HOLBA_DIR)),
        "holmake": str(getattr(args, "holmake", DEFAULT_HOLMAKE)),
        "tamarin": str(getattr(args, "tamarin", DEFAULT_TAMARIN) or DEFAULT_TAMARIN),
        "squirrel": str(getattr(args, "squirrel", DEFAULT_SQUIRREL)),
        "ghidra": str(ghidra) if ghidra else None,
    }


def _load_layout(case_arg: str, build_root: Path, *, create: bool = True) -> tuple[object, object]:
    case = load_case(case_arg)
    layout = layout_for_case(case, build_root)
    if create:
        ensure_layout(layout)
    return case, layout


_CASE_SUFFIXES = {".yaml", ".yml"}


def _is_direct_input(value: str) -> bool:
    path = Path(value).expanduser()
    return path.exists() and path.suffix.lower() not in _CASE_SUFFIXES


def _raw_input_block(raw: dict[str, object]) -> dict[str, object]:
    input_block = raw.setdefault("input", {})
    if not isinstance(input_block, dict):
        input_block = {}
        raw["input"] = input_block
    return input_block


def _raw_sections(raw: dict[str, object], args: argparse.Namespace) -> list[str]:
    cli_sections = _split_sections(getattr(args, "sections", None))
    if getattr(args, "sections", None):
        return cli_sections
    input_block = raw.get("input", {})
    disassembly = input_block.get("disassembly", {}) if isinstance(input_block, dict) else {}
    if isinstance(disassembly, dict):
        sections = disassembly.get("sections", [".text"])
        if isinstance(sections, list) and sections:
            return [str(section) for section in sections]
    return [".text"]


def _raw_symbols(raw: dict[str, object], args: argparse.Namespace) -> list[str] | None:
    cli_symbols = _split_symbols(getattr(args, "symbols", None))
    if cli_symbols:
        return cli_symbols
    input_block = raw.get("input", {})
    symbols = input_block.get("symbols", []) if isinstance(input_block, dict) else []
    if isinstance(symbols, list) and symbols:
        return [str(symbol) for symbol in symbols]
    return None


def _seed_case_defaults(
    raw: dict[str, object],
    *,
    source_path: Path,
    args: argparse.Namespace,
) -> dict[str, object]:
    input_block = _raw_input_block(raw)
    binary_value = input_block.get("binary")
    da_value = input_block.get("da")
    if getattr(args, "name", None):
        case_name = sanitize_case_name(str(args.name))
    elif isinstance(raw.get("name"), str) and raw["name"]:
        case_name = str(raw["name"])
    elif binary_value:
        case_name = default_case_name(Path(str(binary_value)))
    elif da_value:
        case_name = default_case_name(Path(str(da_value)))
    else:
        case_name = default_case_name(source_path)
    raw["name"] = case_name
    raw.setdefault("description", f"Draft case inferred from {source_path.name}.")
    raw.setdefault("arch", getattr(args, "arch", None) or "arm8")
    raw.setdefault("channel", "Channel")
    input_block.setdefault("theory", getattr(args, "theory", None) or default_theory_name(case_name))
    disassembly = input_block.setdefault("disassembly", {})
    if not isinstance(disassembly, dict):
        disassembly = {}
        input_block["disassembly"] = disassembly
    disassembly.setdefault("tool", "ghidra")
    disassembly.setdefault("sections", _raw_sections(raw, args))
    cli_symbols = _split_symbols(getattr(args, "symbols", None))
    if cli_symbols and not input_block.get("symbols"):
        input_block["symbols"] = cli_symbols
    raw.setdefault("backends", ["squirrel"])
    raw.setdefault(
        "proof_status",
        {
            "hol": "generated_unchecked",
            "sapic": "generated_unchecked",
            "squirrel": "generated_unchecked",
        },
    )
    raw.setdefault("security_lemmas", [])
    return raw


def _write_inferred_case_files(case: CaseConfig, layout: BuildLayout, args: argparse.Namespace) -> Path:
    ensure_layout(layout)
    inferred_path = layout.work / "inferred-case.yaml"
    inferred_path.write_text(render_case_yaml(case.raw), encoding="utf-8")
    write_case = getattr(args, "write_case", None)
    if write_case:
        output = Path(write_case).expanduser()
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(render_case_yaml(case.raw), encoding="utf-8")
    inference = case.raw.get("inference", {})
    inference_data = inference if isinstance(inference, dict) else {}
    update_manifest(
        case,
        layout,
        command="infer-case",
        stage="inference",
        stage_data={"status": "generated_unchecked", **inference_data},
        artifacts={"inferred_case": inferred_path},
    )
    return inferred_path


def _complete_case_from_da(args: argparse.Namespace, case: CaseConfig, layout: BuildLayout) -> CaseConfig:
    if not case_needs_inference(case.raw):
        return case
    if case.input_da is None or not case.input_da.exists():
        raise CaseConfigError("case needs inference but has no available input.da")
    raw, _inference = inferred_case_raw(
        da_path=case.input_da,
        arch=case.arch,
        name=case.name,
        theory=case.theory,
        binary_path=case.input_binary,
        sections=_raw_sections(case.raw, args),
        symbols=_raw_symbols(case.raw, args),
        max_functions=int(getattr(args, "max_functions", 16)),
        infer_crypto=True,
        scope=str(getattr(args, "scope", "auto")),
    )
    merged = merge_missing_inferred_fields(case.raw, raw)
    completed = CaseConfig(path=layout.work / "inferred-case.yaml", raw=merged)
    inferred_path = _write_inferred_case_files(completed, layout, args)
    return CaseConfig(path=inferred_path, raw=merged)


def _load_case_allow_incomplete(case_arg: str, args: argparse.Namespace) -> CaseConfig:
    path = resolve_case(case_arg)
    raw = load_yaml_subset(path)
    seeded = _seed_case_defaults(raw, source_path=path, args=args)
    return CaseConfig(path=path, raw=seeded)


def _load_direct_input_case(args: argparse.Namespace) -> tuple[CaseConfig, BuildLayout]:
    input_path = Path(args.case).expanduser().resolve()
    if not input_path.exists():
        raise FileNotFoundError(f"input does not exist: {input_path}")
    is_da = input_path.suffix == ".da"
    raw: dict[str, object] = {
        "input": {"da" if is_da else "binary": str(input_path)},
    }
    raw = _seed_case_defaults(raw, source_path=input_path, args=args)
    case = CaseConfig(path=input_path, raw=raw)
    layout = layout_for_case(case, args.build_root)
    ensure_layout(layout)
    if not is_da:
        case = _prepare_case_for_lift(args, case, layout)
    return _complete_case_from_da(args, case, layout), layout


def _load_pipeline_case(args: argparse.Namespace, *, create: bool = True) -> tuple[CaseConfig, BuildLayout]:
    if _is_direct_input(args.case):
        return _load_direct_input_case(args)
    case = _load_case_allow_incomplete(args.case, args)
    layout = layout_for_case(case, args.build_root)
    if create:
        ensure_layout(layout)
    case = _prepare_case_for_lift(args, case, layout)
    case = _complete_case_from_da(args, case, layout)
    return case, layout


def cmd_init_case(args: argparse.Namespace) -> int:
    output = Path(args.output)
    if not output.suffix:
        output = DEFAULT_CASE_DIR / f"{output}.yaml"
    if output.exists() and not args.force:
        raise FileExistsError(f"{output} already exists; pass --force to overwrite")
    output.parent.mkdir(parents=True, exist_ok=True)
    text = render_case_template(args.name or output.stem, args.template)
    output.write_text(text, encoding="utf-8")
    print(output)
    return 0


def _split_symbols(value: str | None) -> list[str] | None:
    if not value:
        return None
    symbols = [part.strip() for part in value.split(",") if part.strip()]
    return symbols or None


def _case_output_path(value: str | None, name: str) -> Path:
    if value is None:
        return DEFAULT_CASE_DIR / f"{name}.yaml"
    output = Path(value)
    if not output.suffix:
        output = DEFAULT_CASE_DIR / f"{output}.yaml"
    return output


def cmd_scaffold_case(args: argparse.Namespace) -> int:
    input_path = Path(args.input).expanduser().resolve()
    if not input_path.exists():
        raise FileNotFoundError(f"input does not exist: {input_path}")
    sections = _split_sections(args.sections)
    is_da = args.from_da or input_path.suffix == ".da"
    draft_name = default_case_name(Path(args.name) if args.name else input_path)
    da_path = input_path
    binary_path: Path | None = None
    if not is_da:
        binary_path = input_path
        da_path = (args.da_output or (args.build_root / draft_name / "bir" / f"{draft_name}.da")).resolve()
        headless = resolve_ghidra_headless(args.ghidra)
        if headless is None and args.install_ghidra:
            headless = install_ghidra().headless
        if headless is None:
            raise DisassemblyError("Ghidra is unavailable; run 'cryptobap2 install-ghidra' or pass --ghidra")
        run_ghidra_disassembly(
            binary_path,
            da_path,
            arch=args.arch,
            ghidra=headless,
            sections=sections,
            log_path=args.build_root / draft_name / "logs" / "ghidra-disassemble.log",
        )

    scaffold = scaffold_case_from_da(
        da_path,
        arch=args.arch,
        name=args.name,
        theory=args.theory,
        binary_path=binary_path,
        sections=sections,
        symbols=_split_symbols(args.symbols),
        max_functions=args.max_functions,
        infer_crypto=not args.no_infer_crypto,
        scope=args.scope,
    )
    output = _case_output_path(args.output, scaffold.output_name)
    if output.exists() and not args.force:
        raise FileExistsError(f"{output} already exists; pass --force to overwrite")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(scaffold.text, encoding="utf-8")
    print(output)
    print(
        f"found {len(scaffold.discovered_functions)} functions; selected {len(scaffold.selected_functions)}",
        file=sys.stderr,
    )
    for warning in scaffold.warnings:
        print(f"warning: {warning}", file=sys.stderr)
    return 0


def cmd_list_cases(args: argparse.Namespace) -> int:
    for path in sorted(DEFAULT_CASE_DIR.glob("*.yaml")):
        print(path.stem)
    return 0


def _prepare_case_for_lift(args: argparse.Namespace, case, layout):
    if case.input_binary is None:
        return case
    return prepare_case_disassembly(
        case,
        layout,
        ghidra=getattr(args, "ghidra", None),
        install_missing=getattr(args, "install_ghidra", False),
    )


def cmd_lift(args: argparse.Namespace) -> int:
    case, layout = _load_pipeline_case(args)
    errors = case.validate()
    if errors:
        raise CaseConfigError("; ".join(errors))
    result = run_lift_stage(case, layout, holmake=args.holmake, holba=args.holba)
    update_manifest(case, layout, tool_paths=_tool_paths(args))
    print(result["runner"])
    return 0


def cmd_symexec(args: argparse.Namespace) -> int:
    case, layout = _load_pipeline_case(args)
    errors = case.validate()
    if errors:
        raise CaseConfigError("; ".join(errors))
    if not lift_stage_is_current(case, layout, holmake=args.holmake, holba=args.holba):
        run_lift_stage(case, layout, holmake=args.holmake, holba=args.holba)
    result = run_symexec_stage(
        case,
        layout,
        holmake=args.holmake,
        holba=args.holba,
        allow_fixture_fallback=args.allow_fixture_fallback,
    )
    update_manifest(case, layout, tool_paths=_tool_paths(args))
    print(result["runner"])
    return 0


def cmd_translate(args: argparse.Namespace) -> int:
    case, layout = _load_layout(args.case, args.build_root)
    result = stage_spthy(case, layout, tamarin=args.tamarin)
    print(result["spthy"])
    return 1 if _has_error_diagnostics(result.get("diagnostics", [])) else 0


def _has_error_diagnostics(diagnostics: list[dict[str, object]]) -> bool:
    return any(item.get("severity") == "error" for item in diagnostics)


def _export_tamarin_source(case, layout, *, tamarin: Path = DEFAULT_TAMARIN) -> tuple[Path, list[dict[str, object]]]:
    result = stage_spthy(case, layout, tamarin=tamarin)
    return result["spthy"], result["diagnostics"]


def cmd_export(args: argparse.Namespace) -> int:
    case, layout = _load_layout(args.case, args.build_root)
    failed = False
    if args.target in {"tamarin", "all"}:
        spthy, diagnostics = _export_tamarin_source(case, layout, tamarin=args.tamarin)
        print(spthy)
        failed = failed or _has_error_diagnostics(diagnostics)
    if args.target in {"squirrel", "all"}:
        result = export_squirrel(
            case,
            layout,
            tamarin=args.tamarin,
            squirrel=args.squirrel,
            readable=args.readable_squirrel,
        )
        print(result["squirrel"])
        if result.get("readable_squirrel") is not None:
            print(result["readable_squirrel"])
        failed = failed or _has_error_diagnostics(result.get("diagnostics", []))
    update_manifest(case, layout, tool_paths=_tool_paths(args))
    return 1 if failed else 0


def cmd_check(args: argparse.Namespace) -> int:
    case, layout = _load_layout(args.case, args.build_root, create=False)
    findings = run_checks(case, layout, strict=args.strict, record=args.record)
    if args.json:
        print(json.dumps([finding.as_dict() for finding in findings], indent=2, sort_keys=True))
    else:
        _print_findings(findings)
        print(layout.manifest_path)
    return 1 if check_failed(findings, strict=args.strict) else 0


def _target_backends(target: str) -> list[str]:
    if target == "all":
        return ["tamarin", "squirrel"]
    return [target]


def _target_requires_spthy_source(target: str) -> bool:
    return target in {"tamarin", "squirrel", "all"}


def _require_spthy_source_for_target(case: CaseConfig, target: str) -> None:
    if _target_requires_spthy_source(target) and "tamarin_source" not in case.artifacts:
        raise BackendError(
            f"{case.name} requires artifacts.tamarin_source for target {target}; "
            "CryptoBAP2 no longer generates SPTHY from Sapic"
        )


def cmd_run(args: argparse.Namespace) -> int:
    case, layout = _load_pipeline_case(args)
    errors = case.validate()
    if errors:
        raise CaseConfigError("; ".join(errors))
    _require_spthy_source_for_target(case, args.target)

    run_lift_stage(case, layout, holmake=args.holmake, holba=args.holba)
    run_symexec_stage(
        case,
        layout,
        holmake=args.holmake,
        holba=args.holba,
        allow_fixture_fallback=args.allow_fixture_fallback,
    )

    if args.target in {"tamarin", "all"}:
        _export_tamarin_source(case, layout, tamarin=args.tamarin)
    if args.target in {"squirrel", "all"}:
        export_squirrel(
            case,
            layout,
            tamarin=args.tamarin,
            squirrel=args.squirrel,
            readable=args.readable_squirrel,
        )

    update_manifest(case, layout, tool_paths=_tool_paths(args))
    findings = run_checks(case, layout, strict=args.strict, record=True, backends=_target_backends(args.target))
    _print_findings(findings)
    print(layout.manifest_path)
    return 1 if check_failed(findings, strict=args.strict) else 0


def cmd_extract_model(args: argparse.Namespace) -> int:
    case, layout = _load_pipeline_case(args)
    errors = case.validate()
    if errors:
        raise CaseConfigError("; ".join(errors))
    if not lift_stage_is_current(case, layout, holmake=args.holmake, holba=args.holba):
        run_lift_stage(case, layout, holmake=args.holmake, holba=args.holba)
    result = run_symexec_stage(
        case,
        layout,
        holmake=args.holmake,
        holba=args.holba,
        allow_fixture_fallback=args.allow_fixture_fallback,
    )
    model = result["model"]
    if not model.exists():
        raise StageError(f"binary model was not generated for {case.name}; see {layout.logs / 'symexec-holmake.log'}")
    if result.get("stage", {}).get("status") == "validation_failed":
        raise StageError(f"binary model validation failed for {case.name}; see {layout.manifest_path}")
    update_manifest(case, layout, tool_paths=_tool_paths(args))
    print(model)
    return 0


def cmd_install_ghidra(args: argparse.Namespace) -> int:
    install = install_ghidra(
        version=args.version,
        url=args.url,
        sha256=args.sha256,
        force=args.force,
    )
    print(install.headless)
    return 0


def _split_sections(value: str | None) -> list[str]:
    if not value:
        return [".text"]
    return [part.strip() for part in value.split(",") if part.strip()]


def cmd_disassemble(args: argparse.Namespace) -> int:
    headless = resolve_ghidra_headless(args.ghidra)
    if headless is None and args.install_ghidra:
        headless = install_ghidra().headless
    if headless is None:
        raise DisassemblyError("Ghidra is unavailable; run 'cryptobap2 install-ghidra' or pass --ghidra")
    result = run_ghidra_disassembly(
        Path(args.binary).resolve(),
        Path(args.output).resolve(),
        arch=args.arch,
        ghidra=headless,
        sections=_split_sections(args.sections),
    )
    print(result["output"])
    return 0


def cmd_doctor(args: argparse.Namespace) -> int:
    if args.install_ghidra and resolve_ghidra_headless(args.ghidra) is None:
        install_ghidra()
    print(f"cryptobap2 {__version__}")
    for name, status in [
        ("holba", {"path": str(args.holba), "exists": args.holba.exists(), "executable": False}),
        ("holmake", executable_status(args.holmake)),
        ("tamarin", executable_status(args.tamarin)),
        ("squirrel", executable_status(args.squirrel)),
        ("ghidra", ghidra_status(args.ghidra)),
    ]:
        marker = "ok" if status["exists"] and (name == "holba" or status["executable"]) else "missing"
        print(f"{marker}: {name}: {status['path']}")
    java = java_status()
    java_marker = "ok" if java["satisfies_ghidra"] else "missing"
    print(f"{java_marker}: java>=21: {java['path']} ({java.get('version') or 'unknown version'})")
    try:
        import yaml  # type: ignore

        print(f"ok: PyYAML: {yaml.__version__}")
    except Exception as exc:
        print(f"missing: PyYAML: {exc}")

    cases = sorted(DEFAULT_CASE_DIR.glob("*.yaml"))
    print("registered cases: " + (", ".join(path.stem for path in cases) if cases else "<none>"))
    debt_findings: list[Finding] = check_source_trust(strict=True)
    for case_path in cases:
        case, _layout = _load_layout(str(case_path), args.build_root, create=False)
        debt_findings.extend(check_case_config(case))
    unsafe = check_failed(debt_findings, strict=True)
    print(("unsafe" if unsafe else "ok") + f": strict trust findings: {len(debt_findings)}")
    return 1 if unsafe and args.strict else 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="cryptobap2", description="CryptoBAP2 production toolchain")
    parser.add_argument("--build-root", type=Path, default=DEFAULT_BUILD_ROOT, help="artifact root")
    parser.add_argument("--holba", type=Path, default=DEFAULT_HOLBA_DIR, help="HolBA root")
    parser.add_argument("--holmake", type=Path, default=DEFAULT_HOLMAKE, help="Holmake executable")
    parser.add_argument("--tamarin", type=Path, default=DEFAULT_TAMARIN, help="tamarin-prover executable")
    parser.add_argument("--squirrel", type=Path, default=DEFAULT_SQUIRREL, help="Squirrel executable")
    parser.add_argument("--ghidra", type=Path, help="Ghidra analyzeHeadless executable or Ghidra install root")
    subparsers = parser.add_subparsers(dest="command", required=True)

    init_case = subparsers.add_parser("init-case", help="create a YAML case file from a template")
    init_case.add_argument("output", help="case name or output path")
    init_case.add_argument("--name", help="case name to write into the file")
    init_case.add_argument("--template", default="xor", choices=["xor", "tinyssh", "wireguard-init", "wireguard-resp"])
    init_case.add_argument("--force", action="store_true")
    init_case.set_defaults(func=cmd_init_case)

    scaffold = subparsers.add_parser(
        "scaffold-case",
        help="create a draft YAML case by inspecting a binary or existing .da disassembly",
    )
    scaffold.add_argument("input", help="binary file, or a .da file when --from-da is set or the suffix is .da")
    scaffold.add_argument("--arch", default="arm8", help="architecture, e.g. arm8 or m0")
    scaffold.add_argument("--output", help="case output path; defaults to cases/<name>.yaml")
    scaffold.add_argument("--name", help="case name to write into the file")
    scaffold.add_argument("--theory", help="HOL theory name to generate")
    scaffold.add_argument("--symbols", help="comma-separated function symbols to include; default: infer return-like functions")
    scaffold.add_argument("--sections", default=".text", help="comma-separated executable sections to emit")
    scaffold.add_argument("--max-functions", type=int, default=16, help="maximum inferred functions when --symbols is omitted")
    scaffold.add_argument(
        "--scope",
        choices=["auto", "all-functions"],
        default="auto",
        help="inference scope; all-functions groups local labels and models every function region",
    )
    scaffold.add_argument("--no-infer-crypto", action="store_true", help="leave functions.library/adversary/crypto empty")
    scaffold.add_argument("--from-da", action="store_true", help="treat input as an existing HolBA-compatible .da file")
    scaffold.add_argument("--da-output", type=Path, help="where to store generated .da text when input is a binary")
    scaffold.add_argument("--install-ghidra", action="store_true", help="install Ghidra into opt/ when unavailable")
    scaffold.add_argument("--force", action="store_true")
    scaffold.set_defaults(func=cmd_scaffold_case)

    list_cases = subparsers.add_parser("list-cases", help="list registered cases")
    list_cases.set_defaults(func=cmd_list_cases)

    doctor = subparsers.add_parser("doctor", help="check CryptoBAP2 toolchain availability and trust debt")
    doctor.add_argument("--strict", action="store_true", help="exit non-zero when strict trust findings exist")
    doctor.add_argument("--install-ghidra", action="store_true", help="install Ghidra into opt/ when unavailable")
    doctor.set_defaults(func=cmd_doctor)

    install = subparsers.add_parser("install-ghidra", help="download and install Ghidra into opt/")
    install.add_argument("--version", default=DEFAULT_GHIDRA_VERSION)
    install.add_argument("--url", help="Ghidra release zip URL")
    install.add_argument("--sha256", help=f"expected release zip SHA-256; defaults to {DEFAULT_GHIDRA_SHA256} for {DEFAULT_GHIDRA_VERSION}")
    install.add_argument("--force", action="store_true", help="replace an existing opt/ghidra_<version> install")
    install.set_defaults(func=cmd_install_ghidra)

    disassemble = subparsers.add_parser("disassemble", help="disassemble a binary to HolBA-compatible .da text")
    disassemble.add_argument("binary", help="raw binary file")
    disassemble.add_argument("--arch", required=True, help="architecture, e.g. arm8 or m0")
    disassemble.add_argument("--output", required=True, help="output .da path")
    disassemble.add_argument("--sections", default=".text", help="comma-separated executable sections to emit")
    disassemble.add_argument("--install-ghidra", action="store_true", help="install Ghidra into opt/ when unavailable")
    disassemble.set_defaults(func=cmd_disassemble)

    def add_binary_input_options(sub: argparse.ArgumentParser) -> None:
        sub.add_argument("--arch", help="architecture for binary input or incomplete YAML, e.g. arm8 or m0")
        sub.add_argument("--sections", help="comma-separated executable sections to emit")
        sub.add_argument("--name", help="case name for binary input or incomplete YAML")
        sub.add_argument("--theory", help="HOL theory name for binary input or incomplete YAML")
        sub.add_argument("--symbols", help="comma-separated function symbols to include; default: infer return-like functions")
        sub.add_argument("--max-functions", type=int, default=16, help="maximum inferred functions when --symbols is omitted")
        sub.add_argument(
            "--scope",
            choices=["auto", "all-functions"],
            default="auto",
            help="inference scope for direct binary/.da input or incomplete YAML",
        )
        sub.add_argument("--write-case", type=Path, help="write the generated inferred YAML case to this path")

    for name, help_text, func in [
        ("lift", "materialize the stable lift-stage request", cmd_lift),
        ("symexec", "materialize the stable symbolic-execution request", cmd_symexec),
        ("translate", "stage and validate configured Tamarin SPTHY source", cmd_translate),
        ("extract-model", "generate the HOL symbolic-execution binary model", cmd_extract_model),
        ("check", "run static and artifact checks", cmd_check),
        ("run", "run the configured production pipeline", cmd_run),
    ]:
        sub = subparsers.add_parser(name, help=help_text)
        if name in {"check", "translate"}:
            sub.add_argument("case", help="case name or YAML path")
        else:
            sub.add_argument("case", help="case name, YAML path, .da file, or binary path")
        if name in {"lift", "symexec", "extract-model", "run"}:
            add_binary_input_options(sub)
        if name == "check":
            sub.add_argument("--strict", action="store_true", help="fail on proof/status/debt findings")
            sub.add_argument("--json", action="store_true", help="print diagnostics as JSON")
            sub.add_argument("--record", action="store_true", help="record diagnostics in the manifest")
        if name == "run":
            sub.add_argument("--target", choices=["squirrel", "tamarin", "all"], default="squirrel")
            sub.add_argument("--tamarin", type=Path, default=DEFAULT_TAMARIN)
            sub.add_argument("--squirrel", type=Path, default=DEFAULT_SQUIRREL)
            sub.add_argument(
                "--readable-squirrel",
                action="store_true",
                help="also emit a commented, human-readable Squirrel view beside the canonical .sp",
            )
            sub.add_argument("--install-ghidra", action="store_true", help="install Ghidra into opt/ when unavailable")
            sub.add_argument("--strict", action="store_true", help="fail on proof/status/debt findings")
        if name in {"lift", "symexec"}:
            sub.add_argument("--install-ghidra", action="store_true", help="install Ghidra into opt/ when unavailable")
        if name in {"symexec", "extract-model", "run"}:
            sub.add_argument(
                "--allow-fixture-fallback",
                action="store_true",
                help="allow failed symbolic execution to copy artifacts.sapic_source as a partial migration fallback",
            )
        if name == "extract-model":
            sub.add_argument("--install-ghidra", action="store_true", help="install Ghidra into opt/ when unavailable")
        sub.set_defaults(func=func)

    export = subparsers.add_parser("export", help="export to Tamarin and/or Squirrel artifacts")
    export.add_argument("case", help="case name or YAML path")
    export.add_argument("--build-root", type=Path, default=argparse.SUPPRESS, help="artifact root")
    export.add_argument("--target", choices=["squirrel", "tamarin", "all"], default="squirrel")
    export.add_argument("--tamarin", type=Path, default=DEFAULT_TAMARIN)
    export.add_argument("--squirrel", type=Path, default=DEFAULT_SQUIRREL)
    export.add_argument(
        "--readable-squirrel",
        action="store_true",
        help="also emit a commented, human-readable Squirrel view beside the canonical .sp",
    )
    export.set_defaults(func=cmd_export)

    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        return int(args.func(args))
    except (BackendError, CaseConfigError, DisassemblyError, FileNotFoundError, ScaffoldError, StageError, ValueError, OSError) as exc:
        print(f"cryptobap2: error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
