from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

from .config import CaseConfig
from .manifest import BuildLayout, case_config_sha256, load_manifest, sha256_file, update_manifest
from .paths import CRYPTOBAP2_ROOT
from .stages import validate_fragment_labels


def _display_path(path: Path) -> str:
    try:
        return str(path.relative_to(CRYPTOBAP2_ROOT))
    except ValueError:
        return str(path)


UNSAFE_CODES = {
    "config_error",
    "contains_cheat",
    "contains_sorry",
    "generated_hol_artifact",
    "unguarded_debug_print",
    "placeholder_squirrel",
    "missing_manifest",
    "missing_artifact",
    "missing_tamarin_source",
    "missing_hol_artifact",
    "backend_partial",
    "missing_stage",
    "missing_validation_log",
    "stale_config",
    "stale_stage_config",
    "squirrel_abstract_repair",
    "stale_artifact",
    "bad_label",
    "validation_failed",
    "tamarin_validation_failed",
    "squirrel_validation_failed",
    "missing_spthy",
    "missing_squirrel",
}


@dataclass(frozen=True)
class Finding:
    severity: str
    code: str
    message: str
    path: str | None = None
    line: int | None = None

    def as_dict(self) -> dict[str, object]:
        out: dict[str, object] = {
            "severity": self.severity,
            "code": self.code,
            "message": self.message,
        }
        if self.path:
            out["path"] = self.path
        if self.line is not None:
            out["line"] = self.line
        return out


def _iter_files(paths: Iterable[Path], suffixes: tuple[str, ...], *, exclude_parts: set[str] | None = None) -> Iterable[Path]:
    excluded = exclude_parts or set()
    for root in paths:
        if root.is_file() and root.suffix in suffixes:
            yield root
            continue
        if not root.exists():
            continue
        for path in root.rglob("*"):
            if not path.is_file() or path.suffix not in suffixes:
                continue
            parts = set(path.parts)
            if ".hol" in parts or "_build" in parts or "logbook" in parts or parts.intersection(excluded):
                continue
            yield path


def _scan_pattern(
    paths: Iterable[Path],
    suffixes: tuple[str, ...],
    pattern: str,
    code: str,
    message: str,
    *,
    exclude_parts: set[str] | None = None,
) -> list[Finding]:
    regex = re.compile(pattern)
    findings: list[Finding] = []
    for path in _iter_files(paths, suffixes, exclude_parts=exclude_parts):
        try:
            lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
        except OSError:
            continue
        for number, line in enumerate(lines, start=1):
            if regex.search(line):
                findings.append(
                    Finding("error", code, message, _display_path(path), number)
                )
    return findings


def _strip_sml_block_comments(line: str, depth: int) -> tuple[str, int]:
    output: list[str] = []
    index = 0
    while index < len(line):
        if line.startswith("(*", index):
            depth += 1
            index += 2
        elif depth > 0 and line.startswith("*)", index):
            depth -= 1
            index += 2
        elif depth == 0:
            output.append(line[index])
            index += 1
        else:
            index += 1
    return "".join(output), depth


def _scan_unguarded_debug_prints(paths: Iterable[Path], *, exclude_parts: set[str] | None = None) -> list[Finding]:
    regex = re.compile(r"\bval\s+_\s*=\s*(?:print|print_term)\b|\bprint_thm\b")
    findings: list[Finding] = []
    for path in _iter_files(paths, (".sml",), exclude_parts=exclude_parts):
        comment_depth = 0
        try:
            lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
        except OSError:
            continue
        for number, line in enumerate(lines, start=1):
            code, comment_depth = _strip_sml_block_comments(line, comment_depth)
            if regex.search(code):
                findings.append(
                    Finding(
                        "error",
                        "unguarded_debug_print",
                        "production-loaded SML contains direct debug printing",
                        _display_path(path),
                        number,
                    )
                )
    return findings


def check_case_config(case: CaseConfig) -> list[Finding]:
    findings = [
        Finding("error", diagnostic.code, diagnostic.message, str(case.path))
        for diagnostic in case.validation_diagnostics()
    ]
    if case.input_da is not None and not case.input_da.exists():
        findings.append(Finding("error", "missing_input", f"input.da does not exist: {case.input_da}", str(case.path)))
    if case.input_binary is not None and not case.input_binary.exists():
        findings.append(
            Finding("error", "missing_input", f"input.binary does not exist: {case.input_binary}", str(case.path))
        )
    sapic_source = case.artifacts.get("sapic_source")
    if sapic_source is not None and not sapic_source.exists():
        findings.append(
            Finding("error", "missing_artifact", f"artifacts.sapic_source does not exist: {sapic_source}", str(case.path))
        )
    tamarin_source = case.artifacts.get("tamarin_source")
    if "squirrel" in case.backends and tamarin_source is None:
        findings.append(
            Finding(
                "error",
                "missing_tamarin_source",
                "Squirrel backend requires artifacts.tamarin_source",
                str(case.path),
            )
        )
    if tamarin_source is not None and not tamarin_source.exists():
        findings.append(
            Finding(
                "error",
                "missing_artifact",
                f"artifacts.tamarin_source does not exist: {tamarin_source}",
                str(case.path),
            )
        )
    return findings


def check_source_trust(strict: bool) -> list[Finding]:
    roots = [
        CRYPTOBAP2_ROOT / "src",
    ]
    findings: list[Finding] = []
    findings.extend(
        _scan_pattern(
            roots,
            (".sml",),
            r"\bcheat\b",
            "contains_cheat",
            "HOL source contains 'cheat'",
            exclude_parts={"examples"},
        )
    )
    if strict:
        findings.extend(_scan_unguarded_debug_prints(roots, exclude_parts={"examples"}))

    for hol_dir in CRYPTOBAP2_ROOT.rglob(".hol"):
        if "_build" in hol_dir.parts:
            continue
        findings.append(
            Finding(
                "error" if strict else "warning",
                "generated_hol_artifact",
                "generated HOL build directory is present in source tree",
                str(hol_dir.relative_to(CRYPTOBAP2_ROOT)),
            )
        )
    return findings


def _active_backends(case: CaseConfig, backends: list[str] | None) -> list[str]:
    return case.backends if backends is None else backends


def _stage_applies_to_backends(case: CaseConfig, stage: str, active_backends: list[str]) -> bool:
    if stage == "export_squirrel":
        return "squirrel" in active_backends
    if stage == "stage_spthy":
        return "squirrel" in active_backends or "tamarin" in active_backends
    if stage in {"export_tamarin", "translate"}:
        return False
    return True


def _artifact_applies_to_backends(case: CaseConfig, name: str, active_backends: list[str]) -> bool:
    if name in {"squirrel", "readable_squirrel", "export_squirrel_log"}:
        return "squirrel" in active_backends
    if name in {"sapic", "translate_log"}:
        return False
    return True


def _required_backend_stages(active_backends: list[str]) -> list[str]:
    stages: list[str] = []
    if "tamarin" in active_backends or "squirrel" in active_backends:
        stages.append("stage_spthy")
    if "squirrel" in active_backends:
        stages.append("export_squirrel")
    return stages


def check_manifest_integrity(
    case: CaseConfig,
    layout: BuildLayout,
    *,
    backends: list[str] | None = None,
) -> list[Finding]:
    manifest = load_manifest(layout.manifest_path)
    findings: list[Finding] = []
    if not manifest:
        return [Finding("error", "missing_manifest", "manifest has not been generated", str(layout.manifest_path))]
    if manifest.get("config") != case.to_manifest_config():
        findings.append(
            Finding(
                "error",
                "stale_config",
                "manifest config does not match the current case file",
                str(layout.manifest_path),
            )
        )
    current_config_sha = case_config_sha256(case)
    active_backends = _active_backends(case, backends)
    manifest_stages = manifest.get("stages", {})
    for stage in _required_backend_stages(active_backends):
        if stage not in manifest_stages:
            findings.append(
                Finding(
                    "error",
                    "missing_stage",
                    f"required backend stage {stage} has not been recorded",
                    str(layout.manifest_path),
                )
            )
    for name, record in manifest.get("artifacts", {}).items():
        if not _artifact_applies_to_backends(case, name, active_backends):
            continue
        path_text = record.get("path") if isinstance(record, dict) else None
        expected = record.get("sha256") if isinstance(record, dict) else None
        if isinstance(record, dict) and record.get("exists") is False:
            findings.append(
                Finding(
                    "error",
                    "missing_artifact",
                    f"manifest artifact {name} was not generated",
                    str(path_text or layout.manifest_path),
                )
            )
            continue
        if not path_text or not expected:
            continue
        path = Path(path_text)
        if not path.exists():
            findings.append(Finding("error", "missing_artifact", f"manifest artifact {name} is missing", str(path)))
            continue
        actual = sha256_file(path)
        if actual != expected:
            findings.append(Finding("error", "stale_artifact", f"manifest hash for {name} is stale", str(path)))
    for stage, data in manifest.get("stages", {}).items():
        if not isinstance(data, dict):
            continue
        if not _stage_applies_to_backends(case, stage, active_backends):
            continue
        stage_config_sha = data.get("case_config_sha256")
        if isinstance(stage_config_sha, str) and stage_config_sha != current_config_sha:
            findings.append(
                Finding(
                    "error",
                    "stale_stage_config",
                    f"stage {stage} was generated for a different case configuration",
                    str(layout.manifest_path),
                )
            )
        status = data.get("status")
        if status == "backend_partial":
            findings.append(Finding("warning", "backend_partial", f"stage {stage} used a partial backend or migration fallback"))
        if status == "validation_failed":
            findings.append(Finding("error", "validation_failed", f"stage {stage} failed validation"))
        if status == "missing":
            findings.append(Finding("warning", "missing_stage", f"stage {stage} was skipped or unavailable"))
        repairs = data.get("squirrel_abstract_repairs")
        if repairs:
            findings.append(Finding("warning", "squirrel_abstract_repair", f"stage {stage} repaired missing Squirrel abstracts"))
        for diagnostic in data.get("diagnostics", []):
            if not isinstance(diagnostic, dict):
                continue
            findings.append(
                Finding(
                    str(diagnostic.get("severity", "warning")),
                    str(diagnostic.get("code", "stage_diagnostic")),
                    f"stage {stage}: {diagnostic.get('message', '')}",
                )
            )
    return findings


def check_label_artifacts(case: CaseConfig, layout: BuildLayout) -> list[Finding]:
    findings: list[Finding] = []
    for diagnostic in validate_fragment_labels(case, layout):
        findings.append(
            Finding(
                str(diagnostic.get("severity", "warning")),
                str(diagnostic.get("code", "label_validation")),
                str(diagnostic.get("message", "")),
            )
        )
    return findings


def check_backend_artifacts(
    case: CaseConfig,
    layout: BuildLayout,
    *,
    strict: bool,
    backends: list[str] | None = None,
) -> list[Finding]:
    findings: list[Finding] = []
    active_backends = _active_backends(case, backends)
    spthy = layout.spthy / f"{case.name}.spthy"
    sp = layout.squirrel / f"{case.name}.sp"
    if not spthy.exists() and ("tamarin" in active_backends or "squirrel" in active_backends):
        findings.append(Finding("error", "missing_spthy", "Tamarin SPTHY source has not been staged", str(spthy)))
    elif spthy.exists():
        text = spthy.read_text(encoding="utf-8", errors="replace")
        for number, line in enumerate(text.splitlines(), start=1):
            if "by sorry" in line:
                findings.append(
                    Finding("error", "contains_sorry", "Tamarin artifact contains 'by sorry'", str(spthy), number)
                )
    if "squirrel" in active_backends:
        if not sp.exists():
            findings.append(Finding("error", "missing_artifact", "Squirrel artifact has not been generated", str(sp)))
        elif "placeholder" in sp.read_text(encoding="utf-8", errors="replace").lower():
            findings.append(Finding("error", "placeholder_squirrel", "Squirrel artifact is a placeholder", str(sp)))
        validate_log = layout.logs / "squirrel-validate.log"
        if validate_log.exists():
            log_text = validate_log.read_text(encoding="utf-8", errors="replace")
            if "Fatal error" in log_text or "Typing.Error" in log_text:
                findings.append(
                    Finding(
                        "error",
                        "squirrel_validation_failed",
                        "Squirrel validation failed; see validation log",
                        str(validate_log),
                    )
                )
        elif strict and sp.exists():
            findings.append(Finding("error", "missing_validation_log", "Squirrel validation log is missing", str(validate_log)))
    tamarin_log = layout.logs / "tamarin-validate.log"
    if strict and ("tamarin" in active_backends or "squirrel" in active_backends) and spthy.exists() and not tamarin_log.exists():
        findings.append(Finding("error", "missing_validation_log", "Tamarin validation log is missing", str(tamarin_log)))
    return findings


def run_checks(
    case: CaseConfig,
    layout: BuildLayout,
    *,
    strict: bool = False,
    record: bool = False,
    backends: list[str] | None = None,
) -> list[Finding]:
    findings: list[Finding] = []
    findings.extend(check_case_config(case))
    findings.extend(check_source_trust(strict))
    findings.extend(check_label_artifacts(case, layout))
    findings.extend(check_manifest_integrity(case, layout, backends=backends))
    findings.extend(check_backend_artifacts(case, layout, strict=strict, backends=backends))
    if record:
        update_manifest(
            case,
            layout,
            command="check",
            diagnostics=[finding.as_dict() for finding in findings],
            refresh_case_metadata=False,
        )
    return findings


def check_failed(findings: list[Finding], *, strict: bool) -> bool:
    always_fail = {
        "config_error",
        "missing_field",
        "missing_manifest",
        "missing_input",
        "missing_artifact",
        "missing_tamarin_source",
        "missing_hol_artifact",
        "missing_symbol",
        "missing_stage",
        "missing_label",
        "stale_config",
        "stale_stage_config",
        "bad_symbol",
        "bad_type",
        "bad_name",
        "bad_backend",
        "bad_status",
        "bad_fragment",
        "bad_label",
        "bad_disassembly_tool",
        "validation_failed",
        "tamarin_validation_failed",
        "squirrel_validation_failed",
        "missing_spthy",
        "missing_squirrel",
        "ghidra_failed",
        "empty_disassembly",
        "bad_disassembly",
    }
    for finding in findings:
        if finding.severity == "error" and (strict or finding.code in always_fail):
            return True
    if strict and any(finding.code in UNSAFE_CODES for finding in findings):
        return True
    return False
