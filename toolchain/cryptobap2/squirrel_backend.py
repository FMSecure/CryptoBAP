from __future__ import annotations

import shutil
import subprocess
from pathlib import Path
from typing import Any

from .config import CaseConfig
from .manifest import BuildLayout, case_config_sha256, ensure_layout, load_manifest, sha256_file, update_manifest
from .paths import DEFAULT_SQUIRREL, DEFAULT_TAMARIN
from .readable_squirrel import write_readable_squirrel
from .source_segments import write_source_segment_files


class BackendError(RuntimeError):
    pass


def _write_log(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _has_errors(diagnostics: list[dict[str, Any]]) -> bool:
    return any(item.get("severity") == "error" for item in diagnostics)


def _stage_matches_case(manifest: dict[str, Any], stage_name: str, case: CaseConfig) -> bool:
    stage = manifest.get("stages", {}).get(stage_name)
    return isinstance(stage, dict) and stage.get("case_config_sha256") == case_config_sha256(case)


def _artifact_hash_matches(manifest: dict[str, Any], name: str, path: Path) -> bool:
    record = manifest.get("artifacts", {}).get(name)
    if not isinstance(record, dict) or not path.exists():
        return False
    expected = record.get("sha256")
    return isinstance(expected, str) and sha256_file(path) == expected


def _source_hash_matches(case: CaseConfig, manifest: dict[str, Any], stage_name: str) -> bool:
    source = case.artifacts.get("tamarin_source")
    stage = manifest.get("stages", {}).get(stage_name)
    if source is None or not source.exists() or not isinstance(stage, dict):
        return False
    expected = stage.get("source_sha256")
    return isinstance(expected, str) and sha256_file(source) == expected


def _spthy_is_current(case: CaseConfig, manifest: dict[str, Any], path: Path) -> bool:
    if not path.exists() or not manifest:
        return False
    return (
        _stage_matches_case(manifest, "stage_spthy", case)
        and _source_hash_matches(case, manifest, "stage_spthy")
        and _artifact_hash_matches(manifest, "spthy", path)
    )


def _require_tamarin_source(case: CaseConfig) -> Path:
    source = case.artifacts.get("tamarin_source")
    if source is None:
        raise BackendError(
            f"{case.name} requires artifacts.tamarin_source; CryptoBAP2 no longer generates SPTHY from Sapic"
        )
    if not source.exists():
        raise BackendError(f"Tamarin source does not exist: {source}")
    return source


def stage_spthy(
    case: CaseConfig,
    layout: BuildLayout,
    *,
    tamarin: Path = DEFAULT_TAMARIN,
) -> dict[str, Any]:
    ensure_layout(layout)
    source = _require_tamarin_source(case)
    spthy_output = layout.spthy / f"{case.name}.spthy"
    if source.resolve() != spthy_output.resolve():
        shutil.copyfile(source, spthy_output)

    diagnostics = validate_tamarin_spthy(spthy_output, layout, tamarin=tamarin)
    status = "validation_failed" if _has_errors(diagnostics) else "generated_unchecked"
    artifact_map = {"spthy": spthy_output}
    artifact_map.update(write_source_segment_files(case, layout, folders=("spthy",)))
    update_manifest(
        case,
        layout,
        stage="stage_spthy",
        stage_data={
            "status": status,
            "source": str(source),
            "source_kind": "tamarin_source",
            "source_sha256": sha256_file(source),
            "case_config_sha256": case_config_sha256(case),
            "diagnostics": diagnostics,
        },
        artifacts=artifact_map,
    )
    return {"spthy": spthy_output, "diagnostics": diagnostics, "status": status}


def _run_tamarin_squirrel_export(tamarin: Path, spthy: Path, sp: Path, log_path: Path) -> None:
    if not tamarin.exists():
        raise BackendError(f"tamarin-prover not found: {tamarin}")
    sp.parent.mkdir(parents=True, exist_ok=True)
    result = subprocess.run(
        [
            str(tamarin.resolve()),
            "--derivcheck-timeout=0",
            "--output-module=squirrel",
            f"--output={sp.resolve()}",
            str(spthy.resolve()),
        ],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    _write_log(log_path, result.stdout)
    if result.returncode != 0:
        raise BackendError(f"Tamarin Squirrel export failed; see {log_path}")
    if not sp.exists():
        raise BackendError(f"Tamarin Squirrel export did not create {sp}; see {log_path}")


def export_squirrel(
    case: CaseConfig,
    layout: BuildLayout,
    *,
    tamarin: Path | None = None,
    squirrel: Path = DEFAULT_SQUIRREL,
    readable: bool = False,
) -> dict[str, Any]:
    ensure_layout(layout)
    spthy_output = layout.spthy / f"{case.name}.spthy"
    tamarin_path = tamarin or DEFAULT_TAMARIN
    manifest = load_manifest(layout.manifest_path)
    stage_result: dict[str, Any] = {"diagnostics": []}
    if not _spthy_is_current(case, manifest, spthy_output):
        stage_result = stage_spthy(case, layout, tamarin=tamarin_path)
    if _has_errors(stage_result.get("diagnostics", [])):
        raise BackendError(f"Tamarin SPTHY validation failed for {case.name}; see {layout.logs / 'tamarin-validate.log'}")

    sp_output = layout.squirrel / f"{case.name}.sp"
    log_path = layout.logs / "export-squirrel.log"
    _run_tamarin_squirrel_export(tamarin_path, spthy_output, sp_output, log_path)

    diagnostics = validate_backend_outputs(
        spthy_output,
        sp_output,
        layout,
        tamarin=tamarin_path,
        squirrel=squirrel,
        validate_tamarin=False,
    )
    status = "validation_failed" if _has_errors(diagnostics) else "generated_unchecked"
    readable_result = write_readable_squirrel(case, layout, sp_output) if readable else None
    artifact_map = {"spthy": spthy_output, "squirrel": sp_output, "export_squirrel_log": log_path}
    if readable_result is not None:
        artifact_map["readable_squirrel"] = readable_result.path
    artifact_map.update(write_source_segment_files(case, layout, folders=("squirrel",)))
    update_manifest(
        case,
        layout,
        stage="export_squirrel",
        stage_data={
            "status": status,
            "effective_exporter": "tamarin",
            "tamarin": str(tamarin_path),
            "squirrel": str(squirrel),
            "case_config_sha256": case_config_sha256(case),
            "log": str(log_path),
            "readable_squirrel": str(readable_result.path) if readable_result is not None else None,
            "readable_squirrel_renamed_identifiers": (
                readable_result.renamed_identifiers if readable_result is not None else 0
            ),
            "readable_squirrel_annotated_calls": readable_result.annotated_calls if readable_result is not None else 0,
            "readable_squirrel_call_targets": readable_result.call_targets if readable_result is not None else 0,
            "diagnostics": diagnostics,
        },
        artifacts=artifact_map,
    )
    return {
        "spthy": spthy_output,
        "squirrel": sp_output,
        "readable_squirrel": readable_result.path if readable_result is not None else None,
        "log": log_path,
        "status": status,
        "effective_exporter": "tamarin",
        "diagnostics": diagnostics,
    }


def validate_tamarin_spthy(spthy: Path, layout: BuildLayout, *, tamarin: Path = DEFAULT_TAMARIN) -> list[dict[str, Any]]:
    diagnostics: list[dict[str, Any]] = []
    if not spthy.exists():
        return [{"severity": "error", "code": "missing_spthy", "message": str(spthy)}]
    if "by sorry" in spthy.read_text(encoding="utf-8", errors="replace"):
        diagnostics.append({"severity": "error", "code": "contains_sorry", "message": str(spthy)})
    if not tamarin.exists():
        diagnostics.append({"severity": "error", "code": "missing_tamarin", "message": str(tamarin)})
        return diagnostics

    log_path = layout.logs / "tamarin-validate.log"
    result = subprocess.run(
        [str(tamarin.resolve()), "--parse-only", str(spthy.resolve())],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    _write_log(log_path, result.stdout)
    if result.returncode != 0:
        diagnostics.append(
            {
                "severity": "error",
                "code": "tamarin_validation_failed",
                "message": str(log_path),
            }
        )
    return diagnostics


def validate_backend_outputs(
    spthy: Path,
    sp: Path,
    layout: BuildLayout,
    *,
    tamarin: Path = DEFAULT_TAMARIN,
    squirrel: Path = DEFAULT_SQUIRREL,
    validate_tamarin: bool = True,
) -> list[dict[str, Any]]:
    diagnostics: list[dict[str, Any]] = []
    if validate_tamarin:
        diagnostics.extend(validate_tamarin_spthy(spthy, layout, tamarin=tamarin))

    if not sp.exists():
        diagnostics.append({"severity": "error", "code": "missing_squirrel", "message": str(sp)})
    elif "placeholder" in sp.read_text(encoding="utf-8", errors="replace").lower():
        diagnostics.append({"severity": "error", "code": "placeholder_squirrel", "message": str(sp)})

    if sp.exists() and squirrel.exists():
        log_path = layout.logs / "squirrel-validate.log"
        result = subprocess.run(
            [str(squirrel.resolve()), str(sp.resolve())],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            cwd=str(layout.root.resolve()),
        )
        _write_log(log_path, result.stdout)
        if result.returncode != 0:
            diagnostics.append(
                {
                    "severity": "error",
                    "code": "squirrel_validation_failed",
                    "message": str(log_path),
                }
            )
    elif sp.exists():
        diagnostics.append({"severity": "warning", "code": "missing_squirrel_binary", "message": str(squirrel)})
    return diagnostics
