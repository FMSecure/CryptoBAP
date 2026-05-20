from __future__ import annotations

import hashlib
import json
import os
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from . import __version__
from .config import CaseConfig
from .paths import DEFAULT_BUILD_ROOT


MANIFEST_SCHEMA = "cryptobap2-manifest-v3"
ARTIFACT_DIRS = ("work", "bir", "tree", "model", "sapic", "spthy", "squirrel", "logs")


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def sha256_json(data: Any) -> str:
    payload = json.dumps(data, sort_keys=True, default=str, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def case_config_sha256(case: CaseConfig) -> str:
    return sha256_json(case.to_manifest_config())


@dataclass(frozen=True)
class BuildLayout:
    root: Path
    work: Path
    bir: Path
    tree: Path
    sapic: Path
    spthy: Path
    squirrel: Path
    logs: Path

    @property
    def manifest_path(self) -> Path:
        return self.root / "manifest.json"

    @property
    def model(self) -> Path:
        return self.root / "model"

    def as_dict(self) -> dict[str, str]:
        return {name: str(getattr(self, name)) for name in ("root", *ARTIFACT_DIRS)}


def layout_for_case(case: CaseConfig, build_root: Path = DEFAULT_BUILD_ROOT) -> BuildLayout:
    root = build_root / case.name
    return BuildLayout(
        root=root,
        work=root / "work",
        bir=root / "bir",
        tree=root / "tree",
        sapic=root / "sapic",
        spthy=root / "spthy",
        squirrel=root / "squirrel",
        logs=root / "logs",
    )


def ensure_layout(layout: BuildLayout) -> None:
    for dirname in ARTIFACT_DIRS:
        getattr(layout, dirname).mkdir(parents=True, exist_ok=True)


def load_manifest(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    return json.loads(path.read_text(encoding="utf-8"))


def write_manifest(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(data, indent=2, sort_keys=True) + "\n"
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(payload, encoding="utf-8")
    os.replace(tmp, path)


def artifact_record(path: Path, kind: str) -> dict[str, Any]:
    if not path.exists():
        return {"path": str(path), "kind": kind, "exists": False}
    return {
        "path": str(path),
        "kind": kind,
        "exists": True,
        "bytes": path.stat().st_size,
        "sha256": sha256_file(path),
        "updated_at": utc_now(),
    }


def base_manifest(case: CaseConfig, layout: BuildLayout) -> dict[str, Any]:
    return {
        "schema": MANIFEST_SCHEMA,
        "tool": {
            "name": "cryptobap2",
            "version": __version__,
        },
        "case": case.name,
        "case_file": str(case.path),
        "created_at": utc_now(),
        "updated_at": utc_now(),
        "layout": layout.as_dict(),
        "config": case.to_manifest_config(),
        "proof_status": case.proof_status,
        "stages": {},
        "artifacts": {},
        "diagnostics": [],
        "commands": [],
        "tool_paths": {},
    }


def update_manifest(
    case: CaseConfig,
    layout: BuildLayout,
    *,
    command: str | None = None,
    stage: str | None = None,
    stage_data: dict[str, Any] | None = None,
    artifacts: dict[str, Path] | None = None,
    diagnostics: list[dict[str, Any]] | None = None,
    tool_paths: dict[str, Any] | None = None,
    refresh_case_metadata: bool = True,
) -> dict[str, Any]:
    manifest = load_manifest(layout.manifest_path) or base_manifest(case, layout)
    manifest["schema"] = MANIFEST_SCHEMA
    manifest["tool"] = {
        "name": "cryptobap2",
        "version": __version__,
    }
    manifest["updated_at"] = utc_now()
    manifest["layout"] = layout.as_dict()
    if refresh_case_metadata or "config" not in manifest:
        manifest["config"] = case.to_manifest_config()
    if refresh_case_metadata or "proof_status" not in manifest:
        manifest["proof_status"] = case.proof_status
    manifest.setdefault("commands", [])
    if command:
        manifest["commands"].append({"command": command, "updated_at": utc_now()})
    if tool_paths:
        manifest["tool_paths"] = tool_paths
    if stage:
        manifest.setdefault("stages", {})[stage] = {
            "updated_at": utc_now(),
            **(stage_data or {}),
        }
    if artifacts:
        artifact_block = manifest.setdefault("artifacts", {})
        for name, path in artifacts.items():
            artifact_block[name] = artifact_record(path, name)
    if diagnostics is not None:
        manifest["diagnostics"] = diagnostics
    write_manifest(layout.manifest_path, manifest)
    return manifest
