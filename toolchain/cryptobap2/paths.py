from __future__ import annotations

import os
import shutil
from pathlib import Path


CRYPTOBAP2_ROOT = Path(__file__).resolve().parents[2]
WORKSPACE_ROOT = CRYPTOBAP2_ROOT.parent.parent
DEFAULT_OPT_DIR = CRYPTOBAP2_ROOT / "opt"
DEFAULT_BUILD_ROOT = CRYPTOBAP2_ROOT / "_build"
DEFAULT_CASE_DIR = CRYPTOBAP2_ROOT / "cases"
DEFAULT_HOLBA_DIR = Path(
    os.environ.get("HOLBA_DIR")
    or os.environ.get("HOLBADIR")
    or WORKSPACE_ROOT / "deps" / "HolBA"
).resolve()
DEFAULT_HOLMAKE = Path(
    os.environ.get("HOLMAKE")
    or shutil.which("Holmake")
    or WORKSPACE_ROOT / "deps" / "HOL" / "bin" / "Holmake"
).resolve()


def find_vendored_tamarin(workspace_root: Path = WORKSPACE_ROOT) -> Path | None:
    install_root = workspace_root / "deps" / "tamarin-prover" / ".stack-work" / "install"
    candidates = sorted(install_root.glob("**/bin/tamarin-prover"), reverse=True)
    for candidate in candidates:
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return candidate.resolve()
    return None


def default_tamarin() -> Path:
    explicit = os.environ.get("TAMARIN")
    if explicit:
        return Path(explicit).resolve()
    vendored = find_vendored_tamarin()
    if vendored is not None:
        return vendored
    return Path(shutil.which("tamarin-prover") or Path.home() / ".local" / "bin" / "tamarin-prover").resolve()


DEFAULT_TAMARIN = default_tamarin()
DEFAULT_SQUIRREL = Path(
    os.environ.get("SQUIRREL")
    or WORKSPACE_ROOT / "deps" / "squirrel-prover" / "squirrel"
).resolve()


def _default_ghidra_headless() -> Path | None:
    explicit = os.environ.get("GHIDRA_HEADLESS")
    if explicit:
        return Path(explicit).resolve()
    home = os.environ.get("GHIDRA_HOME")
    if home:
        return (Path(home) / "support" / "analyzeHeadless").resolve()
    on_path = shutil.which("analyzeHeadless")
    if on_path:
        return Path(on_path).resolve()
    installed = sorted(DEFAULT_OPT_DIR.glob("ghidra_*/support/analyzeHeadless"), reverse=True)
    if installed:
        return installed[0].resolve()
    return None


DEFAULT_GHIDRA_HEADLESS = _default_ghidra_headless()


def resolve_under_root(value: str | Path, base: Path = CRYPTOBAP2_ROOT) -> Path:
    path = Path(value)
    if not path.is_absolute():
        path = base / path
    return path.resolve()


def ensure_workspace_path(path: Path) -> Path:
    resolved = path.resolve()
    if WORKSPACE_ROOT not in {resolved, *resolved.parents}:
        raise ValueError(f"path is outside the workspace: {path}")
    return resolved


def executable_status(path: Path) -> dict[str, object]:
    return {
        "path": str(path),
        "exists": path.exists(),
        "executable": os.access(path, os.X_OK) if path.exists() else False,
    }
