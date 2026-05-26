from __future__ import annotations

import os
from pathlib import Path


CRYPTOBAP2_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OPT_DIR = CRYPTOBAP2_ROOT / "opt"
DEFAULT_BUILD_ROOT = CRYPTOBAP2_ROOT / "_build"
DEFAULT_CASE_DIR = CRYPTOBAP2_ROOT / "cases"


def _env_path(*names: str) -> Path | None:
    for name in names:
        value = os.environ.get(name)
        if value:
            return Path(value).expanduser().resolve()
    return None


def _missing_path(label: str) -> Path:
    return Path(f"<missing:{label}>")


def _env_or_missing(label: str, *names: str) -> Path:
    return _env_path(*names) or _missing_path(label)


def default_holba_dir() -> Path:
    return _env_or_missing("HOLBA_DIR|HOLBADIR", "HOLBA_DIR", "HOLBADIR")


def default_holmake() -> Path:
    return _env_or_missing("HOLMAKE", "HOLMAKE")


def default_tamarin() -> Path:
    return _env_or_missing("TAMARIN", "TAMARIN")


def default_squirrel() -> Path:
    return _env_or_missing("SQUIRREL", "SQUIRREL")


DEFAULT_HOLBA_DIR = default_holba_dir()
DEFAULT_HOLMAKE = default_holmake()
DEFAULT_TAMARIN = default_tamarin()
DEFAULT_SQUIRREL = default_squirrel()


def _default_ghidra_headless() -> Path | None:
    explicit = os.environ.get("GHIDRA_HEADLESS")
    if explicit:
        return Path(explicit).resolve()
    home = os.environ.get("GHIDRA_HOME")
    if home:
        return (Path(home) / "support" / "analyzeHeadless").resolve()
    return None


DEFAULT_GHIDRA_HEADLESS = _default_ghidra_headless()


def resolve_config_path(value: str | Path, base: Path = CRYPTOBAP2_ROOT) -> Path:
    path = Path(value).expanduser()
    if not path.is_absolute():
        path = base / path
    return path.resolve()


def executable_status(path: Path) -> dict[str, object]:
    return {
        "path": str(path),
        "exists": path.exists(),
        "executable": os.access(path, os.X_OK) if path.exists() else False,
    }
