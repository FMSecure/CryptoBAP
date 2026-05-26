from __future__ import annotations

import hashlib
import json
import shutil
import subprocess
from pathlib import Path
from typing import Any

from .manifest import BuildLayout, ensure_layout, sha256_file
from .paths import CRYPTOBAP2_ROOT, DEFAULT_HOLBA_DIR, DEFAULT_HOLMAKE


class HolSupportError(RuntimeError):
    pass


HOL_SOURCE_DIRS = ("tree", "sapic", "translate_to_sapic", "pretty_print", "pipeline_support")
HOL_SUPPORT_CACHE_DIRNAME = "_cryptobap2-support-cache"
HOL_SOURCE_ROOT = CRYPTOBAP2_ROOT / "src"
PIPELINE_SUPPORT_ROOT = HOL_SOURCE_ROOT / "pipeline_support"
HOLBA_DEPENDENCY_DIRS = (
    "src/extra",
    "src/theory/bir",
    "src/theory/bir-support",
    "src/shared",
    "src/shared/convs",
    "src/shared/smt",
    "src/tools/cfg",
    "src/tools/exec",
    "src/tools/lifter",
    "src/tools/symbexec",
)
PIPELINE_SUPPORT_FILES = (
    Path("bir_constpropLib.sml"),
    Path("bir_exp_helperLib.sml"),
    Path("bir_symbexec_PreprocessLib.sml"),
    Path("bir_symbexec_compLib.sml"),
    Path("bir_symbexec_coreLib.sml"),
    Path("bir_symbexec_funcLib.sml"),
    Path("bir_symbexec_oracleLib.sml"),
    Path("bir_symbexec_sortLib.sml"),
    Path("bir_symbexec_stateLib.sml"),
    Path("bir_symbexec_stepLib.sml"),
    Path("bir_symbexec_sumLib.sml"),
    Path("bir_symbexec_treeLib.sml"),
    Path("commonBalrobScriptLib.sml"),
    Path("imlLib.sml"),
    Path("pipelineConfigLib.sml"),
    Path("yamlLib.sml"),
    Path("binariesLib.sml"),
    Path("bir_auxiliaryLib.sml"),
)


def _write_json(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _ignore_hol_source_artifact(name: str) -> bool:
    return (
        name == ".hol"
        or name == "Holmakefile.gen"
        or name == "exec_output.txt"
        or name.endswith("Theory.txt")
        or name == "__pycache__"
    )


def _link_source_file(source: Path, target: Path) -> None:
    if target.is_symlink():
        try:
            if target.resolve() == source.resolve():
                return
        except OSError:
            pass
    if target.is_symlink() or target.is_file():
        target.unlink()
    elif target.exists():
        shutil.rmtree(target)
    target.symlink_to(source)


def _validate_hol_sources() -> None:
    missing: list[str] = []
    for dirname in HOL_SOURCE_DIRS:
        if not (HOL_SOURCE_ROOT / dirname).is_dir():
            missing.append(str(HOL_SOURCE_ROOT / dirname))
    for relative in PIPELINE_SUPPORT_FILES:
        if not (PIPELINE_SUPPORT_ROOT / relative).is_file():
            missing.append(str(PIPELINE_SUPPORT_ROOT / relative))
    if missing:
        raise HolSupportError("CryptoBAP2 HOL support sources are incomplete: " + ", ".join(sorted(missing)))


def _iter_hol_source_files() -> list[tuple[Path, Path]]:
    files: list[tuple[Path, Path]] = []
    for dirname in HOL_SOURCE_DIRS:
        source_dir = HOL_SOURCE_ROOT / dirname
        for source in sorted(source_dir.iterdir()):
            if _ignore_hol_source_artifact(source.name) or not source.is_file():
                continue
            files.append((Path(dirname) / source.name, source))
    return files


def _git_dir(root: Path) -> Path | None:
    dot_git = root / ".git"
    if dot_git.is_dir():
        return dot_git
    if dot_git.is_file():
        text = dot_git.read_text(encoding="utf-8", errors="replace").strip()
        prefix = "gitdir:"
        if text.startswith(prefix):
            path = Path(text[len(prefix) :].strip())
            return path if path.is_absolute() else (root / path).resolve()
    return None


def _hash_file_marker(digest: hashlib._Hash, label: str, path: Path) -> None:
    digest.update(label.encode("utf-8") + b"\0")
    digest.update(str(path.resolve()).encode("utf-8") + b"\0")
    if not path.exists():
        digest.update(b"<missing>\0")
        return
    if path.is_file():
        digest.update(b"file\0")
        digest.update(sha256_file(path).encode("ascii") + b"\0")
    elif path.is_dir():
        digest.update(b"dir\0")
    else:
        digest.update(b"other\0")


def _iter_holba_dependency_files(holba: Path) -> list[tuple[Path, Path]]:
    files: list[tuple[Path, Path]] = []
    for dirname in HOLBA_DEPENDENCY_DIRS:
        root = holba / dirname
        if not root.is_dir():
            continue
        for source in sorted(root.rglob("*")):
            if not source.is_file() or _ignore_hol_source_artifact(source.name):
                continue
            if any(part in {".hol", "build", "__pycache__"} for part in source.parts):
                continue
            files.append((source.relative_to(holba), source))
    return files


def _hash_holba_dependency_files(digest: hashlib._Hash, holba: Path, label: str) -> None:
    files = _iter_holba_dependency_files(holba)
    digest.update(f"{label}-count:{len(files)}".encode("ascii") + b"\0")
    for relative, source in files:
        digest.update(str(relative).encode("utf-8") + b"\0")
        digest.update(sha256_file(source).encode("ascii") + b"\0")


def _git_dependency_status(holba: Path) -> str | None:
    try:
        result = subprocess.run(
            [
                "git",
                "-C",
                str(holba),
                "status",
                "--porcelain=v1",
                "--untracked-files=all",
                "--",
                *HOLBA_DEPENDENCY_DIRS,
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
        )
    except OSError:
        return None
    if result.returncode != 0:
        return None
    return result.stdout


def _holba_dependency_hash(holba: Path) -> str:
    digest = hashlib.sha256()
    resolved = holba.expanduser().resolve()
    digest.update(b"holba-dependencies-v1\0")
    digest.update(str(resolved).encode("utf-8") + b"\0")

    git_dir = _git_dir(resolved)
    if git_dir is not None:
        digest.update(b"holba-git-fast\0")
        _hash_file_marker(digest, "holba-git-head", git_dir / "HEAD")
        head = git_dir / "HEAD"
        if head.exists():
            text = head.read_text(encoding="utf-8", errors="replace").strip()
            ref_prefix = "ref:"
            if text.startswith(ref_prefix):
                ref_path = git_dir / text[len(ref_prefix) :].strip()
                _hash_file_marker(digest, "holba-git-ref", ref_path)
        _hash_file_marker(digest, "holba-git-index", git_dir / "index")
        status = _git_dependency_status(resolved)
        if status is None:
            digest.update(b"holba-git-status-unavailable\0")
            _hash_holba_dependency_files(digest, resolved, "holba-source")
        else:
            digest.update(b"holba-git-status\0")
            digest.update(status.encode("utf-8") + b"\0")
            if status:
                _hash_holba_dependency_files(digest, resolved, "holba-dirty-source")
        return digest.hexdigest()
    else:
        digest.update(b"holba-git-missing\0")

    _hash_holba_dependency_files(digest, resolved, "holba-source")
    return digest.hexdigest()


def _hol_support_cache_key(
    *,
    holmake: Path,
    holba: Path,
    holba_dependency_hash: str,
    source_files: list[tuple[Path, Path]],
) -> str:
    digest = hashlib.sha256()
    digest.update(b"cryptobap2-hol-support-v2\0")
    digest.update(str(CRYPTOBAP2_ROOT.resolve()).encode("utf-8") + b"\0")
    digest.update(str(holba.resolve()).encode("utf-8") + b"\0")
    digest.update(str(holmake.resolve()).encode("utf-8") + b"\0")
    _hash_file_marker(digest, "holmake", holmake)
    digest.update(holba_dependency_hash.encode("ascii") + b"\0")
    for relative, source in source_files:
        digest.update(str(relative).encode("utf-8") + b"\0")
        digest.update(sha256_file(source).encode("ascii") + b"\0")
    return digest.hexdigest()[:24]


def clear_legacy_case_source_view(layout: BuildLayout) -> None:
    legacy = layout.work / "src"
    if legacy.is_symlink() or legacy.is_file():
        legacy.unlink()
    elif legacy.exists():
        shutil.rmtree(legacy)


def stage_hol_sources(
    layout: BuildLayout,
    *,
    holmake: Path = DEFAULT_HOLMAKE,
    holba: Path = DEFAULT_HOLBA_DIR,
) -> Path:
    """Create a shared symlink view of CryptoBAP2 HOL sources."""
    ensure_layout(layout)
    _validate_hol_sources()
    clear_legacy_case_source_view(layout)

    holba_dependency_hash = _holba_dependency_hash(holba)
    source_files = _iter_hol_source_files()
    cache_root = layout.root.parent / HOL_SUPPORT_CACHE_DIRNAME / _hol_support_cache_key(
        holmake=holmake,
        holba=holba,
        holba_dependency_hash=holba_dependency_hash,
        source_files=source_files,
    )
    staged_root = cache_root / "src"
    staged_root.mkdir(parents=True, exist_ok=True)
    for relative, source in source_files:
        target_dir = staged_root / relative.parent
        target_dir.mkdir(parents=True, exist_ok=True)
        _link_source_file(source, target_dir / source.name)
    _write_json(
        cache_root / "source-manifest.json",
        {
            "cache_key": cache_root.name,
            "cryptobap2_root": str(CRYPTOBAP2_ROOT.resolve()),
            "holba": str(holba.resolve()),
            "holba_dependency_hash": holba_dependency_hash,
            "holmake": str(holmake.resolve()),
            "source_files": [str(relative) for relative, _source in source_files],
        },
    )
    return staged_root


def holmake_includes(source_root: Path | None) -> str:
    includes = [
        "$(HOLBA_ROOT)/src/theory/bir-support",
        "$(HOLBA_ROOT)/src/theory/bir",
        "$(HOLBA_ROOT)/src/extra",
        "$(HOLBA_ROOT)/src/shared",
        "$(HOLBA_ROOT)/src/shared/convs",
        "$(HOLBA_ROOT)/src/shared/smt",
        "$(HOLBA_ROOT)/src/theory/program_logic",
        "$(HOLBA_ROOT)/src/theory/tools/wp",
        "$(HOLBA_ROOT)/src/theory/tools/comp",
        "$(HOLBA_ROOT)/src/theory/tools/symbexec",
        "$(HOLBA_ROOT)/src/theory/tools/lifter",
        "$(HOLBA_ROOT)/src/tools/lifter",
        "$(HOLBA_ROOT)/src/tools/cfg",
        "$(HOLBA_ROOT)/src/tools/exec",
        "$(HOLBA_ROOT)/src/tools/symbexec",
    ]
    if source_root is not None:
        source_root = source_root.resolve()
        includes.extend(
            [
                "$(CRYPTOBAP2_SRC)/pipeline_support",
                "$(CRYPTOBAP2_SRC)/tree",
                "$(CRYPTOBAP2_SRC)/sapic",
                "$(CRYPTOBAP2_SRC)/translate_to_sapic",
                "$(CRYPTOBAP2_SRC)/pretty_print",
            ]
        )

    lines: list[str] = []
    for index, include in enumerate(includes):
        suffix = " \\" if index + 1 < len(includes) else ""
        lines.append(f"{'INCLUDES = ' if index == 0 else '           '}{include}{suffix}")
    return "\n".join(lines)
