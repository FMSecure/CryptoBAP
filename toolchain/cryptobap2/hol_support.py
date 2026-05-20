from __future__ import annotations

import hashlib
import json
import shutil
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


def _hol_support_cache_key(*, holmake: Path, holba: Path) -> str:
    digest = hashlib.sha256()
    digest.update(b"cryptobap2-hol-support-v1\0")
    digest.update(str(CRYPTOBAP2_ROOT.resolve()).encode("utf-8") + b"\0")
    digest.update(str(holba.resolve()).encode("utf-8") + b"\0")
    digest.update(str(holmake.resolve()).encode("utf-8") + b"\0")
    for relative, source in _iter_hol_source_files():
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

    cache_root = layout.root.parent / HOL_SUPPORT_CACHE_DIRNAME / _hol_support_cache_key(
        holmake=holmake,
        holba=holba,
    )
    staged_root = cache_root / "src"
    staged_root.mkdir(parents=True, exist_ok=True)
    for relative, source in _iter_hol_source_files():
        target_dir = staged_root / relative.parent
        target_dir.mkdir(parents=True, exist_ok=True)
        _link_source_file(source, target_dir / source.name)
    _write_json(
        cache_root / "source-manifest.json",
        {
            "cache_key": cache_root.name,
            "cryptobap2_root": str(CRYPTOBAP2_ROOT.resolve()),
            "holba": str(holba.resolve()),
            "holmake": str(holmake.resolve()),
            "source_files": [str(relative) for relative, _source in _iter_hol_source_files()],
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
