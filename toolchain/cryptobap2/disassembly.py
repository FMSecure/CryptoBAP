from __future__ import annotations

import hashlib
import os
import re
import shutil
import subprocess
import tempfile
import urllib.request
import zipfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .config import CaseConfig
from .manifest import BuildLayout, ensure_layout, sha256_file, update_manifest
from .paths import CRYPTOBAP2_ROOT, DEFAULT_GHIDRA_HEADLESS, DEFAULT_OPT_DIR


DEFAULT_GHIDRA_VERSION = "12.0.4"
DEFAULT_GHIDRA_DATE = "20260303"
DEFAULT_GHIDRA_SHA256 = "c3b458661d69e26e203d739c0c82d143cc8a4a29d9e571f099c2cf4bda62a120"
GHIDRA_RELEASE_URL = (
    "https://github.com/NationalSecurityAgency/ghidra/releases/download/"
    "Ghidra_{version}_build/ghidra_{version}_PUBLIC_{date}.zip"
)
GHIDRA_SCRIPT = CRYPTOBAP2_ROOT / "scripts" / "ghidra" / "ExportObjdumpDa.java"


class DisassemblyError(RuntimeError):
    pass


@dataclass(frozen=True)
class GhidraInstall:
    version: str
    root: Path
    headless: Path


def ghidra_download_url(version: str = DEFAULT_GHIDRA_VERSION, *, url: str | None = None) -> str:
    if url:
        return url
    if version != DEFAULT_GHIDRA_VERSION:
        raise DisassemblyError("pass --url when installing a non-default Ghidra version")
    return GHIDRA_RELEASE_URL.format(version=version, date=DEFAULT_GHIDRA_DATE)


def known_ghidra_sha256(version: str) -> str | None:
    if version == DEFAULT_GHIDRA_VERSION:
        return DEFAULT_GHIDRA_SHA256
    return None


def _is_executable(path: Path) -> bool:
    return path.exists() and path.is_file() and os.access(path, os.X_OK)


def resolve_ghidra_headless(value: Path | None = None) -> Path | None:
    candidates: list[Path] = []
    if value is not None:
        path = value.expanduser()
        candidates.append(path / "support" / "analyzeHeadless" if path.is_dir() else path)
    elif DEFAULT_GHIDRA_HEADLESS is not None:
        candidates.append(DEFAULT_GHIDRA_HEADLESS)

    env_headless = os.environ.get("GHIDRA_HEADLESS")
    if env_headless:
        candidates.append(Path(env_headless).expanduser())
    env_home = os.environ.get("GHIDRA_HOME")
    if env_home:
        candidates.append(Path(env_home).expanduser() / "support" / "analyzeHeadless")
    on_path = shutil.which("analyzeHeadless")
    if on_path:
        candidates.append(Path(on_path))
    candidates.extend(sorted(DEFAULT_OPT_DIR.glob("ghidra_*/support/analyzeHeadless"), reverse=True))

    seen: set[Path] = set()
    for candidate in candidates:
        resolved = candidate.resolve()
        if resolved in seen:
            continue
        seen.add(resolved)
        if _is_executable(resolved):
            return resolved
    return None


def ghidra_status(value: Path | None = None) -> dict[str, object]:
    resolved = resolve_ghidra_headless(value)
    path = resolved or value or DEFAULT_GHIDRA_HEADLESS or DEFAULT_OPT_DIR / "ghidra_*/support/analyzeHeadless"
    return {
        "path": str(path),
        "exists": bool(resolved and resolved.exists()),
        "executable": bool(resolved and _is_executable(resolved)),
    }


def _java_major(java: Path) -> tuple[str | None, int | None]:
    result = subprocess.run(
        [str(java), "-version"],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    output = result.stdout.strip()
    version = output.splitlines()[0] if output else None
    match = re.search(r'version "([0-9]+)', output)
    return version, int(match.group(1)) if match else None


def _candidate_jdk_homes() -> list[Path]:
    candidates: list[Path] = []
    env_home = os.environ.get("JAVA_HOME")
    if env_home:
        candidates.append(Path(env_home).expanduser())
    javac = shutil.which("javac")
    if javac:
        candidates.append(Path(javac).resolve().parent.parent)
    candidates.extend(sorted(Path("/usr/lib/jvm").glob("*")))
    candidates.extend(sorted((CRYPTOBAP2_ROOT.parent / "Isabelle2025-2" / "contrib").glob("jdk-*/arm64-linux")))

    out: list[Path] = []
    seen: set[Path] = set()
    for candidate in candidates:
        resolved = candidate.resolve()
        if resolved in seen:
            continue
        seen.add(resolved)
        out.append(resolved)
    return out


def find_jdk_home(min_major: int = 21) -> Path | None:
    for home in _candidate_jdk_homes():
        java = home / "bin" / "java"
        javac = home / "bin" / "javac"
        if not (_is_executable(java) and _is_executable(javac)):
            continue
        _version, major = _java_major(java)
        if major is not None and major >= min_major:
            return home
    return None


def java_status() -> dict[str, object]:
    jdk_home = find_jdk_home()
    java = shutil.which("java")
    java_path = Path(java) if java else (jdk_home / "bin" / "java" if jdk_home else None)
    status: dict[str, object] = {
        "path": str(java_path) if java_path else "java",
        "home": str(jdk_home) if jdk_home else None,
        "javac": str(jdk_home / "bin" / "javac") if jdk_home else None,
        "exists": bool(java_path and java_path.exists()),
        "executable": bool(java_path and _is_executable(java_path)),
        "version": None,
        "major": None,
        "jdk": bool(jdk_home),
        "satisfies_ghidra": bool(jdk_home),
    }
    if not java_path or not _is_executable(java_path):
        return status
    version, major = _java_major(java_path)
    status["version"] = version
    status["major"] = major
    return status


def _sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _download(url: str, target: Path) -> None:
    target.parent.mkdir(parents=True, exist_ok=True)
    with urllib.request.urlopen(url) as response, target.open("wb") as handle:
        shutil.copyfileobj(response, handle)


def _assert_under_opt(path: Path, opt_dir: Path = DEFAULT_OPT_DIR) -> Path:
    resolved = path.resolve()
    opt = opt_dir.resolve()
    if opt not in {resolved, *resolved.parents}:
        raise DisassemblyError(f"Ghidra install path is outside {opt}: {path}")
    return resolved


def _safe_extract(zip_path: Path, target_dir: Path, *, opt_dir: Path = DEFAULT_OPT_DIR) -> Path:
    target = _assert_under_opt(target_dir, opt_dir)
    target.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(zip_path) as archive:
        for member in archive.infolist():
            member_path = target / member.filename
            resolved = member_path.resolve()
            if target not in {resolved, *resolved.parents}:
                raise DisassemblyError(f"unsafe path in Ghidra zip: {member.filename}")
        archive.extractall(target)
    children = [child for child in target.iterdir() if child.is_dir()]
    return children[0] if len(children) == 1 else target


def _patch_ghidra_jdk(root: Path, jdk_home: Path | None = None) -> None:
    jdk = jdk_home or find_jdk_home()
    properties = root / "support" / "launch.properties"
    if jdk is None or not properties.exists():
        return
    text = properties.read_text(encoding="utf-8")
    replacement = f"JAVA_HOME_OVERRIDE={jdk}"
    if re.search(r"(?m)^JAVA_HOME_OVERRIDE=.*$", text):
        text = re.sub(r"(?m)^JAVA_HOME_OVERRIDE=.*$", replacement, text, count=1)
    else:
        text = replacement + "\n" + text
    properties.write_text(text, encoding="utf-8")


def _finalize_ghidra_install(root: Path) -> None:
    for script in [root / "support" / "analyzeHeadless", root / "support" / "launch.sh", root / "ghidraRun"]:
        if script.exists():
            script.chmod(script.stat().st_mode | 0o111)
    _patch_ghidra_jdk(root)


def install_ghidra(
    *,
    version: str = DEFAULT_GHIDRA_VERSION,
    url: str | None = None,
    sha256: str | None = None,
    force: bool = False,
    opt_dir: Path = DEFAULT_OPT_DIR,
) -> GhidraInstall:
    opt = _assert_under_opt(opt_dir, opt_dir)
    opt.mkdir(parents=True, exist_ok=True)
    target = _assert_under_opt(opt / f"ghidra_{version}", opt)
    headless = target / "support" / "analyzeHeadless"
    if headless.exists() and not force:
        _finalize_ghidra_install(target)
        return GhidraInstall(version=version, root=target, headless=headless)
    if target.exists() and force:
        shutil.rmtree(target)

    download_url = ghidra_download_url(version, url=url)
    expected_sha = sha256 or known_ghidra_sha256(version)
    archive_path = opt / "downloads" / f"ghidra_{version}.zip"
    _download(download_url, archive_path)
    actual_sha = _sha256_path(archive_path)
    if expected_sha and actual_sha.lower() != expected_sha.lower():
        raise DisassemblyError(
            f"Ghidra archive SHA-256 mismatch: expected {expected_sha}, got {actual_sha}"
        )

    with tempfile.TemporaryDirectory(prefix=".ghidra-extract-", dir=str(opt)) as tmp:
        extracted = _safe_extract(archive_path, Path(tmp), opt_dir=opt)
        if target.exists():
            shutil.rmtree(target)
        shutil.move(str(extracted), str(target))

    if not headless.exists():
        raise DisassemblyError(f"installed Ghidra is missing analyzeHeadless: {headless}")
    _finalize_ghidra_install(target)
    return GhidraInstall(version=version, root=target, headless=headless)


def _sections_arg(sections: list[str] | None) -> str:
    selected = sections or [".text"]
    return ",".join(selected)


def validate_da(path: Path) -> list[dict[str, str]]:
    diagnostics: list[dict[str, str]] = []
    if not path.exists():
        return [{"severity": "error", "code": "missing_disassembly", "message": f"{path} does not exist"}]
    text = path.read_text(encoding="utf-8", errors="replace")
    if not text.strip():
        diagnostics.append({"severity": "error", "code": "empty_disassembly", "message": f"{path} is empty"})
    if "Disassembly of section" not in text:
        diagnostics.append(
            {"severity": "error", "code": "bad_disassembly", "message": "missing section header"}
        )
    if not re.search(r"(?m)^\s*[0-9A-Fa-f]+:\s+[0-9A-Fa-f ]+\s+\S+", text):
        diagnostics.append(
            {"severity": "error", "code": "bad_disassembly", "message": "missing instruction lines"}
        )
    return diagnostics


def validate_da_symbols(path: Path, symbols: list[str]) -> list[dict[str, str]]:
    if not path.exists():
        return []
    if symbols == ["*"]:
        return []
    text = path.read_text(encoding="utf-8", errors="replace")
    diagnostics: list[dict[str, str]] = []
    for symbol in symbols:
        pattern = r"(?m)^[0-9A-Fa-f]+\s+<" + re.escape(symbol) + r">:"
        if not re.search(pattern, text):
            diagnostics.append(
                {
                    "severity": "error",
                    "code": "missing_symbol",
                    "message": f"generated disassembly does not contain symbol {symbol!r}",
                }
            )
    return diagnostics


def run_ghidra_disassembly(
    binary: Path,
    output: Path,
    *,
    arch: str,
    ghidra: Path,
    sections: list[str] | None = None,
    log_path: Path | None = None,
) -> dict[str, Any]:
    if not binary.exists():
        raise DisassemblyError(f"binary does not exist: {binary}")
    if not _is_executable(ghidra):
        raise DisassemblyError(f"Ghidra analyzeHeadless not found or not executable: {ghidra}")
    if not GHIDRA_SCRIPT.exists():
        raise DisassemblyError(f"Ghidra export script is missing: {GHIDRA_SCRIPT}")

    output.parent.mkdir(parents=True, exist_ok=True)
    log_path = log_path or output.with_suffix(output.suffix + ".ghidra.log")
    log_path.parent.mkdir(parents=True, exist_ok=True)

    with tempfile.TemporaryDirectory(prefix="cryptobap2-ghidra-") as project_root:
        project_root_path = Path(project_root)
        ghidra_state = project_root_path / "state"
        ghidra_env = os.environ.copy()
        ghidra_env["HOME"] = str(ghidra_state / "home")
        ghidra_env["XDG_CONFIG_HOME"] = str(ghidra_state / "config")
        ghidra_env["XDG_CACHE_HOME"] = str(ghidra_state / "cache")
        ghidra_env["XDG_DATA_HOME"] = str(ghidra_state / "data")
        for state_dir in ("home", "config", "cache", "data"):
            (ghidra_state / state_dir).mkdir(parents=True, exist_ok=True)
        command = [
            str(ghidra),
            project_root,
            "cryptobap2",
            "-deleteProject",
            "-import",
            str(binary),
            "-scriptPath",
            str(GHIDRA_SCRIPT.parent),
            "-postScript",
            GHIDRA_SCRIPT.name,
            str(output),
            arch,
            _sections_arg(sections),
        ]
        result = subprocess.run(
            command,
            env=ghidra_env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
    log_path.write_text(result.stdout, encoding="utf-8")

    diagnostics = validate_da(output)
    if result.returncode != 0:
        diagnostics.append(
            {
                "severity": "error",
                "code": "ghidra_failed",
                "message": f"analyzeHeadless exited with {result.returncode}; see {log_path}",
            }
        )
    if any(item["severity"] == "error" for item in diagnostics):
        raise DisassemblyError(f"Ghidra disassembly failed; see {log_path}")

    return {
        "binary": binary,
        "output": output,
        "log": log_path,
        "ghidra": ghidra,
        "sections": sections or [".text"],
        "diagnostics": diagnostics,
        "exit_code": result.returncode,
    }


def prepare_case_disassembly(
    case: CaseConfig,
    layout: BuildLayout,
    *,
    ghidra: Path | None = None,
    install_missing: bool = False,
) -> CaseConfig:
    if case.input_binary is None:
        return case
    ensure_layout(layout)
    binary = case.input_binary
    output = layout.bir / f"{case.name}.da"
    log_path = layout.logs / "ghidra-disassemble.log"
    sections = case.disassembly_sections
    headless = resolve_ghidra_headless(ghidra)
    if headless is None and install_missing:
        headless = install_ghidra().headless
    if headless is None:
        diagnostics = [
            {
                "severity": "warning",
                "code": "missing_ghidra",
                "message": "Ghidra is unavailable; using existing input.da fallback",
            }
        ]
        stage_data = {
            "status": "missing" if case.input_da and case.input_da.exists() else "validation_failed",
            "binary": str(binary),
            "fallback_da": str(case.input_da) if case.input_da else None,
            "diagnostics": diagnostics,
        }
        update_manifest(case, layout, command="disassemble", stage="disassemble", stage_data=stage_data)
        if case.input_da and case.input_da.exists():
            return case
        raise DisassemblyError("Ghidra is unavailable and the case has no existing input.da fallback")

    result = run_ghidra_disassembly(
        binary,
        output,
        arch=case.arch,
        ghidra=headless,
        sections=sections,
        log_path=log_path,
    )
    diagnostics = [*result["diagnostics"], *validate_da_symbols(output, case.symbols)]
    stage_data = {
        "status": "validation_failed" if diagnostics else "generated_unchecked",
        "binary": str(binary),
        "binary_sha256": sha256_file(binary),
        "output_da": str(output),
        "output_sha256": sha256_file(output),
        "ghidra": str(headless),
        "sections": sections,
        "exit_code": result["exit_code"],
        "log": str(log_path),
        "diagnostics": diagnostics,
    }
    update_manifest(
        case,
        layout,
        command="disassemble",
        stage="disassemble",
        stage_data=stage_data,
        artifacts={"disassembled_da": output, "disassemble_log": log_path},
    )
    if any(item["severity"] == "error" for item in diagnostics):
        raise DisassemblyError(f"Ghidra disassembly is missing requested symbols; see {log_path}")
    return case.with_input_da(output)
