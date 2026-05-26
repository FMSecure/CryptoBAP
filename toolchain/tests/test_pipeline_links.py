from __future__ import annotations

import hashlib
import json
import os
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "toolchain"))

from cryptobap2.checks import Finding, check_failed
from cryptobap2.binary_model import BINARY_MODEL_SCHEMA, finalize_binary_model
from cryptobap2 import hol_support
from cryptobap2.config import CaseConfig, load_yaml_subset
from cryptobap2.disassembly import DisassemblyError, run_ghidra_disassembly, validate_da
from cryptobap2.hol_support import _holba_dependency_hash
from cryptobap2.manifest import BuildLayout, layout_for_case, load_manifest
from cryptobap2.paths import (
    CRYPTOBAP2_ROOT,
    default_holba_dir,
    default_holmake,
    default_squirrel,
    default_tamarin,
    resolve_config_path,
)
from cryptobap2.sapic_format import format_sapic_text
from cryptobap2.schema import validate_case_schema
from cryptobap2.squirrel_backend import (
    BackendError,
    export_squirrel,
    stage_spthy,
    validate_backend_outputs,
    validate_tamarin_spthy,
)
from cryptobap2.templates import CASE_TEMPLATES
from cryptobap2.stages import (
    StageError,
    _holmakefile_content,
    _render_sml_template,
    lift_stage_is_current,
    run_lift_stage,
    run_symexec_stage,
    stage_hol_sources,
    validate_fragment_labels,
)


def _executable(path: Path, text: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    path.chmod(path.stat().st_mode | stat.S_IXUSR)
    return path


def _require_fixture(path: Path) -> None:
    if path.exists():
        return
    try:
        display = path.relative_to(ROOT)
    except ValueError:
        display = path
    raise unittest.SkipTest(f"fixture is not available: {display}")


class CryptoBAP2PipelineLinkTests(unittest.TestCase):
    def test_cryptobap2_does_not_vendor_holba_files(self) -> None:
        holba = os.environ.get("HOLBA_DIR") or os.environ.get("HOLBADIR")
        if not holba:
            self.skipTest("HOLBA_DIR/HOLBADIR is not set")
        holba_src = Path(holba).expanduser().resolve() / "src"
        if not holba_src.exists():
            self.skipTest("configured HolBA source checkout is not available")

        copied_suffixes = {".sml", ".sig", ".da", ".mem", ".plus", ".txt"}

        holba_hashes: set[str] = set()
        for path in holba_src.rglob("*"):
            if not path.is_file() or path.suffix not in copied_suffixes:
                continue
            if ".hol" in path.parts or "build" in path.parts:
                continue
            if path.name.endswith("Theory.txt"):
                continue
            holba_hashes.add(hashlib.sha256(path.read_bytes()).hexdigest())

        duplicates: list[str] = []
        for root in (ROOT / "src", ROOT / "examples", ROOT / "tests", ROOT / "docs"):
            for path in root.rglob("*"):
                if not path.is_file() or path.suffix not in copied_suffixes:
                    continue
                if ".hol" in path.parts or "build" in path.parts:
                    continue
                if path.name.endswith("Theory.txt"):
                    continue
                if hashlib.sha256(path.read_bytes()).hexdigest() in holba_hashes:
                    duplicates.append(str(path.relative_to(ROOT)))

        self.assertEqual([], duplicates)

    def test_examples_do_not_use_removed_holba_driver_libraries(self) -> None:
        forbidden = (
            "binariesCfgLib",
            "binariesMemLib",
            "bir_cfg_m0Lib",
            "bir_symbexec_driverLib",
            "bir_symbexec_loopLib",
        )
        offenders: list[str] = []
        for path in (ROOT / "examples").rglob("*.sml"):
            if ".hol" in path.parts or "build" in path.parts:
                continue
            text = path.read_text(encoding="utf-8")
            for token in forbidden:
                if token in text:
                    offenders.append(f"{path.relative_to(ROOT)}: {token}")

        self.assertEqual([], offenders)

    def test_finalize_binary_model_synthesizes_call_stub_for_zero_sapic_fragment(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            da = root / "sample.da"
            da.write_text(
                """
0000000000001000 <main>:
  1004:\t94000000 \tbl 2000 <message_decrypt>
""",
                encoding="utf-8",
            )
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"da": str(da), "symbols": ["main"]},
                    "execution": {
                        "fragments": [
                            {"name": "decrypt", "entry_label": 0x1000, "end_label": 0x1008, "exit_labels": [0x1008]}
                        ]
                    },
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            layout.model.mkdir(parents=True)
            layout.sapic.mkdir(parents=True)
            sapic = layout.sapic / "sample.sapic"
            model = layout.model / "sample.binary-model.json"
            sapic.write_text("", encoding="utf-8")
            model.write_text(
                json.dumps(
                    {
                        "schema": BINARY_MODEL_SCHEMA,
                        "case": {"name": "sample"},
                        "fragments": [
                            {
                                "name": "decrypt",
                                "entry_label": 0x1000,
                                "exit_labels": [0x1008],
                                "total_states": 1,
                                "assertion_clean_states": 1,
                                "path_predicates": [],
                                "symbolic_values": [],
                                "sapic": "0",
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )

            diagnostics, metadata = finalize_binary_model(case, layout, model_path=model, sapic_path=sapic)
            sapic_text = sapic.read_text(encoding="utf-8")
            data = json.loads(model.read_text(encoding="utf-8"))

        self.assertEqual([], diagnostics)
        self.assertEqual(1, metadata["model_fragment_count"])
        self.assertIn("(out(Channel,4100_C_Lib))", sapic_text)
        self.assertEqual("(out(Channel,4100_C_Lib))", data["fragments"][0]["sapic"])
        self.assertTrue(data["fragments"][0]["sapic_synthesized"])
        self.assertEqual(1, data["translation_notes"]["synthesized_sapic_call_stubs"])

    def test_tree_to_process_keeps_casted_assignments_for_sapic(self) -> None:
        text = (ROOT / "src" / "pretty_print" / "tree_to_processLib.sml").read_text(encoding="utf-8")
        self.assertNotIn("(is_BExp_Cast b) orelse", text)
        self.assertIn("else if ((is_BExp_Load b) orelse (is_BExp_Store b))", text)
        self.assertIn("if identical be pred_be then be", text)
        self.assertIn("fun configured_channel ()", text)
        self.assertNotIn("mk_ChOut (mk_none", text)
        self.assertNotIn("mk_ChIn (mk_none", text)

    def test_c_lib_calls_are_observable_in_generated_sapic(self) -> None:
        func_text = (ROOT / "src" / "pipeline_support" / "bir_symbexec_funcLib.sml").read_text(encoding="utf-8")
        step_text = (ROOT / "src" / "pipeline_support" / "bir_symbexec_stepLib.sml").read_text(encoding="utf-8")

        self.assertIn("fun C_Lib syst", func_text)
        self.assertIn('state_add_path "Kr"', func_text)
        self.assertIn('lib_type = "C_Lib"', step_text)
        self.assertIn("lookup_block_dict bl_dict lbl_tm", step_text)
        self.assertIn("bir_symbexec_funcLib.C_Lib syst", step_text)
        self.assertIn("bir_symbexec_funcLib.update_pc syst", step_text)

    def test_indirect_jump_resolution_is_reachable(self) -> None:
        text = (ROOT / "src" / "pipeline_support" / "bir_symbexec_stepLib.sml").read_text(encoding="utf-8")
        self.assertNotIn("else raise state_exec_try_jmp_exp_var_exn;", text)
        self.assertIn("else ();", text)
        self.assertIn("val be_tgt  = (fst o hd) vs;", text)

    def test_sapic_pretty_printer_keeps_process_brackets(self) -> None:
        text = (ROOT / "src" / "pretty_print" / "sapic_to_fileLib.sml").read_text(encoding="utf-8")

        self.assertIn('fun bracket text = "(" ^ text ^ ")"', text)
        self.assertIn("else bracket (process_body_to_string pro)", text)
        self.assertIn('then (process_to_string pl)^"\\n"^(combinator_to_string c)^"\\n"^(process_to_string pr)', text)
        self.assertIn('^"\\nelse\\n"^', text)
        self.assertNotIn('" then "', text)
        self.assertNotIn('^" in "', text)
        self.assertNotIn('then "("^(process_to_string pl)^")"', text)

    def test_checked_in_nordvpnd_example_preserves_translated_branches(self) -> None:
        sapic = ROOT / "examples" / "nordvpnd" / "build" / "nordvpnd-nordlynx" / "sapic" / "nordvpnd-nordlynx.sapic"
        squirrel = ROOT / "examples" / "nordvpnd" / "build" / "nordvpnd-nordlynx" / "squirrel" / "nordvpnd-nordlynx.sp"
        _require_fixture(sapic)
        _require_fixture(squirrel)
        sapic_text = sapic.read_text(encoding="utf-8")
        text = squirrel.read_text(encoding="utf-8")

        self.assertTrue(sapic_text.startswith("(let "))
        self.assertNotRegex(sapic_text, r"(?m)^\s*(?:let |out\(|in\()")
        self.assertNotIn(" in \n", sapic_text)
        self.assertNotIn(" then \n", sapic_text)
        self.assertNotIn(")+(", sapic_text)
        self.assertNotIn(")|(", sapic_text)
        self.assertIn("if SignedLessThan(89_C_Lib,'0') = '1' then", sapic_text)
        self.assertIn("\n                        else\n", sapic_text)
        self.assertIn("abstract Load : message * message * message * message -> message.", text)
        self.assertIn("abstract Plus : message * message -> message.", text)
        self.assertIn("if choice_0_2 = schoice_left_0 then", text)
        self.assertGreaterEqual(text.count("_C_Lib)"), 2)

    def test_lift_holmakefile_imports_only_holba_sources(self) -> None:
        layout = BuildLayout(
            root=Path("relative-build") / "sample",
            work=Path("relative-build") / "sample" / "work",
            bir=Path("relative-build") / "sample" / "bir",
            tree=Path("relative-build") / "sample" / "tree",
            sapic=Path("relative-build") / "sample" / "sapic",
            spthy=Path("relative-build") / "sample" / "spthy",
            squirrel=Path("relative-build") / "sample" / "squirrel",
            logs=Path("relative-build") / "sample" / "logs",
        )
        content = _holmakefile_content(layout)
        self.assertNotIn("CRYPTOBAP2_SRC", content)
        self.assertNotIn("$(CRYPTOBAP2_SRC)/pipeline_support", content)
        self.assertIn("$(HOLBA_ROOT)/src/theory/tools/lifter", content)

    def test_lift_runner_uses_disassembly_section_range(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            da = root / "sample.da"
            da.write_text(
                "\nfake:     file format elf64-littleaarch64\n\n\nDisassembly of section .text:\n\n0000000100000000 <main>:\n  100000000:\td503201f \tnop\n",
                encoding="utf-8",
            )
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"da": str(da), "theory": "Sample", "symbols": ["main"]},
                    "execution": {"entry_label": 0x100000000, "exit_labels": []},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            result = run_lift_stage(case, layout, execute=False)
            text = result["runner"].read_text(encoding="utf-8")

        self.assertIn("val prog_range = da_sections_minmax sections;", text)
        self.assertNotIn("0xffffffff", text)

    def test_symexec_holmakefile_uses_shared_source_cache(self) -> None:
        layout = BuildLayout(
            root=Path("relative-build") / "sample",
            work=Path("relative-build") / "sample" / "work",
            bir=Path("relative-build") / "sample" / "bir",
            tree=Path("relative-build") / "sample" / "tree",
            sapic=Path("relative-build") / "sample" / "sapic",
            spthy=Path("relative-build") / "sample" / "spthy",
            squirrel=Path("relative-build") / "sample" / "squirrel",
            logs=Path("relative-build") / "sample" / "logs",
        )
        source_root = layout.root.parent / "_cryptobap2-support-cache" / "key" / "src"
        content = _holmakefile_content(layout, source_root)
        self.assertIn(f"CRYPTOBAP2_SRC = {source_root.resolve()}", content)
        self.assertIn("$(CRYPTOBAP2_SRC)/pipeline_support", content)
        self.assertNotIn("CRYPTOBAP2_HOL_SRC", content)

    def test_hol_sources_are_cached_without_legacy_case_source_dirs(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            layout = BuildLayout(
                root=root / "sample",
                work=root / "sample" / "work",
                bir=root / "sample" / "bir",
                tree=root / "sample" / "tree",
                sapic=root / "sample" / "sapic",
                spthy=root / "sample" / "spthy",
                squirrel=root / "sample" / "squirrel",
                logs=root / "sample" / "logs",
            )
            legacy = layout.work / "src"
            legacy.mkdir(parents=True)
            (legacy / ".hol").mkdir()
            source_root = stage_hol_sources(layout)
            self.assertTrue(source_root.is_dir())
            self.assertIn("_cryptobap2-support-cache", source_root.parts)
            self.assertFalse((layout.work / "src").exists())
            self.assertFalse((layout.root / "hol").exists())
            self.assertFalse((layout.root / "hol-src").exists())

            forbidden = [
                "pipeline_support/binariesCfgLib.sml",
                "pipeline_support/binariesMemLib.sml",
                "translate_to_sapic/symb_interpretScript.sml",
                "pipeline_support/binariesScript.sml",
                "pipeline_support/bir_cfg_m0Lib.sml",
                "pipeline_support/bir_exp_to_wordsLib.sml",
                "pipeline_support/bir_symbexec_loopLib.sml",
                "pipeline_support/bir_smtLib.sml",
                "pipeline_support/Z3_SAT_modelLib.sml",
            ]
            for relative in forbidden:
                self.assertFalse((source_root / relative).exists(), relative)

            preprocess = source_root / "pipeline_support" / "bir_symbexec_PreprocessLib.sml"
            self.assertNotIn("open binariesTheory", preprocess.read_text(encoding="utf-8"))
            state = source_root / "pipeline_support" / "bir_symbexec_stateLib.sml"
            self.assertTrue(state.is_symlink())
            self.assertNotIn("fallback_holba_root", state.read_text(encoding="utf-8"))

            marker = source_root / "pipeline_support" / ".hol" / "objs" / "cached.ui"
            marker.parent.mkdir(parents=True)
            marker.write_text("cached", encoding="utf-8")
            self.assertEqual(source_root, stage_hol_sources(layout))
            self.assertTrue(marker.exists())

    def test_hol_source_cache_changes_when_holba_sources_change(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            holba = root / "HolBA"
            dependency = holba / "src" / "tools" / "exec" / "Dependency.sml"
            dependency.parent.mkdir(parents=True)
            dependency.write_text("val dependency_version = 1\n", encoding="utf-8")
            holmake = _executable(root / "Holmake", "#!/bin/sh\n")
            layout = BuildLayout(
                root=root / "sample",
                work=root / "sample" / "work",
                bir=root / "sample" / "bir",
                tree=root / "sample" / "tree",
                sapic=root / "sample" / "sapic",
                spthy=root / "sample" / "spthy",
                squirrel=root / "sample" / "squirrel",
                logs=root / "sample" / "logs",
            )

            first = stage_hol_sources(layout, holmake=holmake, holba=holba)
            dependency.write_text("val dependency_version = 2\n", encoding="utf-8")
            second = stage_hol_sources(layout, holmake=holmake, holba=holba)

        self.assertNotEqual(first, second)

    def test_holba_git_hash_changes_when_dependency_sources_are_dirty(self) -> None:
        if shutil.which("git") is None:
            self.skipTest("git is not available")
        with tempfile.TemporaryDirectory() as tmp:
            holba = Path(tmp) / "HolBA"
            dependency = holba / "src" / "tools" / "exec" / "Dependency.sml"
            dependency.parent.mkdir(parents=True)
            dependency.write_text("val dependency_version = 1\n", encoding="utf-8")
            subprocess.run(["git", "init"], cwd=holba, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            subprocess.run(
                ["git", "add", "src/tools/exec/Dependency.sml"],
                cwd=holba,
                check=True,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )

            indexed_hash = _holba_dependency_hash(holba)
            dependency.write_text("val dependency_version = 2\n", encoding="utf-8")
            dirty_hash = _holba_dependency_hash(holba)
            dependency.write_text("val dependency_version = 3\n", encoding="utf-8")
            dirtier_hash = _holba_dependency_hash(holba)

        self.assertNotEqual(indexed_hash, dirty_hash)
        self.assertNotEqual(dirty_hash, dirtier_hash)

    def test_holba_git_hash_falls_back_to_file_content_when_status_unavailable(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            holba = Path(tmp) / "HolBA"
            (holba / ".git").mkdir(parents=True)
            dependency = holba / "src" / "tools" / "exec" / "Dependency.sml"
            dependency.parent.mkdir(parents=True)
            dependency.write_text("val dependency_version = 1\n", encoding="utf-8")

            with mock.patch.object(hol_support, "_git_dependency_status", return_value=None):
                first = _holba_dependency_hash(holba)
                dependency.write_text("val dependency_version = 2\n", encoding="utf-8")
                second = _holba_dependency_hash(holba)

        self.assertNotEqual(first, second)

    def test_dependency_defaults_use_environment_not_repo_local_paths(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            env = {
                "HOLBA_DIR": str(root / "HolBA"),
                "HOLMAKE": str(root / "bin" / "Holmake"),
                "TAMARIN": str(root / "bin" / "tamarin-prover"),
                "SQUIRREL": str(root / "bin" / "squirrel"),
            }
            with mock.patch.dict(os.environ, env, clear=True):
                self.assertEqual(default_holba_dir(), (root / "HolBA").resolve())
                self.assertEqual(default_holmake(), (root / "bin" / "Holmake").resolve())
                self.assertEqual(default_tamarin(), (root / "bin" / "tamarin-prover").resolve())
                self.assertEqual(default_squirrel(), (root / "bin" / "squirrel").resolve())

            path_bin = root / "repo-local-bin"
            _executable(path_bin / "Holmake", "#!/bin/sh\n")
            _executable(path_bin / "tamarin-prover", "#!/bin/sh\n")
            _executable(path_bin / "squirrel", "#!/bin/sh\n")

            with mock.patch.dict(os.environ, {"PATH": str(path_bin)}, clear=True):
                self.assertEqual(str(default_holba_dir()), "<missing:HOLBA_DIR|HOLBADIR>")
                self.assertEqual(str(default_holmake()), "<missing:HOLMAKE>")
                self.assertEqual(str(default_tamarin()), "<missing:TAMARIN>")
                self.assertEqual(str(default_squirrel()), "<missing:SQUIRREL>")

    def test_config_path_resolution_expands_home_without_claiming_root_containment(self) -> None:
        with mock.patch.dict(os.environ, {"HOME": "/tmp/cryptobap2-home"}, clear=False):
            self.assertEqual(resolve_config_path("~/case.yaml"), Path("/tmp/cryptobap2-home/case.yaml"))
        self.assertEqual(resolve_config_path("../outside.yaml"), CRYPTOBAP2_ROOT.parent / "outside.yaml")

    def test_case_config_paths_are_relative_to_case_file(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            case_dir = root / "cases"
            case_dir.mkdir()
            da = case_dir / "sample.da"
            source = case_dir / "source.spthy"
            da.write_text("sample disassembly\n", encoding="utf-8")
            source.write_text("theory sample\nbegin\nend\n", encoding="utf-8")
            case = CaseConfig(
                path=case_dir / "sample.yaml",
                raw={
                    "name": "sample",
                    "input": {"da": "sample.da"},
                    "execution": {"entry_label": 1, "exit_labels": [2]},
                    "artifacts": {"tamarin_source": "source.spthy"},
                },
            )
            self.assertEqual(case.input_da, da.resolve())
            self.assertEqual(case.artifacts["tamarin_source"], source.resolve())

        repo_case = CaseConfig(
            path=CRYPTOBAP2_ROOT / "cases" / "sample.yaml",
            raw={"name": "sample", "input": {"da": "xor.yaml"}},
        )
        self.assertEqual(repo_case.input_da, (CRYPTOBAP2_ROOT / "xor.yaml").resolve())

    def test_binary_to_da_with_fake_ghidra(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            ghidra = _executable(
                root / "analyzeHeadless",
                """#!/usr/bin/env python3
import pathlib
import sys
idx = sys.argv.index("-postScript")
out = pathlib.Path(sys.argv[idx + 2])
out.write_text("\\nfake:     file format elf64-littleaarch64\\n\\n\\nDisassembly of section .text:\\n\\n0000000000000000 <main>:\\n   0:\\td503201f \\tnop\\n", encoding="utf-8")
""",
            )
            binary = root / "sample.elf"
            binary.write_bytes(b"\x00\x01\x02\x03")
            output = root / "sample.da"
            run_ghidra_disassembly(binary, output, arch="arm8", ghidra=ghidra)
            self.assertEqual(validate_da(output), [])

    def test_ghidra_export_does_not_accept_stale_da_output(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            ghidra = _executable(root / "analyzeHeadless", "#!/usr/bin/env python3\nraise SystemExit(0)\n")
            binary = root / "sample.elf"
            binary.write_bytes(b"\x00\x01\x02\x03")
            output = root / "sample.da"
            output.write_text(
                "\nfake:     file format elf64-littleaarch64\n\n\n"
                "Disassembly of section .text:\n\n0000000000000000 <old>:\n   0:\td503201f \tnop\n",
                encoding="utf-8",
            )

            with self.assertRaises(DisassemblyError):
                run_ghidra_disassembly(binary, output, arch="arm8", ghidra=ghidra)

            self.assertIn("<old>", output.read_text(encoding="utf-8"))

    def test_da_validation_rejects_empty_output(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            da = Path(tmp) / "empty.da"
            da.write_text("", encoding="utf-8")
            diagnostics = validate_da(da)
        self.assertEqual([item["code"] for item in diagnostics], ["empty_disassembly", "bad_disassembly", "bad_disassembly"])

    def test_lift_stage_records_label_metadata_from_hol_output(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            da = root / "sample.da"
            da.write_text(
                "\nfake:     file format elf64-littleaarch64\n\n\nDisassembly of section .text:\n\n000000000000003c <main>:\n  3c:\td503201f \tnop\n",
                encoding="utf-8",
            )
            holmake = _executable(
                root / "Holmake",
                """#!/usr/bin/env python3
import pathlib
import re
import sys
target = sys.argv[1] if len(sys.argv) > 1 else ""
objs = pathlib.Path(".hol/objs")
objs.mkdir(parents=True, exist_ok=True)
if target:
    (objs / target).write_text("uo", encoding="utf-8")
script = next(pathlib.Path.cwd().glob("*Script.sml"))
match = re.search(r'TextIO.openOut "([^"]+)"', script.read_text())
pathlib.Path(match.group(1)).write_text("BL_Address (Imm64 60w) BL_Address (Imm64 132w)", encoding="utf-8")
""",
            )
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"da": str(da), "theory": "Sample", "symbols": ["main"]},
                    "execution": {"entry_label": 60, "exit_labels": [132]},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            run_lift_stage(case, layout, holmake=holmake, holba=root)
            manifest = load_manifest(layout.manifest_path)
            self.assertEqual(manifest["stages"]["lift"]["label_count"], 2)
            self.assertIsNone(manifest["stages"]["lift"]["hol_source_root"])
            self.assertFalse((layout.work / "src").exists())
            self.assertEqual(validate_fragment_labels(case, layout), [])
            self.assertTrue(lift_stage_is_current(case, layout, holmake=holmake, holba=root))

            (layout.bir / "lifted-labels.json").unlink()
            self.assertFalse(lift_stage_is_current(case, layout, holmake=holmake, holba=root))
            diagnostics = validate_fragment_labels(case, layout, require_metadata=True)

        self.assertEqual([item["code"] for item in diagnostics], ["missing_lifted_label_metadata"])
        self.assertEqual([item["severity"] for item in diagnostics], ["error"])

    def test_lift_stage_does_not_accept_stale_label_dump(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            da = root / "sample.da"
            da.write_text(
                "\nfake:     file format elf64-littleaarch64\n\n\n"
                "Disassembly of section .text:\n\n000000000000003c <main>:\n  3c:\td503201f \tnop\n",
                encoding="utf-8",
            )
            holmake = _executable(
                root / "Holmake",
                """#!/usr/bin/env python3
import pathlib
import sys
target = sys.argv[1] if len(sys.argv) > 1 else ""
objs = pathlib.Path(".hol/objs")
objs.mkdir(parents=True, exist_ok=True)
if target:
    (objs / target).write_text("uo", encoding="utf-8")
""",
            )
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"da": str(da), "theory": "Sample", "symbols": ["main"]},
                    "execution": {"entry_label": 60, "exit_labels": []},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            stale_label_dump = layout.bir / "lifted-program-labels.txt"
            stale_label_dump.parent.mkdir(parents=True)
            stale_label_dump.write_text("BL_Address (Imm64 999w)", encoding="utf-8")

            with self.assertRaises(StageError):
                run_lift_stage(case, layout, holmake=holmake, holba=root)

            manifest = load_manifest(layout.manifest_path)

        self.assertEqual(manifest["stages"]["lift"]["status"], "validation_failed")
        self.assertEqual(manifest["stages"]["lift"]["diagnostics"][0]["code"], "missing_label_dump")
        self.assertFalse(manifest["artifacts"]["lifted_label_dump"]["exists"])

    def test_lift_stage_rejects_success_without_theory_object(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            da = root / "sample.da"
            da.write_text(
                "\nfake:     file format elf64-littleaarch64\n\n\nDisassembly of section .text:\n\n000000000000003c <main>:\n  3c:\td503201f \tnop\n",
                encoding="utf-8",
            )
            holmake = _executable(
                root / "Holmake",
                """#!/usr/bin/env python3
import pathlib
import re
script = next(pathlib.Path.cwd().glob("*Script.sml"))
match = re.search(r'TextIO.openOut "([^"]+)"', script.read_text())
pathlib.Path(match.group(1)).write_text("BL_Address (Imm64 60w)", encoding="utf-8")
""",
            )
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"da": str(da), "theory": "Sample", "symbols": ["main"]},
                    "execution": {"entry_label": 60, "exit_labels": []},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            with self.assertRaises(StageError):
                run_lift_stage(case, layout, holmake=holmake, holba=root)
            manifest = load_manifest(layout.manifest_path)
        self.assertEqual(manifest["stages"]["lift"]["status"], "validation_failed")
        self.assertFalse(manifest["artifacts"]["lifted_theory_uo"]["exists"])

    def test_lift_runner_supports_wildcard_symbols_and_sections(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            da = root / "sample.da"
            da.write_text(
                "\nfake:     file format elf64-littleaarch64\n\n\nDisassembly of section .text:\n\n000000000000003c <main>:\n  3c:\td503201f \tnop\n",
                encoding="utf-8",
            )
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "channel": "private_chan",
                    "input": {
                        "da": str(da),
                        "theory": "Sample",
                        "symbols": ["*"],
                        "disassembly": {"sections": [".text", ".init"]},
                    },
                    "execution": {"entry_label": 60, "exit_labels": [132]},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            result = run_lift_stage(case, layout, execute=False)
            text = result["runner"].read_text(encoding="utf-8")

        self.assertIn('val lift_all_symbols = true;', text)
        self.assertIn('".text"', text)
        self.assertIn('".init"', text)
        self.assertIn("lift_all_symbols orelse list_has symbname symbs_sec_text", text)

    def test_label_validation_reports_bad_exit_label(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"da": str(root / "sample.da"), "symbols": ["main"]},
                    "execution": {"entry_label": 60, "exit_labels": [999]},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            layout.bir.mkdir(parents=True)
            (layout.bir / "lifted-labels.json").write_text(
                '{"labels": [60, 132], "source": "fake", "source_sha256": "fake"}\n',
                encoding="utf-8",
            )
            diagnostics = validate_fragment_labels(case, layout)
        self.assertEqual([item["code"] for item in diagnostics], ["bad_label"])

    def test_symexec_stage_rejects_bad_label_metadata_before_holmake(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            marker = root / "holmake-called"
            holmake = _executable(
                root / "Holmake",
                f"""#!/usr/bin/env python3
import pathlib
pathlib.Path({str(marker)!r}).write_text("called", encoding="utf-8")
raise SystemExit(99)
""",
            )
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"da": str(root / "sample.da"), "theory": "Sample", "symbols": ["main"]},
                    "execution": {"entry_label": 60, "exit_labels": [132]},
                    "backends": ["squirrel"],
                },
            )
            (root / "sample.da").write_text(
                "\nfake:     file format elf64-littleaarch64\n\n\nDisassembly of section .text:\n\n000000000000003c <main>:\n  3c:\td503201f \tnop\n",
                encoding="utf-8",
            )
            layout = layout_for_case(case, root / "build")
            layout.bir.mkdir(parents=True)
            (layout.bir / "lifted-labels.json").write_text('{"labels": [60]}\n', encoding="utf-8")

            with self.assertRaises(StageError):
                run_symexec_stage(case, layout, holmake=holmake, holba=root)
            manifest = load_manifest(layout.manifest_path)

        self.assertFalse(marker.exists())
        self.assertEqual(manifest["stages"]["symexec"]["status"], "validation_failed")
        diagnostics = manifest["stages"]["symexec"]["diagnostics"]
        self.assertIn("bad_label", [item["code"] for item in diagnostics])

    def test_symexec_stage_writes_generated_sapic_without_fallback(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            holmake = _executable(
                root / "Holmake",
                """#!/usr/bin/env python3
import json
import pathlib
import re
import sys
target = sys.argv[1] if len(sys.argv) > 1 else ""
objs = pathlib.Path(".hol/objs")
objs.mkdir(parents=True, exist_ok=True)
if target:
    (objs / target).write_text("uo", encoding="utf-8")
script = next(pathlib.Path.cwd().glob("CryptoBAP2Symexec_*Script.sml"))
text = script.read_text()
sapic = re.search(r'write_sapic_text\\s*\\("([^"]+)"', text).group(1)
model = re.search(r'write_binary_model_text\\s*\\("([^"]+)"', text).group(1)
pathlib.Path(sapic).write_text("out(Channel,msg)", encoding="utf-8")
pathlib.Path(model).write_text(json.dumps({
    "schema": "cryptobap2-binary-model-v1",
    "case": {"name": "sample"},
    "fragments": [{
        "name": "main",
        "entry_label": 60,
        "exit_labels": [132],
        "total_states": 1,
        "assertion_clean_states": 1,
        "path_predicates": [["init_pred"]],
        "symbolic_values": [],
        "sapic": "out(Channel,msg)"
    }]
}), encoding="utf-8")
""",
            )
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"da": str(root / "sample.da"), "theory": "Sample", "symbols": ["main"]},
                    "execution": {"entry_label": 60, "exit_labels": [132]},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            layout.bir.mkdir(parents=True)
            (layout.bir / "lifted-labels.json").write_text('{"labels": [60, 132]}\n', encoding="utf-8")
            run_symexec_stage(case, layout, holmake=holmake, holba=root)
            manifest = load_manifest(layout.manifest_path)
            self.assertEqual(manifest["stages"]["symexec"]["status"], "generated_unchecked")
            self.assertTrue((layout.sapic / "sample.sapic").exists())
            model = layout.model / "sample.binary-model.json"
            self.assertTrue(model.exists())
            self.assertEqual(json.loads(model.read_text(encoding="utf-8"))["schema"], BINARY_MODEL_SCHEMA)
            self.assertTrue(manifest["artifacts"]["binary_model"]["exists"])
            self.assertEqual(manifest["stages"]["symexec"]["model_fragment_count"], 1)
            self.assertNotIn("fallback_sapic_source", manifest["stages"]["symexec"])

    def test_symexec_stage_flags_null_sapic_as_unfaithful(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            holmake = _executable(
                root / "Holmake",
                f"""#!/usr/bin/env python3
import json
import pathlib
import re
import sys
target = sys.argv[1] if len(sys.argv) > 1 else ""
objs = pathlib.Path(".hol/objs")
objs.mkdir(parents=True, exist_ok=True)
if target:
    (objs / target).write_text("uo", encoding="utf-8")
script = next(pathlib.Path.cwd().glob("CryptoBAP2Symexec_*Script.sml"))
text = script.read_text()
sapic = re.search(r'write_sapic_text\\s*\\("([^"]+)"', text).group(1)
model = re.search(r'write_binary_model_text\\s*\\("([^"]+)"', text).group(1)
pathlib.Path(sapic).write_text("0", encoding="utf-8")
pathlib.Path(model).write_text(json.dumps({{
    "schema": "{BINARY_MODEL_SCHEMA}",
    "case": {{"name": "sample"}},
    "fragments": [{{
        "name": "main",
        "entry_label": 60,
        "exit_labels": [132],
        "total_states": 1,
        "assertion_clean_states": 1,
        "path_predicates": [["init_pred"]],
        "symbolic_values": [],
        "sapic": "0"
    }}]
}}), encoding="utf-8")
""",
            )
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"da": str(root / "sample.da"), "theory": "Sample", "symbols": ["main"]},
                    "execution": {"entry_label": 60, "exit_labels": [132]},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            layout.bir.mkdir(parents=True)
            (layout.bir / "lifted-labels.json").write_text('{"labels": [60, 132]}\n', encoding="utf-8")
            run_symexec_stage(case, layout, holmake=holmake, holba=root)
            manifest = load_manifest(layout.manifest_path)
            diagnostics = manifest["stages"]["symexec"]["diagnostics"]
            coverage = manifest["stages"]["symexec"]["translation_coverage"]
        self.assertEqual(manifest["stages"]["symexec"]["status"], "validation_failed")
        self.assertIn("sapic_null_process", [item["code"] for item in diagnostics])
        self.assertEqual(coverage["sapic_line_count"], 1)

    def test_symexec_runner_contains_binary_model_writer(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"da": str(root / "sample.da"), "theory": "Sample", "symbols": ["main"]},
                    "execution": {"entry_label": 60, "exit_labels": [132]},
                    "functions": {"library": [], "adversary": [], "crypto": {}},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            result = run_symexec_stage(case, layout, execute=False)
            text = result["runner"].read_text(encoding="utf-8")
        self.assertIn("write_binary_model_text", text)
        self.assertIn("sample.binary-model.json", text)
        self.assertIn("symbolic_value_json", text)
        self.assertIn("fragment_specs", text)
        self.assertIn("run_fragment (spec", text)
        self.assertNotIn("fun run_fragment_0", text)

    def test_symexec_runner_configures_stubbed_call_ranges(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"da": str(root / "sample.da"), "theory": "Sample", "symbols": ["*"]},
                    "execution": {
                        "fragments": [
                            {"name": "main", "entry_label": 60, "exit_labels": [132], "end_label": 136}
                        ],
                        "stub_unclassified_calls": True,
                        "allow_unmapped_memory_overapprox": True,
                    },
                    "functions": {"library": [], "adversary": [], "crypto": {}},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            result = run_symexec_stage(case, layout, execute=False)
            runner_text = result["runner"].read_text(encoding="utf-8")
            pipeline_text = result["pipeline_yaml"].read_text(encoding="utf-8")

        self.assertIn("set_stub_unclassified_calls", runner_text)
        self.assertIn("set_allow_unmapped_memory_overapprox", runner_text)
        self.assertIn("set_active_fragment_range (#start_label spec, stop_label)", runner_text)
        self.assertIn("end_label = SOME (IntInf.fromInt 136)", runner_text)
        self.assertIn('channel: "Channel"', pipeline_text)
        self.assertIn("stub_unclassified_calls: true", pipeline_text)
        self.assertIn("allow_unmapped_memory_overapprox: true", pipeline_text)
        self.assertIn("end_label: 136", pipeline_text)
        self.assertNotIn("  entry_label:", pipeline_text.splitlines())

    def test_symexec_pipeline_quotes_binary_names_for_yaml_subset(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "channel": "private_chan",
                    "input": {
                        "da": str(root / "sample.da"),
                        "theory": "Sample-Theory",
                        "symbols": ["ns::send#impl"],
                    },
                    "execution": {
                        "fragments": [
                            {"name": "frag:send#impl", "entry_label": 60, "exit_labels": [132]}
                        ],
                    },
                    "functions": {
                        "library": ["ns::send#impl"],
                        "adversary": ["recv#packet"],
                        "crypto": {"ns::send#impl": "MEMcpy#trace"},
                        "crypto_callsite_labels": {"60": "AEAD:ENC#1"},
                    },
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            result = run_symexec_stage(case, layout, execute=False)
            pipeline_text = result["pipeline_yaml"].read_text(encoding="utf-8")

        self.assertIn('  theory: "Sample_Theory"', pipeline_text)
        self.assertIn('  channel: "private_chan"', pipeline_text)
        self.assertIn('  output_file: "', pipeline_text)
        self.assertIn('    - name: "frag:send#impl"', pipeline_text)
        self.assertIn('  - "ns::send#impl"', pipeline_text)
        self.assertIn('  - "recv#packet"', pipeline_text)
        self.assertIn('  "ns::send#impl": "MEMcpy#trace"', pipeline_text)
        self.assertIn('  60: "AEAD:ENC#1"', pipeline_text)

    def test_symexec_runner_escapes_extra_variable_names(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"da": str(root / "sample.da"), "theory": "Sample", "symbols": ["main"]},
                    "execution": {
                        "entry_label": 60,
                        "exit_labels": [132],
                        "extra_variables": [{"name": 'bad"name\\path', "type": "Imm", "width": 64}],
                    },
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            result = run_symexec_stage(case, layout, execute=False)
            runner_text = result["runner"].read_text(encoding="utf-8")

        self.assertIn(
            'bir_envSyntax.mk_BVar_string ("bad\\"name\\\\path", ``BType_Imm Bit64``)',
            runner_text,
        )
        self.assertNotIn('``BVar "bad"name', runner_text)

    def test_symexec_runner_rejects_non_boolean_execution_flags(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"da": str(root / "sample.da"), "theory": "Sample", "symbols": ["main"]},
                    "execution": {
                        "entry_label": 60,
                        "exit_labels": [132],
                        "stub_unclassified_calls": "false",
                    },
                    "functions": {"library": [], "adversary": [], "crypto": {}},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")

            with self.assertRaises(StageError):
                run_symexec_stage(case, layout, execute=False)

    def test_sml_template_renderer_rejects_missing_arguments(self) -> None:
        with self.assertRaises(StageError):
            _render_sml_template("lift_runner.sml", theory='"Sample"')

    def test_symexec_fixture_fallback_requires_explicit_opt_in(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            holmake = _executable(root / "Holmake", "#!/usr/bin/env python3\nraise SystemExit(1)\n")
            sapic_source = root / "fixture.sapic"
            sapic_source.write_text("out(Channel,msg)", encoding="utf-8")
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"da": str(root / "sample.da"), "theory": "Sample", "symbols": ["main"]},
                    "execution": {"entry_label": 60, "exit_labels": [132]},
                    "artifacts": {"sapic_source": str(sapic_source)},
                    "backends": ["squirrel"],
                },
            )
            (root / "sample.da").write_text(
                "\nfake:     file format elf64-littleaarch64\n\n\nDisassembly of section .text:\n\n000000000000003c <main>:\n  3c:\td503201f \tnop\n",
                encoding="utf-8",
            )
            layout = layout_for_case(case, root / "build")
            layout.bir.mkdir(parents=True)
            (layout.bir / "lifted-labels.json").write_text('{"labels": [60, 132]}\n', encoding="utf-8")

            with self.assertRaises(StageError):
                run_symexec_stage(case, layout, holmake=holmake, holba=root)
            manifest = load_manifest(layout.manifest_path)
            self.assertEqual(manifest["stages"]["symexec"]["status"], "validation_failed")
            self.assertNotIn("fallback_sapic_source", manifest["stages"]["symexec"])

            run_symexec_stage(case, layout, holmake=holmake, holba=root, allow_fixture_fallback=True)
            manifest = load_manifest(layout.manifest_path)
            self.assertEqual(manifest["stages"]["symexec"]["status"], "backend_partial")
            self.assertEqual(manifest["stages"]["symexec"]["fallback_sapic_source"], str(sapic_source))
            self.assertEqual((layout.sapic / "sample.sapic").read_text(encoding="utf-8"), "out(Channel,msg)")

    def test_symexec_fixture_fallback_preserves_existing_generated_outputs(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            holmake = _executable(root / "Holmake", "#!/usr/bin/env python3\nraise SystemExit(1)\n")
            sapic_source = root / "fixture.sapic"
            sapic_source.write_text("out(Channel,fixture)", encoding="utf-8")
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"da": str(root / "sample.da"), "theory": "Sample", "symbols": ["main"]},
                    "execution": {"entry_label": 60, "exit_labels": [132]},
                    "artifacts": {"sapic_source": str(sapic_source)},
                    "backends": ["squirrel"],
                },
            )
            (root / "sample.da").write_text(
                "\nfake:     file format elf64-littleaarch64\n\n\nDisassembly of section .text:\n\n000000000000003c <main>:\n  3c:\td503201f \tnop\n",
                encoding="utf-8",
            )
            layout = layout_for_case(case, root / "build")
            layout.bir.mkdir(parents=True)
            layout.sapic.mkdir(parents=True)
            layout.model.mkdir(parents=True)
            (layout.bir / "lifted-labels.json").write_text('{"labels": [60, 132]}\n', encoding="utf-8")
            existing_sapic = layout.sapic / "sample.sapic"
            existing_model = layout.model / "sample.binary-model.json"
            existing_sapic.write_text("out(Channel,generated)", encoding="utf-8")
            existing_model.write_text('{"schema": "preserved"}\n', encoding="utf-8")

            run_symexec_stage(case, layout, holmake=holmake, holba=root, allow_fixture_fallback=True)
            manifest = load_manifest(layout.manifest_path)

            self.assertEqual(existing_sapic.read_text(encoding="utf-8"), "out(Channel,generated)")
            self.assertEqual(existing_model.read_text(encoding="utf-8"), '{"schema": "preserved"}\n')
            self.assertEqual(manifest["stages"]["symexec"]["status"], "backend_partial")
            self.assertEqual(manifest["stages"]["symexec"]["fallback_preserved_existing_sapic"], str(existing_sapic))
            self.assertEqual(manifest["stages"]["symexec"]["fallback_preserved_existing_binary_model"], str(existing_model))

    def test_sapic_formatter_indents_nested_process_blocks(self) -> None:
        formatted = format_sapic_text("(let 1_R0='0' in\n(out(1_R0);\n(let 2_R1='1' in\n(out(2_R1)))))\n")
        self.assertIn("  (out(1_R0);", formatted)
        self.assertIn("    (let 2_R1='1' in", formatted)

    def test_stage_spthy_requires_configured_tamarin_source(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"symbols": ["main"]},
                    "execution": {"entry_label": 1, "exit_labels": [2]},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            with self.assertRaises(BackendError):
                stage_spthy(case, layout, tamarin=root / "tamarin-prover")

    def test_export_squirrel_records_tamarin_only_export(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "source.spthy"
            source.write_text("theory sample\nbegin\nprocess:\n  out(c,m)\nend\n", encoding="utf-8")
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"symbols": ["main"]},
                    "execution": {"entry_label": 1, "exit_labels": [2]},
                    "artifacts": {"tamarin_source": str(source)},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            tamarin = _executable(
                root / "tamarin-prover",
                """#!/usr/bin/env python3
import json
import pathlib
import sys
log = pathlib.Path(__file__).with_suffix(".argv.json")
items = json.loads(log.read_text(encoding="utf-8")) if log.exists() else []
items.append(sys.argv[1:])
log.write_text(json.dumps(items), encoding="utf-8")
if "--parse-only" in sys.argv:
    print("parse ok")
    raise SystemExit(0)
if "--output-module=squirrel" not in sys.argv:
    raise SystemExit(1)
out = next(arg.split("=", 1)[1] for arg in sys.argv if arg.startswith("--output="))
pathlib.Path(out).write_text("include Core.\\nprocess main = null.\\nsystem main.\\n", encoding="utf-8")
""",
            )
            result = export_squirrel(case, layout, tamarin=tamarin, squirrel=root / "missing-squirrel")
            manifest = load_manifest(layout.manifest_path)
            argv_records = json.loads((root / "tamarin-prover.argv.json").read_text(encoding="utf-8"))
        self.assertEqual(result["effective_exporter"], "tamarin")
        self.assertEqual(result["status"], "validation_failed")
        self.assertIn("missing_squirrel_binary", [item["code"] for item in result["diagnostics"]])
        self.assertEqual(manifest["stages"]["stage_spthy"]["status"], "generated_unchecked")
        self.assertEqual(manifest["stages"]["export_squirrel"]["effective_exporter"], "tamarin")
        self.assertIn(["--parse-only", str((layout.spthy / "sample.spthy").resolve())], argv_records)
        self.assertTrue(any("--output-module=squirrel" in record for record in argv_records))

    def test_export_squirrel_does_not_accept_stale_sp_output(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "source.spthy"
            source.write_text("theory sample\nbegin\nprocess:\n  out(c,m)\nend\n", encoding="utf-8")
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"symbols": ["main"]},
                    "execution": {"entry_label": 1, "exit_labels": [2]},
                    "artifacts": {"tamarin_source": str(source)},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            layout.squirrel.mkdir(parents=True)
            stale = layout.squirrel / "sample.sp"
            stale.write_text("include Core.\nprocess main = null.\nsystem main.\n", encoding="utf-8")
            tamarin = _executable(
                root / "tamarin-prover",
                """#!/usr/bin/env python3
import sys
if "--parse-only" in sys.argv:
    raise SystemExit(0)
raise SystemExit(0)
""",
            )

            with self.assertRaises(BackendError):
                export_squirrel(case, layout, tamarin=tamarin, squirrel=root / "missing-squirrel")

            self.assertEqual("include Core.\nprocess main = null.\nsystem main.\n", stale.read_text(encoding="utf-8"))

    def test_export_squirrel_stages_configured_spthy_source(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "source.spthy"
            source.write_text("theory sample\nbegin\nprocess:\n  out(c,new)\nend\n", encoding="utf-8")
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"symbols": ["main"]},
                    "execution": {"entry_label": 1, "exit_labels": [2]},
                    "artifacts": {"tamarin_source": str(source)},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            layout.spthy.mkdir(parents=True)
            (layout.spthy / "sample.spthy").write_text(
                "theory old\nbegin\nprocess:\n  out(c,m)\nend\n",
                encoding="utf-8",
            )
            tamarin = _executable(
                root / "tamarin-prover",
                """#!/usr/bin/env python3
import pathlib
import sys
if "--parse-only" in sys.argv:
    raise SystemExit(0)
out = next(arg.split("=", 1)[1] for arg in sys.argv if arg.startswith("--output="))
pathlib.Path(out).write_text("include Core.\\nprocess main = null.\\nsystem main.\\n", encoding="utf-8")
""",
            )
            export_squirrel(case, layout, tamarin=tamarin, squirrel=root / "missing-squirrel")
            staged_text = (layout.spthy / "sample.spthy").read_text(encoding="utf-8")
            manifest = load_manifest(layout.manifest_path)

        self.assertIn("out(c,new)", staged_text)
        self.assertEqual(str(source), manifest["stages"]["stage_spthy"]["source"])

    def test_export_squirrel_does_not_repair_tamarin_output(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "source.spthy"
            source.write_text("theory sample\nbegin\nprocess:\n  out(c,m)\nend\n", encoding="utf-8")
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"symbols": ["main"]},
                    "execution": {"entry_label": 1, "exit_labels": [2]},
                    "artifacts": {"tamarin_source": str(source)},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            tamarin = _executable(
                root / "tamarin-prover",
                """#!/usr/bin/env python3
import pathlib
import sys
if "--parse-only" in sys.argv:
    raise SystemExit(0)
out = next(arg.split("=", 1)[1] for arg in sys.argv if arg.startswith("--output="))
pathlib.Path(out).write_text(\"\"\"include Core.
abstract sig_verify : message * message -> message.
process main =
  if sig_verify(sig_1, pkS_1) then
    null
  else
    null.
system main.
\"\"\", encoding="utf-8")
""",
            )
            squirrel = _executable(
                root / "squirrel",
                """#!/usr/bin/env python3
import pathlib
import sys
text = pathlib.Path(sys.argv[1]).read_text(encoding="utf-8")
raise SystemExit(0 if "abstract sig_verify : message * message -> bool." in text else 1)
""",
            )
            result = export_squirrel(case, layout, tamarin=tamarin, squirrel=squirrel)
            text = (layout.squirrel / "sample.sp").read_text(encoding="utf-8")
            manifest = load_manifest(layout.manifest_path)

        self.assertIn("abstract sig_verify : message * message -> message.", text)
        self.assertEqual(["squirrel_validation_failed"], [item["code"] for item in result["diagnostics"]])
        self.assertNotIn("squirrel_abstract_repair", [item["code"] for item in result["diagnostics"]])
        self.assertNotIn("squirrel_abstract_repairs", manifest["stages"]["export_squirrel"])

    def test_readable_squirrel_rewrites_generated_names_without_touching_canonical_file(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            da = root / "sample.da"
            da.write_text(
                """
fake:     file format elf64-littleaarch64

Disassembly of section .text:

0000000000001000 <main>:
  1004:\t94000000 \tbl 2000 <fmt.Sprintf>
  1008:\t94000000 \tbl 2010 <strconv.FormatInt>
""",
                encoding="utf-8",
            )
            source = root / "source.spthy"
            source.write_text("theory sample\nbegin\nprocess:\n  out(c,m)\nend\n", encoding="utf-8")
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"da": str(da), "symbols": ["main"]},
                    "execution": {
                        "fragments": [
                            {"name": "main", "entry_label": 0x1000, "end_label": 0x1010, "exit_labels": [0x1008]}
                        ]
                    },
                    "artifacts": {"tamarin_source": str(source)},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            tamarin = _executable(
                root / "tamarin-prover",
                """#!/usr/bin/env python3
import pathlib
import sys
if "--parse-only" in sys.argv:
    raise SystemExit(0)
out = next(arg.split("=", 1)[1] for arg in sys.argv if arg.startswith("--output="))
pathlib.Path(out).write_text(\"\"\"include Core.
channel pub_chan.
abstract s51820 : message.
abstract sv20_C_Lib : message.
abstract sv10_C_Lib : message.
abstract Plus : message * message -> message.

process main =
  let v4_R17_2 = s51820 in
  out(pub_chan, sv10_C_Lib);
  out(pub_chan, sv20_C_Lib).
system main.
\"\"\", encoding="utf-8")
""",
            )
            result = export_squirrel(
                case,
                layout,
                tamarin=tamarin,
                squirrel=root / "missing-squirrel",
                readable=True,
            )
            canonical_text = (layout.squirrel / "sample.sp").read_text(encoding="utf-8")
            readable_text = result["readable_squirrel"].read_text(encoding="utf-8")
            manifest = load_manifest(layout.manifest_path)

        self.assertIn("sv10_C_Lib", canonical_text)
        self.assertIn("ret_fmt_Sprintf_1004", readable_text)
        self.assertIn("ret_strconv_FormatInt_1008", readable_text)
        self.assertIn("const_51820", readable_text)
        self.assertIn("reg_R17_4", readable_text)
        self.assertIn("stubbed call return: fmt.Sprintf at 0x1004", readable_text)
        self.assertIn("stubbed call return: strconv.FormatInt at 0x1008", readable_text)
        self.assertIn("readable_squirrel", manifest["artifacts"])

    def test_squirrel_export_does_not_fallback_when_tamarin_module_is_missing(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "source.spthy"
            source.write_text("theory sample\nbegin\nprocess:\n  out(c,m)\nend\n", encoding="utf-8")
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"symbols": ["main"]},
                    "execution": {"entry_label": 1, "exit_labels": [2]},
                    "artifacts": {"tamarin_source": str(source)},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            tamarin = _executable(
                root / "tamarin-prover",
                """#!/usr/bin/env python3
import sys
if "--parse-only" in sys.argv:
    raise SystemExit(0)
print("tamarin-prover: output mode not supported.")
raise SystemExit(1)
""",
            )
            with self.assertRaises(BackendError):
                export_squirrel(case, layout, tamarin=tamarin, squirrel=root / "missing-squirrel")
            manifest = load_manifest(layout.manifest_path)
        self.assertNotIn("export_squirrel", manifest.get("stages", {}))
        self.assertNotIn("backend_partial", json.dumps(manifest))

    def test_squirrel_export_fails_on_tamarin_parse_failure(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "source.spthy"
            source.write_text("theory sample\nbegin\nprocess:\n  0\n  out(c,m)\nend\n", encoding="utf-8")
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"symbols": ["main"]},
                    "execution": {"entry_label": 1, "exit_labels": [2]},
                    "artifacts": {"tamarin_source": str(source)},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            tamarin = _executable(
                root / "tamarin-prover",
                """#!/usr/bin/env python3
print("unexpected 0")
raise SystemExit(1)
""",
            )
            with self.assertRaises(BackendError) as raised:
                export_squirrel(case, layout, tamarin=tamarin, squirrel=root / "missing-squirrel")
            manifest = load_manifest(layout.manifest_path)
            log_text = (layout.logs / "tamarin-validate.log").read_text(encoding="utf-8")
            self.assertIn("Tamarin SPTHY validation failed", str(raised.exception))
        self.assertEqual("validation_failed", manifest["stages"]["stage_spthy"]["status"])
        self.assertIn("unexpected 0", log_text)

    def test_checked_in_squirrel_cases_have_tamarin_sources(self) -> None:
        template_missing = [
            name for name, text in CASE_TEMPLATES.items() if "squirrel" in text and "tamarin_source" not in text
        ]
        self.assertEqual([], template_missing)
        if not (CRYPTOBAP2_ROOT / "examples").exists():
            self.skipTest("CryptoBAP2 example artifacts are not available")

        roots = [
            CRYPTOBAP2_ROOT / "cases",
            CRYPTOBAP2_ROOT / "examples",
        ]
        missing: list[str] = []
        for root in roots:
            if not root.exists():
                continue
            for path in root.rglob("*.yaml"):
                if {"build", "cryptobap2-build", "work"}.intersection(path.parts):
                    continue
                data = load_yaml_subset(path)
                backends = [str(item) for item in data.get("backends", [])] if isinstance(data, dict) else []
                if "squirrel" not in backends:
                    continue
                case = CaseConfig(path=path, raw=data)
                source = case.artifacts.get("tamarin_source")
                if source is None or not source.exists():
                    missing.append(str(path.relative_to(CRYPTOBAP2_ROOT)))

        self.assertEqual([], missing)

    def test_registered_case_yaml_uses_supported_schema(self) -> None:
        failures: list[str] = []
        for path in sorted((CRYPTOBAP2_ROOT / "cases").glob("*.yaml")):
            data = load_yaml_subset(path)
            for diagnostic in validate_case_schema(data, path=path):
                failures.append(f"{path.name}: {diagnostic.field}: {diagnostic.message}")

        self.assertEqual([], failures)

    def test_tamarin_parse_and_squirrel_validation_diagnostics_are_first_class(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"symbols": ["main"]},
                    "execution": {"entry_label": 1, "exit_labels": [2]},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            layout.spthy.mkdir(parents=True)
            layout.squirrel.mkdir(parents=True)
            spthy = layout.spthy / "sample.spthy"
            sp = layout.squirrel / "sample.sp"
            spthy.write_text("theory sample\nbegin\nprocess:\n  out(c,m)\nend\n", encoding="utf-8")
            sp.write_text("process Sample = null.\nsystem Sample.\n", encoding="utf-8")
            tamarin = _executable(root / "tamarin-prover", "#!/usr/bin/env python3\nprint('parse ok')\n")
            squirrel = _executable(root / "squirrel", "#!/usr/bin/env python3\nprint('Typing.Error: nope')\nraise SystemExit(1)\n")
            self.assertEqual(validate_tamarin_spthy(spthy, layout, tamarin=tamarin), [])
            diagnostics = validate_backend_outputs(spthy, sp, layout, tamarin=tamarin, squirrel=squirrel)
        self.assertIn("squirrel_validation_failed", [item["code"] for item in diagnostics])
        self.assertTrue(check_failed([Finding("error", "squirrel_validation_failed", "bad")], strict=False))

    def test_backend_validation_treats_placeholder_squirrel_as_error(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            layout = layout_for_case(
                CaseConfig(
                    path=root / "case.yaml",
                    raw={
                        "name": "sample",
                        "arch": "arm8",
                        "input": {"symbols": ["main"]},
                        "execution": {"entry_label": 1, "exit_labels": [2]},
                        "backends": ["squirrel"],
                    },
                ),
                root / "build",
            )
            layout.spthy.mkdir(parents=True)
            layout.squirrel.mkdir(parents=True)
            spthy = layout.spthy / "sample.spthy"
            sp = layout.squirrel / "sample.sp"
            spthy.write_text("theory sample\nbegin\nprocess:\n  0\nend\n", encoding="utf-8")
            sp.write_text("(* placeholder Squirrel export *)\n", encoding="utf-8")
            diagnostics = validate_backend_outputs(
                spthy,
                sp,
                layout,
                squirrel=root / "missing-squirrel",
                validate_tamarin=False,
            )

        self.assertIn(
            {"severity": "error", "code": "placeholder_squirrel", "message": str(sp)},
            diagnostics,
        )


if __name__ == "__main__":
    unittest.main()
