from __future__ import annotations

import contextlib
import io
import json
import stat
import tempfile
import unittest
import zipfile
from pathlib import Path
from unittest import mock

import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "toolchain"))
XOR_FROM_BINARY_DA = ROOT / "examples" / "xor" / "build" / "xor-from-binary" / "bir" / "xor-from-binary.da"

from cryptobap2.autocase import parse_da_functions, scaffold_case_from_da
from cryptobap2.binary_model import BINARY_MODEL_SCHEMA, validate_binary_model_data
from cryptobap2.checks import Finding, _scan_unguarded_debug_prints, check_failed, run_checks
from cryptobap2.cli import main as cli_main
from cryptobap2.config import load_case, load_yaml_subset
from cryptobap2.config import CaseConfig
from cryptobap2.disassembly import (
    DEFAULT_GHIDRA_VERSION,
    DisassemblyError,
    ghidra_download_url,
    prepare_case_disassembly,
    resolve_ghidra_headless,
    run_ghidra_disassembly,
    _safe_extract,
)
from cryptobap2.inference import (
    infer_functions,
    inferred_case_raw,
    merge_missing_inferred_fields,
    parse_da_function_analysis,
    render_case_yaml,
)
from cryptobap2.manifest import case_config_sha256, update_manifest
from cryptobap2.manifest import layout_for_case, load_manifest
from cryptobap2.schema import validate_case_schema
from cryptobap2.source_segments import write_source_segment_files
from cryptobap2.squirrel_backend import BackendError, stage_spthy
from cryptobap2.stages import write_lift_descriptor, write_symexec_descriptor


class CryptoBAP2ToolchainTests(unittest.TestCase):
    def _write_fake_extract_holmake(self, root: Path) -> Path:
        holmake = root / "Holmake"
        holmake.write_text(
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
if "CryptoBAP2Symexec" in target:
    script = next(pathlib.Path.cwd().glob("CryptoBAP2Symexec_*Script.sml"))
    text = script.read_text()
    sapic = re.search(r'write_sapic_text\\s*\\("([^"]+)"', text).group(1)
    model = re.search(r'write_binary_model_text\\s*\\("([^"]+)"', text).group(1)
    pathlib.Path(sapic).write_text("out(Channel,msg)", encoding="utf-8")
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
            "sapic": "out(Channel,msg)"
        }}]
    }}), encoding="utf-8")
else:
    script = next(pathlib.Path.cwd().glob("SampleScript.sml"))
    text = script.read_text()
    label_dump = re.search(r'TextIO.openOut "([^"]+)"', text).group(1)
    pathlib.Path(label_dump).write_text("BL_Address (Imm64 60w) BL_Address (Imm64 132w)", encoding="utf-8")
""",
            encoding="utf-8",
        )
        holmake.chmod(holmake.stat().st_mode | stat.S_IXUSR)
        return holmake

    def _write_fake_ghidra(self, root: Path) -> Path:
        fake = root / "analyzeHeadless"
        fake.write_text(
            """#!/usr/bin/env python3
import pathlib
import sys
idx = sys.argv.index("-postScript")
output = pathlib.Path(sys.argv[idx + 2])
output.write_text("\\nfake:     file format elf64-littleaarch64\\n\\n\\nDisassembly of section .text:\\n\\n000000000000003c <main>:\\n  3c:\\td503201f \\tnop\\n  84:\\td65f03c0 \\tret\\n", encoding="utf-8")
""",
            encoding="utf-8",
        )
        fake.chmod(fake.stat().st_mode | stat.S_IXUSR)
        return fake

    def _write_fake_tamarin_exporter(self, root: Path) -> Path:
        tamarin = root / "tamarin-prover"
        tamarin.write_text(
            """#!/usr/bin/env python3
import pathlib
import sys
if "--parse-only" in sys.argv:
    print("parse ok")
    raise SystemExit(0)
output = next((arg.split("=", 1)[1] for arg in sys.argv if arg.startswith("--output=")), None)
if output is None:
    print("missing --output")
    raise SystemExit(1)
pathlib.Path(output).write_text("include Core.\\nchannel catt.\\nprocess main = null.\\nsystem main.\\n", encoding="utf-8")
print("export ok")
""",
            encoding="utf-8",
        )
        tamarin.chmod(tamarin.stat().st_mode | stat.S_IXUSR)
        return tamarin

    def _write_fake_squirrel(self, root: Path) -> Path:
        squirrel = root / "squirrel"
        squirrel.write_text("#!/usr/bin/env python3\nprint('squirrel ok')\n", encoding="utf-8")
        squirrel.chmod(squirrel.stat().st_mode | stat.S_IXUSR)
        return squirrel

    def test_case_yaml_subset_parser_handles_fragments(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "case.yaml"
            path.write_text(
                """
name: sample
input:
  symbols: [main, helper]
execution:
  fragments:
    - name: first
      entry_label: 0x10
      exit_labels: [0x20, 0x30]
""",
                encoding="utf-8",
            )
            data = load_yaml_subset(path)
        self.assertEqual(data["execution"]["fragments"][0]["entry_label"], 0x10)
        self.assertEqual(data["execution"]["fragments"][0]["exit_labels"], [0x20, 0x30])

    def test_scaffold_case_from_da_infers_return_fragments(self) -> None:
        da = XOR_FROM_BINARY_DA
        functions = parse_da_functions(da)
        self.assertIn("main", [function.name for function in functions])

        scaffold = scaffold_case_from_da(
            da,
            arch="arm8",
            name="sample",
            symbols=["send", "main"],
        )
        with tempfile.TemporaryDirectory() as tmp:
            case_path = Path(tmp) / "case.yaml"
            case_path.write_text(scaffold.text, encoding="utf-8")
            data = load_yaml_subset(case_path)
        self.assertEqual(data["input"]["symbols"], ["send", "main"])
        self.assertEqual(data["execution"]["fragments"][0]["entry_label"], 0)
        self.assertEqual(data["execution"]["fragments"][0]["exit_labels"], [16])
        self.assertEqual(data["execution"]["fragments"][1]["entry_label"], 52)
        self.assertEqual(data["execution"]["fragments"][1]["exit_labels"], [132])
        self.assertEqual(data["functions"]["crypto"]["send"], "MEMcpy")

    def test_all_functions_scope_groups_local_labels_and_restart_blocks(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            da = Path(tmp) / "sample.da"
            da.write_text(
                """
fake:     file format elf64-littleaarch64


Disassembly of section .text:

0000000000001000 <foo>:
  1000:\td503201f \tnop
  1004:\td65f03c0 \tret
0000000000001020 <LAB_00001020>:
  1020:\t94000000 \tbl 2000 <runtime.morestack_noctxt.abi0>
  1024:\t17fffff7 \tb 1000 <foo>
0000000000001030 <bar>:
  1030:\t14000004 \tb 2000 <runtime.morestack_noctxt.abi0>
0000000000002000 <runtime.morestack_noctxt.abi0>:
  2000:\td65f03c0 \tret
""",
                encoding="utf-8",
            )
            functions = parse_da_function_analysis(da, group_local_labels=True)
            result = infer_functions(da, symbols=None, max_functions=16, scope="all-functions")

        self.assertEqual([function.name for function in functions], ["foo", "bar", "runtime.morestack_noctxt.abi0"])
        self.assertEqual(functions[0].local_labels, ["LAB_00001020"])
        self.assertEqual(functions[0].exit_labels, [0x1004, 0x1020])
        self.assertEqual(functions[1].exit_labels, [0x1030])
        self.assertEqual(result.scope, "all-functions")
        self.assertEqual([function.name for function in result.selected_functions], ["foo", "bar", "runtime.morestack_noctxt.abi0"])

    def test_auto_scope_groups_local_labels_for_requested_symbol(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            da = Path(tmp) / "sample.da"
            da.write_text(
                """
fake:     file format elf64-littleaarch64


Disassembly of section .text:

0000000000001000 <foo>:
  1000:\td503201f \tnop
0000000000001020 <LAB_00001020>:
  1020:\t17fffff7 \tb 1000 <foo>
0000000000001040 <bar>:
  1040:\td65f03c0 \tret
""",
                encoding="utf-8",
            )
            result = infer_functions(da, symbols=["foo"], max_functions=16, scope="auto")
            scaffold = scaffold_case_from_da(da, arch="arm8", name="sample", symbols=["foo"])
            case_path = Path(tmp) / "case.yaml"
            case_path.write_text(scaffold.text, encoding="utf-8")
            data = load_yaml_subset(case_path)

        self.assertEqual(result.scope, "auto")
        self.assertEqual([function.name for function in result.discovered_functions], ["foo", "bar"])
        self.assertEqual(result.selected_functions[0].end_label, 0x1040)
        self.assertEqual(result.selected_functions[0].local_labels, ["LAB_00001020"])
        self.assertEqual(result.selected_functions[0].exit_labels, [0x1020])
        self.assertEqual(data["input"]["symbols"], ["foo", "LAB_00001020"])
        self.assertEqual([fragment["name"] for fragment in data["execution"]["fragments"]], ["foo"])

    def test_scaffold_case_all_functions_uses_wildcard_symbols(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            da = Path(tmp) / "sample.da"
            da.write_text(
                """
fake:     file format elf64-littleaarch64


Disassembly of section .text:

0000000000001000 <foo>:
  1000:\td65f03c0 \tret
0000000000001010 <LAB_00001010>:
  1010:\t17fffffc \tb 1000 <foo>
0000000000001020 <bar>:
  1020:\td65f03c0 \tret
""",
                encoding="utf-8",
            )
            scaffold = scaffold_case_from_da(da, arch="arm8", name="sample", scope="all-functions")
            case_path = Path(tmp) / "case.yaml"
            case_path.write_text(scaffold.text, encoding="utf-8")
            data = load_yaml_subset(case_path)

        fragment_names = [fragment["name"] for fragment in data["execution"]["fragments"]]
        self.assertEqual(data["input"]["symbols"], ["*"])
        self.assertEqual(fragment_names, ["foo", "bar"])
        self.assertNotIn("LAB_00001010", fragment_names)
        self.assertTrue(data["execution"]["stub_unclassified_calls"])
        self.assertEqual(data["inference"]["scope"], "all-functions")

    def test_incomplete_direct_case_preserves_inferred_stubbed_calls(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            da = Path(tmp) / "sample.da"
            da.write_text(
                """
fake:     file format elf64-littleaarch64


Disassembly of section .text:

0000000000001000 <foo>:
  1000:\td65f03c0 \tret
0000000000001020 <bar>:
  1020:\td65f03c0 \tret
""",
                encoding="utf-8",
            )
            inferred, _ = inferred_case_raw(
                da_path=da,
                arch="arm8",
                name="sample",
                theory="Sample",
                binary_path=None,
                sections=[".text"],
                symbols=None,
                max_functions=16,
                scope="all-functions",
            )
            merged = merge_missing_inferred_fields(
                {
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"da": str(da), "theory": "Sample"},
                },
                inferred,
            )

        self.assertEqual(merged["input"]["symbols"], ["*"])
        self.assertTrue(merged["execution"]["stub_unclassified_calls"])
        self.assertEqual(merged["inference"]["scope"], "all-functions")

    def test_incomplete_direct_case_preserves_inferred_local_labels(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            da = Path(tmp) / "sample.da"
            da.write_text(
                """
fake:     file format elf64-littleaarch64


Disassembly of section .text:

0000000000001000 <foo>:
  1000:\td503201f \tnop
0000000000001020 <LAB_00001020>:
  1020:\t17fffff7 \tb 1000 <foo>
0000000000001040 <bar>:
  1040:\td65f03c0 \tret
""",
                encoding="utf-8",
            )
            inferred, _ = inferred_case_raw(
                da_path=da,
                arch="arm8",
                name="sample",
                theory="Sample",
                binary_path=None,
                sections=[".text"],
                symbols=["foo"],
                max_functions=16,
            )
            merged = merge_missing_inferred_fields(
                {
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"da": str(da), "theory": "Sample", "symbols": ["foo"]},
                },
                inferred,
            )

        self.assertEqual(inferred["input"]["symbols"], ["foo", "LAB_00001020"])
        self.assertEqual(merged["input"]["symbols"], ["foo", "LAB_00001020"])

    def test_scaffold_without_crypto_preserves_local_labels(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            da = Path(tmp) / "sample.da"
            da.write_text(
                """
fake:     file format elf64-littleaarch64


Disassembly of section .text:

0000000000001000 <foo>:
  1000:\td503201f \tnop
0000000000001020 <LAB_00001020>:
  1020:\t17fffff7 \tb 1000 <foo>
0000000000001040 <bar>:
  1040:\td65f03c0 \tret
""",
                encoding="utf-8",
            )
            scaffold = scaffold_case_from_da(
                da,
                arch="arm8",
                name="sample",
                symbols=["foo"],
                infer_crypto=False,
            )
            case_path = Path(tmp) / "case.yaml"
            case_path.write_text(scaffold.text, encoding="utf-8")
            data = load_yaml_subset(case_path)

        self.assertEqual(data["input"]["symbols"], ["foo", "LAB_00001020"])

    def test_scaffold_without_crypto_all_functions_scope_selects_functions(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            da = Path(tmp) / "sample.da"
            da.write_text(
                """
fake:     file format elf64-littleaarch64


Disassembly of section .text:

0000000000001000 <foo>:
  1000:\td65f03c0 \tret
0000000000001020 <bar>:
  1020:\td65f03c0 \tret
""",
                encoding="utf-8",
            )
            scaffold = scaffold_case_from_da(
                da,
                arch="arm8",
                name="sample",
                infer_crypto=False,
                scope="all-functions",
            )
            case_path = Path(tmp) / "case.yaml"
            case_path.write_text(scaffold.text, encoding="utf-8")
            data = load_yaml_subset(case_path)

        self.assertEqual(data["input"]["symbols"], ["*"])
        self.assertEqual([fragment["name"] for fragment in data["execution"]["fragments"]], ["foo", "bar"])

    def test_da_inference_classifies_checked_in_binary_examples(self) -> None:
        examples = {
            "xor": (
                ROOT / "examples" / "xor" / "build" / "xor-from-binary" / "bir" / "xor-from-binary.da",
                {"new_key": "OTP", "senc": "XOR", "send": "MEMcpy"},
            ),
            "double-xor": (
                ROOT / "examples" / "double-xor" / "build" / "double-xor-from-binary" / "bir" / "double-xor-from-binary.da",
                {"new_key": "OTP", "senc": "XOR", "mix": "XOR", "send": "MEMcpy"},
            ),
            "two-key": (
                ROOT / "examples" / "two-key" / "build" / "two-key-from-binary" / "bir" / "two-key-from-binary.da",
                {"client_key": "OTP", "server_key": "OTP", "protect": "XOR", "send": "MEMcpy"},
            ),
        }
        for _name, (da, expected) in examples.items():
            with self.subTest(da=da):
                result = infer_functions(da, symbols=None, max_functions=16)
                self.assertEqual(result.crypto, expected)

    def test_all_functions_scope_finds_nordvpnd_nordlynx_config(self) -> None:
        da = ROOT / "examples" / "nordvpn" / "build" / "nordvpnd" / "bir" / "nordvpnd.da"
        result = infer_functions(da, symbols=None, max_functions=16, scope="all-functions")
        target = "github.com/NordSecurity/nordvpn-linux/daemon/vpn/nordlynx.wgQuickConfig"
        matches = [function for function in result.selected_functions if function.name == target]

        self.assertEqual(result.scope, "all-functions")
        self.assertEqual(result.as_metadata()["selected_symbols"], ["*"])
        self.assertEqual(len(matches), 1)
        self.assertEqual(matches[0].exit_labels, [0xB631E8, 0xB631EC])

    def test_scaffold_case_cli_writes_yaml_from_da(self) -> None:
        da = XOR_FROM_BINARY_DA
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "draft.yaml"
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                code = cli_main(
                    [
                        "scaffold-case",
                        str(da),
                        "--from-da",
                        "--name",
                        "sample",
                        "--symbols",
                        "send,main",
                        "--output",
                        str(output),
                    ]
                )
            self.assertEqual(code, 0)
            data = load_yaml_subset(output)
        self.assertEqual(data["name"], "sample")
        self.assertEqual(data["backends"], ["squirrel"])
        self.assertEqual(data["functions"]["crypto"], {"send": "MEMcpy"})
        self.assertEqual(data["inference"]["selected_symbols"], ["send", "main"])

    def test_scaffold_case_cli_can_keep_empty_classifications(self) -> None:
        da = XOR_FROM_BINARY_DA
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "draft.yaml"
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                code = cli_main(
                    [
                        "scaffold-case",
                        str(da),
                        "--from-da",
                        "--name",
                        "sample",
                        "--symbols",
                        "send,main",
                        "--output",
                        str(output),
                        "--no-infer-crypto",
                    ]
                )
            self.assertEqual(code, 0)
            data = load_yaml_subset(output)
        self.assertEqual(data["functions"], {"library": [], "adversary": [], "crypto": {}})

    def test_stage_descriptors_and_manifest_are_written(self) -> None:
        case = load_case("xor")
        with tempfile.TemporaryDirectory() as tmp:
            layout = layout_for_case(case, Path(tmp))
            lift = write_lift_descriptor(case, layout)
            symexec = write_symexec_descriptor(case, layout)
            self.assertTrue(lift.exists())
            self.assertTrue(symexec.exists())
            manifest = load_manifest(layout.manifest_path)
            runner_text = Path(manifest["artifacts"]["symexec_runner"]["path"]).read_text(encoding="utf-8")
        self.assertEqual(manifest["schema"], "cryptobap2-manifest-v3")
        self.assertIn("work", manifest["layout"])
        self.assertIn("model", manifest["layout"])
        self.assertNotIn("hol", manifest["layout"])
        self.assertNotIn("hol_src", manifest["layout"])
        self.assertIn("lift", manifest["stages"])
        self.assertIn("symexec", manifest["stages"])
        self.assertIsNone(manifest["stages"]["lift"]["hol_source_root"])
        self.assertIn("_cryptobap2-support-cache", manifest["stages"]["symexec"]["hol_source_root"])
        self.assertIn("model_output", manifest["stages"]["symexec"])
        self.assertIn("write_binary_model_text", runner_text)
        self.assertIn(".binary-model.json", runner_text)
        self.assertFalse((layout.work / "src").exists())

    def test_stage_spthy_copies_configured_source_and_manifest_hashes(self) -> None:
        case = load_case("xor")
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            layout = layout_for_case(case, root)
            tamarin = self._write_fake_tamarin_exporter(root)
            artifacts = stage_spthy(case, layout, tamarin=tamarin)
            self.assertTrue(artifacts["spthy"].exists())
            manifest = load_manifest(layout.manifest_path)
            self.assertIn("sha256", manifest["artifacts"]["spthy"])
            self.assertEqual(manifest["stages"]["stage_spthy"]["status"], "generated_unchecked")
            self.assertEqual(manifest["stages"]["stage_spthy"]["source_kind"], "tamarin_source")
            self.assertIn("theory XOR_Pipeline", artifacts["spthy"].read_text(encoding="utf-8"))

    def test_stage_spthy_requires_configured_tamarin_source(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            da = root / "sample.da"
            da.write_text("fake", encoding="utf-8")
            case = CaseConfig(
                path=root / "new.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"da": str(da), "symbols": ["main"]},
                    "execution": {"entry_label": 3, "exit_labels": [4]},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")

            with self.assertRaises(BackendError):
                stage_spthy(case, layout, tamarin=root / "tamarin-prover")

    def test_schema_reports_structured_backend_error(self) -> None:
        diagnostics = validate_case_schema(
            {
                "name": "sample",
                "input": {"symbols": ["main"]},
                "execution": {"entry_label": 1, "exit_labels": [2]},
                "backends": ["unknown"],
            }
        )
        self.assertEqual([diagnostic.code for diagnostic in diagnostics], ["bad_backend"])

    def test_schema_rejects_unimplemented_proverif_backend(self) -> None:
        diagnostics = validate_case_schema(
            {
                "name": "sample",
                "input": {"symbols": ["main"]},
                "execution": {"entry_label": 1, "exit_labels": [2]},
                "backends": ["proverif"],
            }
        )
        self.assertEqual([diagnostic.code for diagnostic in diagnostics], ["bad_backend"])

    def test_schema_requires_boolean_memory_overapprox_flag(self) -> None:
        diagnostics = validate_case_schema(
            {
                "name": "sample",
                "input": {"symbols": ["main"]},
                "execution": {
                    "entry_label": 1,
                    "exit_labels": [2],
                    "allow_unmapped_memory_overapprox": "yes",
                },
            }
        )
        self.assertIn("bad_type", [diagnostic.code for diagnostic in diagnostics])

    def test_schema_requires_boolean_stub_unclassified_calls_flag(self) -> None:
        diagnostics = validate_case_schema(
            {
                "name": "sample",
                "input": {"symbols": ["main"]},
                "execution": {
                    "entry_label": 1,
                    "exit_labels": [2],
                    "stub_unclassified_calls": "false",
                },
            }
        )
        self.assertIn("bad_type", [diagnostic.code for diagnostic in diagnostics])

    def test_schema_requires_integer_fragment_end_label(self) -> None:
        diagnostics = validate_case_schema(
            {
                "name": "sample",
                "input": {"symbols": ["main"]},
                "execution": {
                    "fragments": [
                        {
                            "name": "main",
                            "entry_label": 1,
                            "end_label": "bad",
                            "exit_labels": [2],
                        }
                    ],
                },
            }
        )
        self.assertIn("bad_label", [diagnostic.code for diagnostic in diagnostics])

    def test_schema_rejects_boolean_labels(self) -> None:
        scalar_diagnostics = validate_case_schema(
            {
                "name": "sample",
                "input": {"symbols": ["main"]},
                "execution": {"entry_label": True, "exit_labels": [False]},
            }
        )
        fragment_diagnostics = validate_case_schema(
            {
                "name": "sample",
                "input": {"symbols": ["main"]},
                "execution": {
                    "fragments": [
                        {
                            "name": "main",
                            "entry_label": True,
                            "end_label": False,
                            "exit_labels": [False],
                        }
                    ]
                },
            }
        )
        self.assertEqual([diagnostic.code for diagnostic in scalar_diagnostics], ["bad_label", "bad_label"])
        self.assertEqual([diagnostic.code for diagnostic in fragment_diagnostics], ["bad_label", "bad_label", "bad_label"])

    def test_schema_validates_extra_variables_shape(self) -> None:
        diagnostics = validate_case_schema(
            {
                "name": "sample",
                "input": {"symbols": ["main"]},
                "execution": {
                    "entry_label": 1,
                    "exit_labels": [2],
                    "extra_variables": [{"name": "", "type": "Unknown", "width": "bad"}],
                },
            }
        )
        self.assertEqual([diagnostic.code for diagnostic in diagnostics], ["bad_type", "bad_type", "bad_type"])

    def test_case_yaml_renderer_rejects_non_boolean_execution_flags(self) -> None:
        raw = {
            "name": "sample",
            "arch": "arm8",
            "channel": "Channel",
            "input": {"da": "sample.da", "theory": "Sample", "symbols": ["main"]},
            "execution": {
                "fragments": [{"name": "main", "entry_label": 1, "exit_labels": [2]}],
                "extra_variables": [],
                "stub_unclassified_calls": "false",
            },
            "functions": {"library": [], "adversary": [], "crypto": {}},
            "backends": ["squirrel"],
            "proof_status": {},
            "security_lemmas": [],
        }
        with self.assertRaises(ValueError):
            render_case_yaml(raw)

    def test_bad_symbol_fails_non_strict_check(self) -> None:
        self.assertTrue(check_failed([Finding("error", "bad_symbol", "bad")], strict=False))

    def test_strict_debug_print_scan_ignores_sml_comments(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "Sample.sml"
            path.write_text(
                """(* val _ = print "commented" *)
val _ = print "active"
val _ = if true then () else print "guarded"
""",
                encoding="utf-8",
            )
            findings = _scan_unguarded_debug_prints([root])
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].line, 2)

    def test_binary_model_schema_reports_bad_fragments(self) -> None:
        diagnostics = validate_binary_model_data(
            {
                "schema": BINARY_MODEL_SCHEMA,
                "fragments": [
                    {
                        "name": "",
                        "entry_label": "not-an-int",
                        "exit_labels": ["bad"],
                        "total_states": "one",
                    }
                ],
            }
        )
        self.assertEqual([item["code"] for item in diagnostics], ["bad_model_fragment"] * 4)

    def test_binary_model_schema_rejects_boolean_integer_fields(self) -> None:
        diagnostics = validate_binary_model_data(
            {
                "schema": BINARY_MODEL_SCHEMA,
                "fragments": [
                    {
                        "name": "main",
                        "entry_label": True,
                        "exit_labels": [False],
                        "total_states": True,
                        "assertion_clean_states": False,
                    }
                ],
            }
        )
        self.assertEqual(
            [item["field"] for item in diagnostics],
            [
                "fragments[0].entry_label",
                "fragments[0].exit_labels",
                "fragments[0].total_states",
                "fragments[0].assertion_clean_states",
            ],
        )

    def test_source_segments_accept_function_header_whitespace(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            da = root / "sample.da"
            da.write_text(
                """Disassembly of section .text:

00000040    <main>:
  40: 00 00 00 00   nop
  44: 00 00 00 00   ret
""",
                encoding="utf-8",
            )
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "input": {"da": str(da), "symbols": ["main"]},
                    "execution": {"entry_label": 0x40, "exit_labels": [0x44]},
                },
            )
            layout = layout_for_case(case, root / "build")
            written = write_source_segment_files(case, layout, folders=("bir",))
            text = written["source_segments_bir"].read_text(encoding="utf-8")

        self.assertIn("### main", text)
        self.assertNotIn("not found in input disassembly", text)
        self.assertIn("enclosing_function: main", text)

    def test_schema_accepts_binary_disassembly_config(self) -> None:
        diagnostics = validate_case_schema(
            {
                "name": "sample",
                "input": {
                    "binary": "examples/bin/sample.elf",
                    "symbols": ["main"],
                    "disassembly": {"tool": "ghidra", "sections": [".text"]},
                },
                "execution": {"entry_label": 1, "exit_labels": [2]},
                "backends": ["squirrel"],
            }
        )
        self.assertEqual(diagnostics, [])

    def test_ghidra_resolution_accepts_executable_path(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            fake = Path(tmp) / "analyzeHeadless"
            fake.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            fake.chmod(fake.stat().st_mode | stat.S_IXUSR)
            self.assertEqual(resolve_ghidra_headless(fake), fake.resolve())

    def test_default_ghidra_url_uses_known_version(self) -> None:
        url = ghidra_download_url(DEFAULT_GHIDRA_VERSION)
        self.assertIn(f"Ghidra_{DEFAULT_GHIDRA_VERSION}_build", url)
        self.assertIn(f"ghidra_{DEFAULT_GHIDRA_VERSION}_PUBLIC", url)

    def test_safe_extract_rejects_path_traversal(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            opt = Path(tmp) / "opt"
            opt.mkdir()
            archive = opt / "bad.zip"
            with zipfile.ZipFile(archive, "w") as handle:
                handle.writestr("../escape.txt", "bad")
            with self.assertRaises(DisassemblyError):
                _safe_extract(archive, opt / "extract", opt_dir=opt)

    def test_fake_ghidra_disassemble_writes_da(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fake = root / "analyzeHeadless"
            fake.write_text(
                """#!/usr/bin/env python3
import os
import pathlib
import sys
idx = sys.argv.index("-postScript")
output = pathlib.Path(sys.argv[idx + 2])
output.write_text("\\nfake:     file format elf64-littleaarch64\\n\\n\\nDisassembly of section .text:\\n\\n0000000000000000 <main>:\\n   0:\\td503201f \\tnop\\n", encoding="utf-8")
(output.parent / "xdg-config.txt").write_text(os.environ.get("XDG_CONFIG_HOME", ""), encoding="utf-8")
print("fake ghidra")
""",
                encoding="utf-8",
            )
            fake.chmod(fake.stat().st_mode | stat.S_IXUSR)
            binary = root / "sample.elf"
            binary.write_bytes(b"\x00\x01\x02\x03")
            output = root / "sample.da"
            result = run_ghidra_disassembly(binary, output, arch="arm8", ghidra=fake)
            self.assertTrue(result["output"].exists())
            self.assertIn("Disassembly of section .text", output.read_text(encoding="utf-8"))
            self.assertIn("cryptobap2-ghidra-", (root / "xdg-config.txt").read_text(encoding="utf-8"))

    def test_check_reports_direct_da_input_as_cli_error(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            da = Path(tmp) / "sample.da"
            da.write_text(
                """
fake:     file format elf64-littleaarch64


Disassembly of section .text:

0000000000001000 <main>:
  1000:\td65f03c0 \tret
""",
                encoding="utf-8",
            )
            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr):
                code = cli_main(["--build-root", str(Path(tmp) / "build"), "check", str(da)])

        self.assertEqual(code, 2)
        self.assertIn("cryptobap2: error:", stderr.getvalue())
        self.assertIn("could not parse case YAML", stderr.getvalue())

    def test_prepare_case_disassembly_records_missing_ghidra_fallback(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            binary = root / "sample.elf"
            binary.write_bytes(b"\x00")
            da = root / "sample.da"
            da.write_text(
                "\nfake:     file format elf64-littleaarch64\n\n\nDisassembly of section .text:\n\n0000000000000000 <main>:\n   0:\td503201f \tnop\n",
                encoding="utf-8",
            )
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"binary": str(binary), "da": str(da), "symbols": ["main"]},
                    "execution": {"entry_label": 0, "exit_labels": [4]},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            with mock.patch("cryptobap2.disassembly.resolve_ghidra_headless", return_value=None):
                returned = prepare_case_disassembly(
                    case,
                    layout,
                    ghidra=root / "missing-analyzeHeadless",
                    install_missing=False,
                )
            manifest = load_manifest(layout.manifest_path)
        self.assertEqual(returned.input_da, da)
        self.assertEqual(manifest["stages"]["disassemble"]["status"], "missing")

    def test_prepare_case_disassembly_fails_missing_requested_symbol(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fake = root / "analyzeHeadless"
            fake.write_text(
                """#!/usr/bin/env python3
import pathlib
import sys
idx = sys.argv.index("-postScript")
output = pathlib.Path(sys.argv[idx + 2])
output.write_text("\\nfake:     file format elf64-littleaarch64\\n\\n\\nDisassembly of section .text:\\n\\n0000000000000000 <main>:\\n   0:\\td503201f \\tnop\\n", encoding="utf-8")
""",
                encoding="utf-8",
            )
            fake.chmod(fake.stat().st_mode | stat.S_IXUSR)
            binary = root / "sample.elf"
            binary.write_bytes(b"\x00")
            case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"binary": str(binary), "symbols": ["missing_symbol"]},
                    "execution": {"entry_label": 0, "exit_labels": [4]},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(case, root / "build")
            with self.assertRaises(DisassemblyError):
                prepare_case_disassembly(case, layout, ghidra=fake, install_missing=False)
            manifest = load_manifest(layout.manifest_path)
        self.assertEqual(manifest["stages"]["disassemble"]["status"], "validation_failed")

    def test_extract_model_cli_prints_binary_model_path(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            da = root / "sample.da"
            da.write_text(
                "\nfake:     file format elf64-littleaarch64\n\n\nDisassembly of section .text:\n\n000000000000003c <main>:\n  3c:\td503201f \tnop\n",
                encoding="utf-8",
            )
            holmake = root / "Holmake"
            holmake.write_text(
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
if "CryptoBAP2Symexec" in target:
    script = next(pathlib.Path.cwd().glob("CryptoBAP2Symexec_*Script.sml"))
    text = script.read_text()
    sapic = re.search(r'write_sapic_text\\s*\\("([^"]+)"', text).group(1)
    model = re.search(r'write_binary_model_text\\s*\\("([^"]+)"', text).group(1)
    pathlib.Path(sapic).write_text("out(Channel,msg)", encoding="utf-8")
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
            "sapic": "out(Channel,msg)"
        }}]
    }}), encoding="utf-8")
else:
    script = next(pathlib.Path.cwd().glob("SampleScript.sml"))
    text = script.read_text()
    label_dump = re.search(r'TextIO.openOut "([^"]+)"', text).group(1)
    pathlib.Path(label_dump).write_text("BL_Address (Imm64 60w) BL_Address (Imm64 132w)", encoding="utf-8")
""",
                encoding="utf-8",
            )
            holmake.chmod(holmake.stat().st_mode | stat.S_IXUSR)
            case_path = root / "case.yaml"
            case_path.write_text(
                f"""
name: sample
arch: arm8
channel: Channel
input:
  da: {da}
  theory: Sample
  symbols: [main]
execution:
  entry_label: 60
  exit_labels: [132]
functions:
  library: []
  adversary: []
  crypto: {{}}
backends: [squirrel]
proof_status:
  hol: generated_unchecked
  sapic: generated_unchecked
  squirrel: generated_unchecked
security_lemmas: []
""",
                encoding="utf-8",
            )
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(io.StringIO()):
                code = cli_main(
                    [
                        "--build-root",
                        str(root / "build"),
                        "--holmake",
                        str(holmake),
                        "--holba",
                        str(root),
                        "extract-model",
                        str(case_path),
                    ]
                )
            self.assertEqual(code, 0)
            model_path = Path(stdout.getvalue().strip().splitlines()[-1])
            model = json.loads(model_path.read_text(encoding="utf-8"))
        self.assertEqual(model_path.name, "sample.binary-model.json")
        self.assertEqual(model["schema"], BINARY_MODEL_SCHEMA)
        self.assertIsNotNone(model["provenance"]["sapic_sha256"])

    def test_symexec_cli_reruns_stale_lift_artifact(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            da = root / "sample.da"
            da.write_text(
                "\nfake:     file format elf64-littleaarch64\n\n\nDisassembly of section .text:\n\n000000000000003c <main>:\n  3c:\td503201f \tnop\n  84:\td65f03c0 \tret\n",
                encoding="utf-8",
            )
            call_log = root / "holmake-calls.txt"
            holmake = root / "Holmake"
            holmake.write_text(
                f"""#!/usr/bin/env python3
import json
import pathlib
import re
import sys

target = sys.argv[1] if len(sys.argv) > 1 else ""
pathlib.Path({str(call_log)!r}).open("a", encoding="utf-8").write(target + "\\n")
objs = pathlib.Path(".hol/objs")
objs.mkdir(parents=True, exist_ok=True)
(objs / target).write_text("uo", encoding="utf-8")
if "CryptoBAP2Symexec" in target:
    script = next(pathlib.Path.cwd().glob("CryptoBAP2Symexec_*Script.sml"))
    text = script.read_text()
    sapic = re.search(r'write_sapic_text\\s*\\("([^"]+)"', text).group(1)
    model = re.search(r'write_binary_model_text\\s*\\("([^"]+)"', text).group(1)
    pathlib.Path(sapic).write_text("out(Channel,msg)", encoding="utf-8")
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
            "sapic": "out(Channel,msg)"
        }}]
    }}), encoding="utf-8")
else:
    script = next(pathlib.Path.cwd().glob("SampleScript.sml"))
    text = script.read_text()
    label_dump = re.search(r'TextIO.openOut "([^"]+)"', text).group(1)
    pathlib.Path(label_dump).write_text("BL_Address (Imm64 60w) BL_Address (Imm64 132w)", encoding="utf-8")
""",
                encoding="utf-8",
            )
            holmake.chmod(holmake.stat().st_mode | stat.S_IXUSR)
            case_path = root / "case.yaml"
            case_path.write_text(
                f"""
name: sample
arch: arm8
channel: Channel
input:
  da: {da}
  theory: Sample
  symbols: [main]
execution:
  entry_label: 60
  exit_labels: [132]
functions:
  library: []
  adversary: []
  crypto: {{}}
backends: [squirrel]
security_lemmas: []
""",
                encoding="utf-8",
            )
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(
                    cli_main(
                        [
                            "--build-root",
                            str(root / "build"),
                            "--holmake",
                            str(holmake),
                            "--holba",
                            str(root),
                            "lift",
                            str(case_path),
                        ]
                    ),
                    0,
                )
            da.write_text(da.read_text(encoding="utf-8") + "\n# changed after lift\n", encoding="utf-8")
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(
                    cli_main(
                        [
                            "--build-root",
                            str(root / "build"),
                            "--holmake",
                            str(holmake),
                            "--holba",
                            str(root),
                            "symexec",
                            str(case_path),
                        ]
                    ),
                    0,
                )
            calls = call_log.read_text(encoding="utf-8").splitlines()
        self.assertEqual(calls.count("SampleTheory.uo"), 2)
        self.assertTrue(any(call.startswith("CryptoBAP2Symexec_") for call in calls))

    def test_extract_model_accepts_binary_without_user_yaml(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            ghidra = self._write_fake_ghidra(root)
            holmake = self._write_fake_extract_holmake(root)
            binary = root / "sample.o"
            binary.write_bytes(b"\x00\x01\x02\x03")
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(io.StringIO()):
                code = cli_main(
                    [
                        "--build-root",
                        str(root / "build"),
                        "--holmake",
                        str(holmake),
                        "--holba",
                        str(root),
                        "--ghidra",
                        str(ghidra),
                        "extract-model",
                        str(binary),
                        "--arch",
                        "arm8",
                    ]
                )
            self.assertEqual(code, 0)
            model_path = Path(stdout.getvalue().strip().splitlines()[-1])
            inferred_case = root / "build" / "sample" / "work" / "inferred-case.yaml"
            inferred_case_exists = inferred_case.exists()
            manifest = load_manifest(root / "build" / "sample" / "manifest.json")
        self.assertEqual(model_path.name, "sample.binary-model.json")
        self.assertTrue(inferred_case_exists)
        self.assertEqual(manifest["config"]["input"]["symbols"], ["main"])
        self.assertIn("inference", manifest["stages"])

    def test_run_squirrel_rejects_binary_without_tamarin_source(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            ghidra = self._write_fake_ghidra(root)
            holmake = self._write_fake_extract_holmake(root)
            tamarin = self._write_fake_tamarin_exporter(root)
            squirrel = self._write_fake_squirrel(root)
            binary = root / "sample.o"
            binary.write_bytes(b"\x00\x01\x02\x03")
            stdout = io.StringIO()
            stderr = io.StringIO()
            with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                code = cli_main(
                    [
                        "--build-root",
                        str(root / "build"),
                        "--holmake",
                        str(holmake),
                        "--holba",
                        str(root),
                        "--ghidra",
                        str(ghidra),
                        "run",
                        str(binary),
                        "--arch",
                        "arm8",
                        "--target",
                        "squirrel",
                        "--tamarin",
                        str(tamarin),
                        "--squirrel",
                        str(squirrel),
                        "--readable-squirrel",
                    ]
                )
            spthy = root / "build" / "sample" / "spthy" / "sample.spthy"
            sp = root / "build" / "sample" / "squirrel" / "sample.sp"
            readable_sp = root / "build" / "sample" / "squirrel" / "sample.readable.sp"
            spthy_exists = spthy.exists()
            sp_exists = sp.exists()
            readable_sp_exists = readable_sp.exists()
        self.assertEqual(code, 2)
        self.assertIn("artifacts.tamarin_source", stderr.getvalue())
        self.assertFalse(spthy_exists)
        self.assertFalse(sp_exists)
        self.assertFalse(readable_sp_exists)

    def test_run_tamarin_uses_target_scoped_backend_check(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            ghidra = self._write_fake_ghidra(root)
            holmake = self._write_fake_extract_holmake(root)
            tamarin = self._write_fake_tamarin_exporter(root)
            binary = root / "sample.o"
            binary.write_bytes(b"\x00\x01\x02\x03")
            source = root / "source.spthy"
            source.write_text("theory sample\nbegin\nprocess:\n  out(c,m)\nend\n", encoding="utf-8")
            case_path = root / "case.yaml"
            case_path.write_text(
                f"""
name: sample
arch: arm8
input:
  binary: {binary}
  theory: Sample
  symbols: [main]
execution:
  entry_label: 60
  exit_labels: [132]
artifacts:
  tamarin_source: {source}
backends: [squirrel]
""",
                encoding="utf-8",
            )
            stdout = io.StringIO()
            stderr = io.StringIO()
            with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                code = cli_main(
                    [
                        "--build-root",
                        str(root / "build"),
                        "--holmake",
                        str(holmake),
                        "--holba",
                        str(root),
                        "--ghidra",
                        str(ghidra),
                        "run",
                        str(case_path),
                        "--arch",
                        "arm8",
                        "--target",
                        "tamarin",
                        "--tamarin",
                        str(tamarin),
                    ]
                )
            spthy = root / "build" / "sample" / "spthy" / "sample.spthy"
            sp = root / "build" / "sample" / "squirrel" / "sample.sp"
            spthy_exists = spthy.exists()
            sp_exists = sp.exists()
            manifest = load_manifest(root / "build" / "sample" / "manifest.json")

        self.assertEqual(code, 0, stderr.getvalue())
        self.assertTrue(spthy_exists)
        self.assertFalse(sp_exists)
        self.assertEqual(manifest["config"]["backends"], ["squirrel"])
        self.assertEqual(manifest["stages"]["stage_spthy"]["status"], "generated_unchecked")
        self.assertNotIn("missing_artifact", [item["code"] for item in manifest["diagnostics"]])

    def test_extract_model_completes_minimal_binary_yaml(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            ghidra = self._write_fake_ghidra(root)
            holmake = self._write_fake_extract_holmake(root)
            binary = root / "sample.o"
            binary.write_bytes(b"\x00\x01\x02\x03")
            case_path = root / "minimal.yaml"
            case_path.write_text(
                f"""
input:
  binary: {binary}
""",
                encoding="utf-8",
            )
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(io.StringIO()):
                code = cli_main(
                    [
                        "--build-root",
                        str(root / "build"),
                        "--holmake",
                        str(holmake),
                        "--holba",
                        str(root),
                        "--ghidra",
                        str(ghidra),
                        "extract-model",
                        str(case_path),
                        "--arch",
                        "arm8",
                    ]
                )
            self.assertEqual(code, 0)
            model_path = Path(stdout.getvalue().strip().splitlines()[-1])
            inferred_case = root / "build" / "sample" / "work" / "inferred-case.yaml"
            data = load_yaml_subset(inferred_case)
        self.assertEqual(model_path.name, "sample.binary-model.json")
        self.assertEqual(data["name"], "sample")
        self.assertEqual(data["input"]["symbols"], ["main"])
        self.assertEqual(data["execution"]["fragments"][0]["entry_label"], 60)

    def test_checks_are_pure_without_record(self) -> None:
        case = load_case("xor")
        with tempfile.TemporaryDirectory() as tmp:
            layout = layout_for_case(case, Path(tmp))
            write_lift_descriptor(case, layout)
            before = load_manifest(layout.manifest_path)
            findings = run_checks(case, layout, strict=False, record=False)
            after = load_manifest(layout.manifest_path)
        self.assertTrue(findings)
        self.assertEqual(before.get("diagnostics"), after.get("diagnostics"))

    def test_check_reports_stale_manifest_config(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            old_case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"symbols": ["main"]},
                    "execution": {"entry_label": 1, "exit_labels": [2]},
                    "backends": ["squirrel"],
                },
            )
            new_case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"symbols": ["main"]},
                    "execution": {"entry_label": 3, "exit_labels": [4]},
                    "backends": ["squirrel"],
                },
            )
            layout = layout_for_case(old_case, root / "build")
            update_manifest(
                old_case,
                layout,
                stage="symexec",
                stage_data={
                    "status": "generated_unchecked",
                    "case_config_sha256": case_config_sha256(old_case),
                },
            )
            findings = run_checks(new_case, layout, strict=False, record=False)
        codes = [finding.code for finding in findings]
        self.assertIn("stale_config", codes)
        self.assertIn("stale_stage_config", codes)
        self.assertTrue(check_failed(findings, strict=False))

    def test_check_record_preserves_stale_manifest_config(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            old_case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"symbols": ["main"]},
                    "execution": {"entry_label": 1, "exit_labels": [2]},
                    "backends": ["tamarin"],
                },
            )
            new_case = CaseConfig(
                path=root / "case.yaml",
                raw={
                    "name": "sample",
                    "arch": "arm8",
                    "input": {"symbols": ["main"]},
                    "execution": {"entry_label": 3, "exit_labels": [4]},
                    "backends": ["tamarin"],
                },
            )
            layout = layout_for_case(old_case, root / "build")
            update_manifest(
                old_case,
                layout,
                stage="disassemble",
                stage_data={"status": "generated_unchecked"},
            )
            first_findings = run_checks(new_case, layout, strict=False, record=True)
            manifest_after_record = load_manifest(layout.manifest_path)
            second_findings = run_checks(new_case, layout, strict=False, record=False)

        self.assertIn("stale_config", [finding.code for finding in first_findings])
        self.assertEqual(manifest_after_record["config"], old_case.to_manifest_config())
        self.assertIn("stale_config", [finding.code for finding in second_findings])
        self.assertTrue(check_failed(second_findings, strict=False))

    def test_missing_manifest_artifact_record_fails_check(self) -> None:
        case = CaseConfig(
            path=Path("case.yaml"),
            raw={
                "name": "sample",
                "arch": "arm8",
                "input": {"symbols": ["main"]},
                "execution": {"entry_label": 1, "exit_labels": [2]},
                "backends": ["squirrel"],
            },
        )
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            layout = layout_for_case(case, root / "build")
            missing = layout.work / ".hol" / "objs" / "SampleTheory.uo"
            update_manifest(
                case,
                layout,
                stage="lift",
                stage_data={"status": "generated_unchecked"},
                artifacts={"lifted_theory_uo": missing},
            )
            findings = run_checks(case, layout, strict=False, record=False)
        self.assertIn("missing_artifact", [finding.code for finding in findings])
        self.assertTrue(check_failed(findings, strict=False))

    def test_unbuilt_squirrel_case_fails_check(self) -> None:
        case = CaseConfig(
            path=Path("case.yaml"),
            raw={
                "name": "sample",
                "arch": "arm8",
                "input": {"symbols": ["main"]},
                "execution": {"entry_label": 1, "exit_labels": [2]},
                "backends": ["squirrel"],
            },
        )
        with tempfile.TemporaryDirectory() as tmp:
            layout = layout_for_case(case, Path(tmp))
            findings = run_checks(case, layout, strict=False, record=False)

        codes = [finding.code for finding in findings]
        self.assertIn("missing_manifest", codes)
        self.assertIn("missing_artifact", codes)
        self.assertTrue(check_failed(findings, strict=False))

    def test_tamarin_backend_missing_spthy_fails_check(self) -> None:
        case = CaseConfig(
            path=Path("case.yaml"),
            raw={
                "name": "sample",
                "arch": "arm8",
                "input": {"symbols": ["main"]},
                "execution": {"entry_label": 1, "exit_labels": [2]},
                "backends": ["tamarin"],
            },
        )
        with tempfile.TemporaryDirectory() as tmp:
            layout = layout_for_case(case, Path(tmp))
            findings = run_checks(case, layout, strict=False, record=False)

        self.assertIn("missing_spthy", [finding.code for finding in findings])
        self.assertTrue(check_failed(findings, strict=False))

    def test_squirrel_backend_sp_without_spthy_fails_check(self) -> None:
        case = CaseConfig(
            path=Path("case.yaml"),
            raw={
                "name": "sample",
                "arch": "arm8",
                "input": {"symbols": ["main"]},
                "execution": {"entry_label": 1, "exit_labels": [2]},
                "backends": ["squirrel"],
            },
        )
        with tempfile.TemporaryDirectory() as tmp:
            layout = layout_for_case(case, Path(tmp))
            layout.squirrel.mkdir(parents=True)
            sp = layout.squirrel / "sample.sp"
            sp.write_text("system null.\n", encoding="utf-8")
            update_manifest(
                case,
                layout,
                stage="export_squirrel",
                stage_data={"status": "generated_unchecked"},
                artifacts={"squirrel": sp},
            )
            findings = run_checks(case, layout, strict=False, record=False)

        self.assertIn("missing_spthy", [finding.code for finding in findings])
        self.assertTrue(check_failed(findings, strict=False))

    def test_target_scoped_check_ignores_non_target_squirrel_manifest_state(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "source.spthy"
            source.write_text("theory sample\nbegin\nend\n", encoding="utf-8")
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
            layout = layout_for_case(case, root)
            update_manifest(
                case,
                layout,
                stage="export_squirrel",
                stage_data={
                    "status": "validation_failed",
                    "case_config_sha256": case_config_sha256(case),
                    "diagnostics": [
                        {"severity": "error", "code": "squirrel_validation_failed", "message": "old"}
                    ],
                },
                artifacts={"squirrel": layout.squirrel / "sample.sp"},
            )
            layout.spthy.mkdir(parents=True)
            spthy = layout.spthy / "sample.spthy"
            spthy.write_text("theory sample\nbegin\nend\n", encoding="utf-8")
            update_manifest(
                case,
                layout,
                stage="stage_spthy",
                stage_data={
                    "status": "generated_unchecked",
                    "case_config_sha256": case_config_sha256(case),
                    "diagnostics": [],
                },
                artifacts={"spthy": spthy},
            )
            scoped_findings = run_checks(case, layout, strict=False, record=False, backends=["tamarin"])
            full_findings = run_checks(case, layout, strict=False, record=False)

        scoped_codes = [finding.code for finding in scoped_findings]
        self.assertNotIn("missing_artifact", scoped_codes)
        self.assertNotIn("validation_failed", scoped_codes)
        self.assertNotIn("squirrel_validation_failed", scoped_codes)
        self.assertFalse(check_failed(scoped_findings, strict=False))

        full_codes = [finding.code for finding in full_findings]
        self.assertIn("missing_artifact", full_codes)
        self.assertIn("validation_failed", full_codes)
        self.assertIn("squirrel_validation_failed", full_codes)
        self.assertTrue(check_failed(full_findings, strict=False))

    def test_strict_fails_partial_backend_status(self) -> None:
        case = load_case("xor")
        with tempfile.TemporaryDirectory() as tmp:
            layout = layout_for_case(case, Path(tmp))
            update_manifest(case, layout, stage="symexec", stage_data={"status": "backend_partial"})
            findings = run_checks(case, layout, strict=True, record=False)
        self.assertTrue(check_failed(findings, strict=True))

    def test_export_cli_returns_nonzero_on_squirrel_validation_error(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "source.spthy"
            source.write_text("theory sample\nbegin\nprocess:\n  out(c,m)\nend\n", encoding="utf-8")
            raw = {
                "name": "sample",
                "arch": "arm8",
                "input": {"symbols": ["main"]},
                "execution": {"entry_label": 1, "exit_labels": [2]},
                "artifacts": {"tamarin_source": str(source)},
                "backends": ["squirrel"],
            }
            case_path = root / "case.yaml"
            case_path.write_text(
                f"""
name: sample
arch: arm8
input:
  symbols: [main]
execution:
  entry_label: 1
  exit_labels: [2]
artifacts:
  tamarin_source: {source}
backends: [squirrel]
""",
                encoding="utf-8",
            )
            case = CaseConfig(path=case_path, raw=raw)
            layout = layout_for_case(case, root / "build")
            tamarin = self._write_fake_tamarin_exporter(root)
            squirrel = root / "squirrel"
            squirrel.write_text("#!/usr/bin/env python3\nprint('Typing.Error: bad')\nraise SystemExit(1)\n", encoding="utf-8")
            squirrel.chmod(squirrel.stat().st_mode | stat.S_IXUSR)

            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                code = cli_main(
                    [
                        "--build-root",
                        str(root / "build"),
                        "export",
                        str(case_path),
                        "--target",
                        "squirrel",
                        "--tamarin",
                        str(tamarin),
                        "--squirrel",
                        str(squirrel),
                    ]
                )
            manifest = load_manifest(layout.manifest_path)
        self.assertEqual(code, 1)
        self.assertEqual(manifest["stages"]["export_squirrel"]["status"], "validation_failed")


if __name__ == "__main__":
    unittest.main()
