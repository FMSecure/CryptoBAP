from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from .config import CaseConfig
from .manifest import BuildLayout


_DA_FUNCTION_HEADER_RE = re.compile(r"^([0-9A-Fa-f]+)\s+<([^>]+)>:")
_DA_INSTRUCTION_RE = re.compile(
    r"^\s*[0-9A-Fa-f]+:\s+(?:[0-9A-Fa-f]{2,}\s+)+\s*[A-Za-z_.][A-Za-z0-9_.]*\b"
)


def parse_lifted_labels(text: str) -> set[int]:
    labels: set[int] = set()
    for match in re.finditer(r"BL_Address(?:_HC)?\s*\(Imm(?:32|64)\s+([0-9]+)w", text):
        labels.add(int(match.group(1)))
    for match in re.finditer(r"BL_Address(?:_HC)?\s*\(Imm(?:32|64)\s+0x([0-9A-Fa-f]+)w", text):
        labels.add(int(match.group(1), 16))
    return labels


def validate_fragment_labels(case: CaseConfig, layout: BuildLayout) -> list[dict[str, Any]]:
    metadata_path = layout.bir / "lifted-labels.json"
    if not metadata_path.exists():
        return [
            {
                "severity": "warning",
                "code": "missing_lifted_label_metadata",
                "message": "could not validate labels because lift metadata is missing",
            }
        ]
    metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
    labels = {int(label) for label in metadata.get("labels", [])}
    diagnostics: list[dict[str, Any]] = []
    for fragment in case.fragments:
        requested = [int(fragment["entry_label"]), *[int(value) for value in fragment.get("exit_labels", [])]]
        for label in requested:
            if label not in labels:
                diagnostics.append(
                    {
                        "severity": "error",
                        "code": "bad_label",
                        "message": f"label {label} was not found in lifted metadata {metadata_path}",
                    }
                )
    return diagnostics


def _scan_da_scope(case: CaseConfig) -> dict[str, Any]:
    da_path = case.input_da
    if da_path is None or not da_path.exists():
        return {}

    symbols = set(case.symbols)
    wildcard_symbols = symbols == {"*"}
    line_count = 0
    function_count = 0
    instruction_count = 0
    selected_instruction_count = 0
    selected_functions: set[str] = set()
    current_name: str | None = None
    current_instruction_count = 0

    def flush_function() -> None:
        nonlocal selected_instruction_count, current_name, current_instruction_count
        if current_name is not None and (wildcard_symbols or current_name in symbols):
            selected_functions.add(current_name)
            selected_instruction_count += current_instruction_count
        current_name = None
        current_instruction_count = 0

    with da_path.open("r", encoding="utf-8", errors="replace") as handle:
        for raw in handle:
            line_count += 1
            header = _DA_FUNCTION_HEADER_RE.match(raw.strip())
            if header is not None:
                flush_function()
                function_count += 1
                current_name = header.group(2)
                continue
            if current_name is None:
                continue
            if _DA_INSTRUCTION_RE.match(raw):
                instruction_count += 1
                current_instruction_count += 1
    flush_function()

    return {
        "input_da": str(da_path),
        "input_da_line_count": line_count,
        "input_da_function_count": function_count,
        "input_da_instruction_count": instruction_count,
        "selected_symbol_count": function_count if wildcard_symbols else len(symbols),
        "selected_symbol_found_count": len(selected_functions),
        "selected_symbol_instruction_count": selected_instruction_count,
    }


def _lifted_label_count(layout: BuildLayout) -> int | None:
    metadata_path = layout.bir / "lifted-labels.json"
    if not metadata_path.exists():
        return None
    try:
        metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None
    labels = metadata.get("labels")
    return len(labels) if isinstance(labels, list) else None


def _ratio(numerator: int, denominator: int | None) -> float | None:
    if denominator is None or denominator <= 0:
        return None
    return numerator / denominator


def sapic_translation_coverage(case: CaseConfig, layout: BuildLayout, sapic_path: Path) -> dict[str, Any]:
    text = sapic_path.read_text(encoding="utf-8", errors="replace") if sapic_path.exists() else ""
    sapic_lines = [line for line in text.splitlines() if line.strip()]
    lifted_labels = _lifted_label_count(layout)
    coverage: dict[str, Any] = {
        "sapic_line_count": len(sapic_lines),
        "sapic_action_count": len(re.findall(r"\b(?:in|out|event)\s*\(", text)) + len(re.findall(r"\bnew\s+", text)),
        "lifted_label_count": lifted_labels,
        "sapic_to_lifted_label_ratio": _ratio(len(sapic_lines), lifted_labels),
    }
    coverage.update(_scan_da_scope(case))
    if coverage.get("input_da_line_count"):
        coverage["sapic_to_input_da_line_ratio"] = _ratio(len(sapic_lines), int(coverage["input_da_line_count"]))
    if coverage.get("selected_symbol_instruction_count"):
        coverage["sapic_to_selected_symbol_instruction_ratio"] = _ratio(
            len(sapic_lines),
            int(coverage["selected_symbol_instruction_count"]),
        )

    diagnostics: list[dict[str, Any]] = []
    if text.strip() == "0":
        diagnostics.append(
            {
                "severity": "error",
                "code": "sapic_null_process",
                "message": f"generated Sapic for {case.name} is a null process",
            }
        )
    elif lifted_labels is not None and lifted_labels > 0 and len(sapic_lines) / lifted_labels < 0.02:
        diagnostics.append(
            {
                "severity": "error",
                "code": "sapic_too_small_for_lifted_scope",
                "message": (
                    f"generated Sapic has {len(sapic_lines)} non-empty lines for {lifted_labels} lifted labels"
                ),
            }
        )

    full_functions = coverage.get("input_da_function_count")
    selected = coverage.get("selected_symbol_count")
    if isinstance(full_functions, int) and isinstance(selected, int) and selected and selected < full_functions:
        diagnostics.append(
            {
                "severity": "warning",
                "code": "partial_disassembly_scope",
                "message": (
                    f"case lifts {selected} configured symbol(s) out of {full_functions} functions in input.da; "
                    "Sapic line count is expected to match the lifted fragment scope, not the full disassembly"
                ),
            }
        )

    coverage["diagnostics"] = diagnostics
    return coverage
