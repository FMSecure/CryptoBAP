from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

from .config import CaseConfig
from .manifest import BuildLayout


ARTIFACT_FOLDERS = ("bir", "tree", "model", "sapic", "spthy", "squirrel")

_FUNCTION_RE = re.compile(r"^([0-9A-Fa-f]+)\s+<(.+)>:$")
_INSTRUCTION_RE = re.compile(r"^\s*([0-9A-Fa-f]+):")


@dataclass(frozen=True)
class SourceLine:
    number: int
    text: str


@dataclass(frozen=True)
class FunctionSpan:
    name: str
    start: int
    start_line: int
    end_line: int


def _read_source(path: Path) -> list[SourceLine]:
    return [
        SourceLine(number=index, text=line.rstrip("\n"))
        for index, line in enumerate(path.read_text(encoding="utf-8", errors="replace").splitlines(True), 1)
    ]


def _function_spans(lines: list[SourceLine]) -> list[FunctionSpan]:
    starts: list[tuple[int, str, int]] = []
    for line in lines:
        match = _FUNCTION_RE.match(line.text)
        if match:
            starts.append((int(match.group(1), 16), match.group(2), line.number))

    spans: list[FunctionSpan] = []
    for index, (start, name, start_line) in enumerate(starts):
        end_line = starts[index + 1][2] - 1 if index + 1 < len(starts) else len(lines)
        spans.append(FunctionSpan(name=name, start=start, start_line=start_line, end_line=end_line))
    return spans


def _line_slice(lines: list[SourceLine], start_line: int, end_line: int) -> list[SourceLine]:
    return [line for line in lines if start_line <= line.number <= end_line]


def _find_function(spans: list[FunctionSpan], address: int) -> FunctionSpan | None:
    found: FunctionSpan | None = None
    for span in spans:
        if span.start <= address:
            found = span
        else:
            break
    return found


def _instruction_address(line: SourceLine) -> int | None:
    match = _INSTRUCTION_RE.match(line.text)
    if not match:
        return None
    return int(match.group(1), 16)


def _fragment_lines(lines: list[SourceLine], start: int, end: int) -> list[SourceLine]:
    selected: list[SourceLine] = []
    for line in lines:
        address = _instruction_address(line)
        if address is not None and start <= address < end:
            selected.append(line)
    return selected


def _format_lines(lines: Iterable[SourceLine]) -> list[str]:
    return [f"{line.number:>6}: {line.text}" for line in lines]


def _format_hex(value: int) -> str:
    return f"0x{value:x} / {value}"


def _source_segments_filename(case: CaseConfig) -> str:
    return f"{case.name}.da.segments.txt"


def _render_segments(case: CaseConfig, artifact_folder: str) -> str:
    source = case.input_da
    if source is None or not source.exists():
        return (
            "# CryptoBAP2 source disassembly segments\n\n"
            f"case: {case.name}\n"
            f"artifact_folder: {artifact_folder}\n"
            "input_da: <missing>\n"
        )

    lines = _read_source(source)
    spans = _function_spans(lines)
    functions_by_name = {span.name: span for span in spans}

    output: list[str] = [
        "# CryptoBAP2 source disassembly segments",
        "",
        f"case: {case.name}",
        f"artifact_folder: {artifact_folder}",
        f"input_da: {source}",
        "",
        "These excerpts are copied from the input disassembly for traceability.",
        "Selected symbols are the lift input; fragment ranges are the symbolic-execution input.",
        "",
        "## Selected Symbol Disassembly",
    ]

    for symbol in case.symbols:
        if symbol == "*":
            output.extend(["", "### *", "wildcard symbol selection; no bounded source excerpt emitted"])
            continue
        span = functions_by_name.get(symbol)
        if span is None:
            output.extend(["", f"### {symbol}", "not found in input disassembly"])
            continue
        output.extend(
            [
                "",
                f"### {symbol}",
                f"range_start: {_format_hex(span.start)}",
                f"source_lines: {span.start_line}-{span.end_line}",
                "",
                "```text",
                *_format_lines(_line_slice(lines, span.start_line, span.end_line)),
                "```",
            ]
        )

    output.extend(["", "## Symbolic-Execution Fragment Disassembly"])
    for fragment in case.fragments:
        try:
            name = str(fragment.get("name", "fragment"))
            start = int(fragment["entry_label"])
            exits = [int(value) for value in fragment.get("exit_labels", [])]
            end = int(fragment.get("end_label", max(exits) + 4 if exits else start + 4))
        except (KeyError, TypeError, ValueError):
            continue

        selected = _fragment_lines(lines, start, end)
        enclosing = _find_function(spans, start)
        line_range = f"{selected[0].number}-{selected[-1].number}" if selected else "<empty>"
        output.extend(
            [
                "",
                f"### {name}",
                f"entry_label: {_format_hex(start)}",
                "exit_labels: " + ", ".join(_format_hex(exit_label) for exit_label in exits),
                f"end_label: {_format_hex(end)}",
                f"enclosing_function: {enclosing.name if enclosing else '<unknown>'}",
                f"source_lines: {line_range}",
                "",
                "```text",
                *_format_lines(selected),
                "```",
            ]
        )

    return "\n".join(output).rstrip() + "\n"


def write_source_segment_files(
    case: CaseConfig,
    layout: BuildLayout,
    *,
    folders: Iterable[str] = ARTIFACT_FOLDERS,
) -> dict[str, Path]:
    written: dict[str, Path] = {}
    for folder in folders:
        artifact_dir = getattr(layout, folder, None)
        if not isinstance(artifact_dir, Path):
            continue
        artifact_dir.mkdir(parents=True, exist_ok=True)
        output = artifact_dir / _source_segments_filename(case)
        output.write_text(_render_segments(case, folder), encoding="utf-8")
        written[f"source_segments_{folder}"] = output
    return written
