from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .binary_model import binary_model_path
from .config import CaseConfig
from .manifest import BuildLayout
from .readability import CallTarget, call_targets_for_fragments, readable_return_name, readable_symbolic_name


_TOKEN_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_]*\b")


@dataclass(frozen=True)
class ReadableSquirrelResult:
    path: Path
    renamed_identifiers: int
    annotated_calls: int
    call_targets: int


def _load_model(case: CaseConfig, layout: BuildLayout) -> dict[str, Any]:
    path = binary_model_path(case, layout)
    if not path.exists():
        return {}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {}
    return data if isinstance(data, dict) else {}


def _unique_name(name: str, used: set[str]) -> str:
    if name not in used:
        used.add(name)
        return name
    index = 2
    while f"{name}_{index}" in used:
        index += 1
    unique = f"{name}_{index}"
    used.add(unique)
    return unique


def _rename_generated_constant(name: str) -> str | None:
    if re.fullmatch(r"s(?:0x)?[0-9A-Fa-f]+", name):
        return "const_" + name[1:]
    if name == "sLittleEndian":
        return "endian_LittleEndian"
    if name == "sBigEndian":
        return "endian_BigEndian"
    if name.startswith("ssy_"):
        return "sym_" + name[4:]
    if name.startswith("schoice_left_"):
        return "choice_left_" + name.removeprefix("schoice_left_")
    return None


def _rename_generated_variable(name: str) -> str | None:
    match = re.fullmatch(r"v([0-9]+)_(.+?)(?:_[0-9]+)?", name)
    if match:
        return readable_symbolic_name(f"{match.group(1)}_{match.group(2)}")

    match = re.fullmatch(r"sy_(.+?)(?:_[0-9]+)?", name)
    if match:
        return "sym_" + match.group(1)

    match = re.fullmatch(r"choice_([0-9]+)(?:_[0-9]+)?", name)
    if match:
        readable = f"choice_{match.group(1)}"
        return None if name == readable else readable

    return None


def _call_value_names(text: str) -> list[str]:
    values: list[str] = []
    seen: set[str] = set()
    process_first = [text.split("process ", 1)[1], text] if "process " in text else [text]
    for segment in process_first:
        for match in re.finditer(r"\bsv[0-9]+_C_Lib\b", segment):
            name = match.group(0)
            if name in seen:
                continue
            seen.add(name)
            values.append(name)
    return values


def _build_rename_map(
    text: str,
    calls: list[CallTarget],
) -> tuple[dict[str, str], dict[str, CallTarget]]:
    tokens = set(_TOKEN_RE.findall(text))
    used = set(tokens)
    rename: dict[str, str] = {}
    call_comments: dict[str, CallTarget] = {}

    for index, original in enumerate(_call_value_names(text)):
        if index < len(calls):
            call = calls[index]
            readable = readable_return_name(call.target, call.callsite)
            readable = _unique_name(readable, used)
            rename[original] = readable
            call_comments[readable] = call
        else:
            readable = _unique_name(original.replace("sv", "ret_stub_", 1), used)
            rename[original] = readable

    for token in sorted(tokens):
        if token in rename:
            continue

        if token.startswith("sv"):
            match = re.fullmatch(r"sv([0-9]+)_MEM", token)
            if match:
                rename[token] = _unique_name(f"mem_snapshot_{match.group(1)}", used)
                continue
            match = re.fullmatch(r"sv([0-9]+)_(.+)", token)
            if match:
                rename[token] = _unique_name(readable_symbolic_name(f"{match.group(1)}_{match.group(2)}"), used)
                continue

        generated_constant = _rename_generated_constant(token)
        if generated_constant is not None:
            rename[token] = _unique_name(generated_constant, used)
            continue

        generated_variable = _rename_generated_variable(token)
        if generated_variable is not None:
            rename[token] = _unique_name(generated_variable, used)

    return rename, call_comments


def _rewrite_tokens(text: str, rename: dict[str, str]) -> str:
    return _TOKEN_RE.sub(lambda match: rename.get(match.group(0), match.group(0)), text)


def _abstract_group(name: str, line: str) -> str:
    if name.startswith("ret_"):
        return "stubbed library-call return values"
    if name.startswith(("sym_", "mem_snapshot_")):
        return "symbolic inputs and memory snapshots"
    if name.startswith(("const_", "endian_", "choice_left_")):
        return "constants and branch tags"
    if "-> message" in line:
        return "operation constructors"
    return "other declarations"


def _group_abstracts(lines: list[str]) -> list[str]:
    before: list[str] = []
    abstracts: list[tuple[str, str]] = []
    after: list[str] = []
    in_abstracts = True

    for line in lines:
        match = re.match(r"abstract\s+([A-Za-z_][A-Za-z0-9_]*)\s*:", line)
        if in_abstracts and match:
            abstracts.append((match.group(1), line))
            continue
        if abstracts:
            in_abstracts = False
            after.append(line)
        else:
            before.append(line)

    if not abstracts:
        return lines

    groups: dict[str, list[str]] = {}
    order = [
        "constants and branch tags",
        "symbolic inputs and memory snapshots",
        "stubbed library-call return values",
        "operation constructors",
        "other declarations",
    ]
    for name, line in abstracts:
        groups.setdefault(_abstract_group(name, line), []).append(line)

    grouped: list[str] = before
    if grouped and grouped[-1].strip():
        grouped.append("")
    for group in order:
        declarations = groups.get(group)
        if not declarations:
            continue
        grouped.append(f"(* {group.capitalize()}. *)")
        grouped.extend(sorted(declarations, key=str.lower))
        grouped.append("")
    while grouped and grouped[-1] == "":
        grouped.pop()
    if after:
        grouped.append("")
        grouped.extend(after)
    return grouped


def _call_comment(call: CallTarget) -> str:
    return f"stubbed call return: {call.target} at {call.callsite_hex}"


def _call_targets_for_model_outputs(model: dict[str, Any], fallback: list[CallTarget]) -> list[CallTarget]:
    fragments = model.get("fragments", []) if isinstance(model, dict) else []
    if not isinstance(fragments, list):
        return fallback

    selected: list[CallTarget] = []
    for fragment in fragments:
        if not isinstance(fragment, dict):
            continue
        sapic = fragment.get("sapic")
        if not isinstance(sapic, str) or sapic.strip() in {"", "0"}:
            continue
        output_count = len(re.findall(r"\bout\([^)]*\b[0-9]+_C_Lib\b", sapic))
        if output_count == 0:
            continue
        readability = fragment.get("readability", {})
        call_targets = readability.get("call_targets", []) if isinstance(readability, dict) else []
        if not isinstance(call_targets, list) or not call_targets:
            continue
        for call in call_targets[-output_count:]:
            if not isinstance(call, dict):
                continue
            callsite = call.get("callsite")
            target = call.get("target")
            if isinstance(callsite, int) and isinstance(target, str):
                selected.append(CallTarget(callsite=callsite, target=target))

    return selected or fallback


def _annotate_process(lines: list[str], call_comments: dict[str, CallTarget], model: dict[str, Any]) -> list[str]:
    fragments = model.get("fragments", []) if isinstance(model, dict) else []
    fragment_count = len(fragments) if isinstance(fragments, list) else 0
    clean_states = 0
    if isinstance(fragments, list):
        for fragment in fragments:
            if isinstance(fragment, dict) and isinstance(fragment.get("assertion_clean_states"), int):
                clean_states += fragment["assertion_clean_states"]

    annotated: list[str] = []
    process_note_written = False
    for line in lines:
        stripped = line.strip()
        indent = line[: len(line) - len(line.lstrip())]
        if stripped.startswith("process ") and not process_note_written:
            annotated.append(line)
            annotated.append(f"{indent}(* Readable aliases preserve the canonical Squirrel process structure. *)")
            if fragment_count:
                annotated.append(
                    f"{indent}(* Binary model summary: {fragment_count} fragment(s), {clean_states} assertion-clean state(s). *)"
                )
            process_note_written = True
            continue

        if re.match(r"if\s+choice_[0-9]+\s*=", stripped):
            annotated.append(f"{indent}(* Nondeterministic branch from Sapic choice; original path predicates stay in the binary model. *)")

        call_match = re.search(r"\bout\([^,]+,\s*(ret_[A-Za-z0-9_]+)\)", stripped)
        if call_match:
            call = call_comments.get(call_match.group(1))
            if call is not None:
                annotated.append(f"{indent}(* {_call_comment(call)}. *)")

        annotated.append(line)

    return annotated


def write_readable_squirrel(case: CaseConfig, layout: BuildLayout, sp_path: Path) -> ReadableSquirrelResult:
    text = sp_path.read_text(encoding="utf-8")
    model = _load_model(case, layout)
    calls = _call_targets_for_model_outputs(model, call_targets_for_fragments(case.input_da, case.fragments))
    rename, call_comments = _build_rename_map(text, calls)
    rewritten = _rewrite_tokens(text, rename)

    header = [
        "(* Readable view generated by CryptoBAP2. *)",
        f"(* Canonical proof artifact: {sp_path.name}. *)",
        "(* Identifier aliases and comments are cosmetic; validation uses the canonical artifact. *)",
        "",
    ]
    lines = header + rewritten.splitlines()
    lines = _group_abstracts(lines)
    lines = _annotate_process(lines, call_comments, model)

    output = layout.squirrel / f"{case.name}.readable.sp"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")
    return ReadableSquirrelResult(
        path=output,
        renamed_identifiers=len(rename),
        annotated_calls=len(call_comments),
        call_targets=len(calls),
    )
