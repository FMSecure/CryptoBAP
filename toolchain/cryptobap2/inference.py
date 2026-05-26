from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from .paths import CRYPTOBAP2_ROOT
from .yaml_emit import yaml_inline_list, yaml_scalar


class InferenceError(ValueError):
    pass


@dataclass(frozen=True)
class Instruction:
    label: int
    mnemonic: str
    operands: str
    raw: str
    target_label: int | None = None
    target_name: str | None = None


@dataclass(frozen=True)
class FunctionAnalysis:
    name: str
    entry_label: int
    instructions: list[Instruction]
    exit_labels: list[int]
    end_label: int | None = None
    local_labels: list[str] = field(default_factory=list)
    local_entries: list[int] = field(default_factory=list)

    @property
    def instruction_labels(self) -> list[int]:
        return [instruction.label for instruction in self.instructions]

    @property
    def calls(self) -> list[Instruction]:
        call_mnemonics = {"bl", "blr", "call", "callq"}
        return [instruction for instruction in self.instructions if instruction.mnemonic.lower() in call_mnemonics]


@dataclass(frozen=True)
class CryptoClassification:
    name: str
    label: str
    confidence: str
    reason: str


@dataclass(frozen=True)
class InferenceResult:
    discovered_functions: list[FunctionAnalysis]
    selected_functions: list[FunctionAnalysis]
    library: list[str]
    adversary: list[str]
    crypto: dict[str, str]
    classifications: list[CryptoClassification]
    unresolved: list[str]
    warnings: list[str]
    scope: str = "auto"
    unresolved_count: int = 0

    def as_metadata(self) -> dict[str, Any]:
        selected_symbols = (
            ["*"]
            if self.scope == "all-functions"
            else [function.name for function in self.selected_functions]
        )
        return {
            "engine": "cryptobap2-heuristic-v1",
            "scope": self.scope,
            "discovered_function_count": len(self.discovered_functions),
            "selected_function_count": len(self.selected_functions),
            "selected_symbols": selected_symbols,
            "library": self.library,
            "adversary": self.adversary,
            "crypto": self.crypto,
            "classifications": [
                {
                    "name": item.name,
                    "label": item.label,
                    "confidence": item.confidence,
                    "reason": item.reason,
                }
                for item in self.classifications
            ],
            "unresolved": self.unresolved,
            "unresolved_count": self.unresolved_count or len(self.unresolved),
            "warnings": self.warnings,
        }


_FUNCTION_HEADER_RE = re.compile(r"^([0-9A-Fa-f]+)\s+<([^>]+)>:")
_INSTRUCTION_RE = re.compile(
    r"^\s*([0-9A-Fa-f]+):\s+(?:[0-9A-Fa-f]{2,}\s+)+\s*([A-Za-z_.][A-Za-z0-9_.]*)\b(.*)$"
)
_TARGET_RE = re.compile(r"\b(?:0x)?([0-9A-Fa-f]+)\s+<([^>]+)>")
_PLAIN_TARGET_RE = re.compile(r"(?:^|[\s,])(?:0x)?([0-9A-Fa-f]{2,})(?=\s|,|$)")
_INTERNAL_NAMES = {
    "_start",
    "_dl_relocate_static_pie",
    "call_weak_fn",
    "deregister_tm_clones",
    "register_tm_clones",
    "__do_global_dtors_aux",
    "frame_dummy",
}
_INTERNAL_PREFIXES = ("LAB_", "SUB_", "__libc_", "__gmon_", "__cxa_", "__stack_chk_", "_ITM_")
_LOCAL_LABEL_PREFIXES = ("LAB_", ".L", "loc_")
_ADVERSARY_NAMES = {"recv", "receive", "read", "down_read", "packet_getall"}
_DIRECT_BRANCH_MNEMONICS = {"b", "br", "jmp", "jmpq"}
_TARGET_MNEMONIC_PREFIXES = ("b", "bl", "br", "blr", "cbz", "cbnz", "tbz", "tbnz", "jmp", "call")


def sanitize_case_name(value: str) -> str:
    name = re.sub(r"[^A-Za-z0-9_-]+", "-", value).strip("-_").lower()
    if not name:
        name = "generated-case"
    if not name[0].isalpha():
        name = "case-" + name
    return name


def default_case_name(input_path: Path) -> str:
    stem = input_path.stem if input_path.suffix else input_path.name
    return sanitize_case_name(stem)


def default_theory_name(case_name: str) -> str:
    parts = [part for part in re.split(r"[^A-Za-z0-9]+", case_name) if part]
    theory = "".join(part[:1].upper() + part[1:] for part in parts)
    if not theory:
        theory = "Generated"
    if not theory[0].isalpha():
        theory = "Generated" + theory
    return theory


def looks_internal_symbol(name: str) -> bool:
    return name in _INTERNAL_NAMES or name.startswith(_INTERNAL_PREFIXES)


def looks_local_label(name: str) -> bool:
    return name.startswith(_LOCAL_LABEL_PREFIXES)


def _may_have_code_target(mnemonic: str) -> bool:
    lowered = mnemonic.lower()
    return any(lowered == prefix or lowered.startswith(prefix + ".") for prefix in _TARGET_MNEMONIC_PREFIXES)


def _is_direct_branch(mnemonic: str) -> bool:
    lowered = mnemonic.lower()
    return lowered in _DIRECT_BRANCH_MNEMONICS


def _is_return_instruction(mnemonic: str, line: str) -> bool:
    lowered = mnemonic.lower()
    if lowered in {"ret", "retq", "retn", "eret", "retaa", "retab", "iret", "iretd", "iretq"}:
        return True
    if lowered == "bx" and re.search(r"\blr\b", line, flags=re.IGNORECASE):
        return True
    if lowered.startswith("pop") and re.search(r"\bpc\b", line, flags=re.IGNORECASE):
        return True
    return False


def _parse_instruction(line: str) -> Instruction | None:
    match = _INSTRUCTION_RE.match(line)
    if match is None:
        return None
    label = int(match.group(1), 16)
    mnemonic = match.group(2)
    operands = match.group(3).strip()
    target_label: int | None = None
    target_name: str | None = None
    target = _TARGET_RE.search(operands)
    if target:
        target_label = int(target.group(1), 16)
        target_name = target.group(2)
    elif _may_have_code_target(mnemonic):
        plain_target = _PLAIN_TARGET_RE.search(operands)
        if plain_target is not None:
            target_label = int(plain_target.group(1), 16)
    return Instruction(
        label=label,
        mnemonic=mnemonic,
        operands=operands,
        raw=line,
        target_label=target_label,
        target_name=target_name,
    )


def _in_function_range(label: int, *, entry_label: int, end_label: int | None) -> bool:
    if label < entry_label:
        return False
    return end_label is None or label < end_label


def _infer_exit_labels(
    *,
    entry_label: int,
    instructions: list[Instruction],
    local_blocks: dict[int, list[Instruction]],
    end_label: int | None,
) -> list[int]:
    exits: set[int] = {
        instruction.label
        for instruction in instructions
        if _is_return_instruction(instruction.mnemonic, instruction.raw)
    }
    for instruction in instructions:
        if (
            instruction.target_label is not None
            and _is_direct_branch(instruction.mnemonic)
            and not _in_function_range(instruction.target_label, entry_label=entry_label, end_label=end_label)
        ):
            exits.add(instruction.label)
    for local_entry, block in local_blocks.items():
        if any(
            instruction.target_label == entry_label and _is_direct_branch(instruction.mnemonic)
            for instruction in block
        ):
            exits.add(local_entry)
    return sorted(exits)


def parse_da_function_analysis(path: Path, *, group_local_labels: bool = False) -> list[FunctionAnalysis]:
    if not path.exists():
        raise InferenceError(f"disassembly does not exist: {path}")
    functions: list[FunctionAnalysis] = []
    current_name: str | None = None
    current_entry: int | None = None
    instructions: list[Instruction] = []
    exit_labels: list[int] = []
    local_labels: list[str] = []
    local_entries: list[int] = []
    local_blocks: dict[int, list[Instruction]] = {}
    current_local_entry: int | None = None

    def flush(end_label: int | None = None) -> None:
        nonlocal current_name, current_entry, instructions, exit_labels
        nonlocal local_labels, local_entries, local_blocks, current_local_entry
        if current_name is not None and current_entry is not None:
            inferred_end = end_label
            if inferred_end is None and instructions:
                inferred_end = instructions[-1].label + 1
            exits = (
                _infer_exit_labels(
                    entry_label=current_entry,
                    instructions=instructions,
                    local_blocks=local_blocks,
                    end_label=inferred_end,
                )
                if group_local_labels
                else sorted(set(exit_labels))
            )
            functions.append(
                FunctionAnalysis(
                    name=current_name,
                    entry_label=current_entry,
                    instructions=instructions,
                    exit_labels=exits,
                    end_label=inferred_end,
                    local_labels=local_labels,
                    local_entries=local_entries,
                )
            )
        current_name = None
        current_entry = None
        instructions = []
        exit_labels = []
        local_labels = []
        local_entries = []
        local_blocks = {}
        current_local_entry = None

    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        header = _FUNCTION_HEADER_RE.match(line.strip())
        if header:
            entry = int(header.group(1), 16)
            name = header.group(2)
            if group_local_labels and current_name is not None and looks_local_label(name):
                local_labels.append(name)
                local_entries.append(entry)
                local_blocks.setdefault(entry, [])
                current_local_entry = entry
                continue
            flush(entry)
            current_entry = entry
            current_name = name
            current_local_entry = None
            continue
        if current_name is None:
            continue
        instruction = _parse_instruction(line)
        if instruction is None:
            continue
        instructions.append(instruction)
        if group_local_labels and current_local_entry is not None:
            local_blocks.setdefault(current_local_entry, []).append(instruction)
        if _is_return_instruction(instruction.mnemonic, line):
            exit_labels.append(instruction.label)
    flush()
    return functions


def select_functions(
    functions: list[FunctionAnalysis],
    *,
    symbols: list[str] | None,
    max_functions: int,
    scope: str = "auto",
) -> tuple[list[FunctionAnalysis], list[str]]:
    warnings: list[str] = []
    if symbols == ["*"]:
        symbols = None
        scope = "all-functions"
    if scope not in {"auto", "all-functions"}:
        raise InferenceError(f"unknown inference scope: {scope}")
    by_name = {function.name: function for function in functions}
    if scope == "all-functions":
        selected = [
            function
            for function in functions
            if function.instructions and not looks_local_label(function.name)
        ]
        if not selected:
            raise InferenceError("no function regions were found in the disassembly")
        return selected, warnings
    if symbols:
        missing = [symbol for symbol in symbols if symbol not in by_name]
        if missing:
            raise InferenceError(
                "requested symbol(s) not found in disassembly: " + ", ".join(sorted(missing))
            )
        selected = [by_name[symbol] for symbol in symbols]
    else:
        candidates = [
            function
            for function in functions
            if function.exit_labels and not looks_internal_symbol(function.name)
        ]
        if not candidates:
            candidates = [function for function in functions if function.exit_labels]
        selected = candidates[:max_functions]
        if len(candidates) > max_functions:
            warnings.append(
                f"selected the first {max_functions} return-like functions out of {len(candidates)}; pass --symbols to choose explicitly"
            )
    if not selected:
        raise InferenceError("no return-like functions were found; pass --symbols after inspecting the .da file")
    for function in selected:
        if not function.exit_labels:
            warnings.append(
                f"{function.name} has no return-like instruction; its fragment has no inferred exit labels"
            )
    return selected, warnings


def _has_mnemonic(function: FunctionAnalysis, mnemonics: set[str]) -> bool:
    return any(instruction.mnemonic.lower() in mnemonics for instruction in function.instructions)


def _looks_like_small_generator(function: FunctionAnalysis) -> bool:
    body_mnemonics = [
        instruction.mnemonic.lower()
        for instruction in function.instructions
        if instruction.mnemonic.lower() not in {"nop", "ret", "retq", "retn"}
    ]
    return len(function.instructions) <= 4 and not function.calls and all(
        mnemonic in {"mov", "movz", "movk", "adrp", "add"} for mnemonic in body_mnemonics
    )


def _classify_crypto(function: FunctionAnalysis) -> CryptoClassification | None:
    lowered = function.name.lower()
    if _has_mnemonic(function, {"eor", "xor"}) or re.search(r"(^|[_./:-])(xor|senc|protect|mix)($|[_./:-])", lowered):
        return CryptoClassification(function.name, "XOR", "high", "function body or name matches XOR-style operation")
    if re.search(r"(^|[_./:-])(send|output|write|memcpy|copy)($|[_./:-])", lowered):
        return CryptoClassification(function.name, "MEMcpy", "medium", "function name matches send/copy-style operation")
    if (
        re.search(r"(^|[_./:-])(new_key|client_key|server_key|keygen|otp)($|[_./:-])", lowered)
        or re.search(r"(^|[_./:-]).*key$", lowered)
    ) and _looks_like_small_generator(function):
        return CryptoClassification(function.name, "OTP", "medium", "function name and small body match key-generation operation")
    if re.search(r"(^|[_./:-])(encrypt|enc)($|[_./:-])", lowered):
        return CryptoClassification(function.name, "Encryption", "low", "function name matches encryption operation")
    if re.search(r"(^|[_./:-])(decrypt|dec)($|[_./:-])", lowered):
        return CryptoClassification(function.name, "Decryption", "low", "function name matches decryption operation")
    if re.search(r"(^|[_./:-])sign($|[_./:-])", lowered):
        return CryptoClassification(function.name, "Signature", "low", "function name matches signature operation")
    if re.search(r"(^|[_./:-])verify($|[_./:-])", lowered):
        return CryptoClassification(function.name, "Verify", "low", "function name matches verification operation")
    if re.search(r"(^|[_./:-])(rng|random|nonce)($|[_./:-])", lowered):
        return CryptoClassification(function.name, "RNG", "low", "function name matches random/nonce operation")
    return None


def infer_functions(
    da_path: Path,
    *,
    symbols: list[str] | None,
    max_functions: int,
    infer_crypto: bool = True,
    scope: str = "auto",
) -> InferenceResult:
    if max_functions < 1:
        raise InferenceError("--max-functions must be at least 1")
    effective_scope = "all-functions" if symbols == ["*"] or scope == "all-functions" else "auto"
    discovered = parse_da_function_analysis(
        da_path,
        group_local_labels=True,
    )
    selected, warnings = select_functions(
        discovered,
        symbols=symbols,
        max_functions=max_functions,
        scope=effective_scope,
    )
    selected_names = {function.name for function in selected}
    classifications: list[CryptoClassification] = []
    unresolved: list[str] = []
    adversary = sorted({function.name for function in selected if function.name in _ADVERSARY_NAMES} | {"recv"})

    if infer_crypto:
        for function in selected:
            call_targets = {call.target_name for call in function.calls if call.target_name is not None}
            is_composition_root = function.name == "main" or bool(call_targets & selected_names)
            if function.name in _ADVERSARY_NAMES or is_composition_root:
                continue
            classification = _classify_crypto(function)
            if classification is None:
                unresolved.append(function.name)
            else:
                classifications.append(classification)
    else:
        unresolved = [
            function.name
            for function in selected
            if function.name not in _ADVERSARY_NAMES and function.name != "main"
        ]

    crypto = {classification.name: classification.label for classification in classifications}
    library = [function.name for function in selected if function.name in crypto]
    unresolved_count = len(unresolved)
    if unresolved and effective_scope == "all-functions":
        warnings.append(
            f"could not infer crypto labels for {unresolved_count} function(s); "
            "unclassified out-of-fragment calls will be summarized as C_Lib"
        )
        unresolved = sorted(unresolved)[:50]
    elif unresolved:
        warnings.append(
            "could not infer crypto labels for: " + ", ".join(sorted(unresolved))
        )
    return InferenceResult(
        discovered_functions=discovered,
        selected_functions=selected,
        library=library,
        adversary=adversary,
        crypto=crypto,
        classifications=classifications,
        unresolved=sorted(unresolved),
        warnings=warnings,
        scope=effective_scope,
        unresolved_count=unresolved_count,
    )


def _relative_or_absolute(path: Path) -> str:
    resolved = path.resolve()
    try:
        return str(resolved.relative_to(CRYPTOBAP2_ROOT))
    except ValueError:
        return str(resolved)


def _infer_extra_variables(crypto: dict[str, str], existing: list[dict[str, Any]] | None = None) -> list[dict[str, Any]]:
    extra = list(existing or [])
    names = {str(item.get("name")) for item in extra if isinstance(item, dict)}
    needs_key = any(label in {"XOR", "Encryption", "Decryption"} for label in crypto.values())
    if needs_key and "key" not in names:
        extra.append({"name": "key", "type": "Imm", "width": 64})
    return extra


def inferred_case_raw(
    *,
    da_path: Path,
    arch: str,
    name: str,
    theory: str,
    binary_path: Path | None,
    sections: list[str],
    symbols: list[str] | None,
    max_functions: int,
    infer_crypto: bool = True,
    scope: str = "auto",
) -> tuple[dict[str, Any], InferenceResult]:
    inference = infer_functions(
        da_path,
        symbols=symbols,
        max_functions=max_functions,
        infer_crypto=infer_crypto,
        scope=scope,
    )
    selected = inference.selected_functions
    selected_names = {function.name for function in selected}
    has_out_of_selection_calls = any(
        call.target_name is not None and call.target_name not in selected_names
        for function in selected
        for call in function.calls
    )
    input_symbols = ["*"] if inference.scope == "all-functions" else [
        symbol
        for function in selected
        for symbol in [function.name, *function.local_labels]
    ]
    raw: dict[str, Any] = {
        "name": name,
        "description": f"Draft case inferred from {(binary_path or da_path).name}.",
        "arch": arch,
        "channel": "Channel",
        "input": {
            "disassembly": {"tool": "ghidra", "sections": sections},
            "theory": theory,
            "symbols": input_symbols,
        },
        "execution": {
            "fragments": [
                {
                    key: value
                    for key, value in {
                        "name": function.name,
                        "entry_label": function.entry_label,
                        "exit_labels": function.exit_labels,
                        "end_label": function.end_label,
                    }.items()
                    if value is not None
                }
                for function in selected
            ],
            "extra_variables": _infer_extra_variables(inference.crypto),
            "stub_unclassified_calls": inference.scope == "all-functions" or has_out_of_selection_calls,
        },
        "functions": {
            "library": inference.library,
            "adversary": inference.adversary,
            "crypto": inference.crypto,
        },
        "backends": ["squirrel"],
        "proof_status": {
            "hol": "generated_unchecked",
            "sapic": "generated_unchecked",
            "squirrel": "generated_unchecked",
        },
        "security_lemmas": [],
        "inference": inference.as_metadata(),
    }
    if binary_path is not None:
        raw["input"]["binary"] = _relative_or_absolute(binary_path)
    if da_path is not None:
        raw["input"]["da"] = _relative_or_absolute(da_path)
    return raw, inference


def _has_fragments(raw: dict[str, Any]) -> bool:
    execution = raw.get("execution", {})
    if not isinstance(execution, dict):
        return False
    fragments = execution.get("fragments")
    return bool(fragments) or "entry_label" in execution


def _has_symbols(raw: dict[str, Any]) -> bool:
    input_block = raw.get("input", {})
    if not isinstance(input_block, dict):
        return False
    symbols = input_block.get("symbols")
    return isinstance(symbols, list) and bool(symbols)


def case_needs_inference(raw: dict[str, Any]) -> bool:
    if not _has_symbols(raw) or not _has_fragments(raw):
        return True
    functions = raw.get("functions")
    return not isinstance(functions, dict)


def _merge_inferred_symbols(existing: Any, inferred: Any) -> Any:
    if existing is None or existing == []:
        return inferred if isinstance(inferred, list) else []
    if not isinstance(existing, list) or not isinstance(inferred, list):
        return existing
    if "*" in existing or "*" in inferred:
        return ["*"]
    merged = list(existing)
    for symbol in inferred:
        if symbol not in merged:
            merged.append(symbol)
    return merged


def merge_missing_inferred_fields(base_raw: dict[str, Any], inferred_raw: dict[str, Any]) -> dict[str, Any]:
    raw = json.loads(json.dumps(base_raw, sort_keys=True, default=str))
    raw.setdefault("name", inferred_raw["name"])
    raw.setdefault("description", inferred_raw["description"])
    raw.setdefault("arch", inferred_raw["arch"])
    raw.setdefault("channel", inferred_raw["channel"])
    raw.setdefault("backends", inferred_raw["backends"])
    raw.setdefault("proof_status", inferred_raw["proof_status"])
    raw.setdefault("security_lemmas", inferred_raw["security_lemmas"])

    input_block = raw.setdefault("input", {})
    if not isinstance(input_block, dict):
        input_block = {}
        raw["input"] = input_block
    inferred_input = inferred_raw["input"]
    input_block.setdefault("binary", inferred_input.get("binary"))
    input_block.setdefault("da", inferred_input.get("da"))
    input_block.setdefault("disassembly", inferred_input.get("disassembly"))
    input_block.setdefault("theory", inferred_input.get("theory"))
    input_block["symbols"] = _merge_inferred_symbols(input_block.get("symbols"), inferred_input.get("symbols", []))

    execution = raw.setdefault("execution", {})
    if not isinstance(execution, dict):
        execution = {}
        raw["execution"] = execution
    if not _has_fragments(raw):
        execution["fragments"] = inferred_raw["execution"]["fragments"]
    if "extra_variables" not in execution:
        execution["extra_variables"] = inferred_raw["execution"].get("extra_variables", [])
    if "stub_unclassified_calls" not in execution and "stub_unclassified_calls" in inferred_raw["execution"]:
        execution["stub_unclassified_calls"] = inferred_raw["execution"]["stub_unclassified_calls"]

    functions = raw.setdefault("functions", {})
    if not isinstance(functions, dict):
        functions = {}
        raw["functions"] = functions
    inferred_functions = inferred_raw["functions"]
    for key in ("library", "adversary", "crypto"):
        if key not in functions:
            functions[key] = inferred_functions.get(key, {} if key == "crypto" else [])

    raw["inference"] = inferred_raw.get("inference", {})
    return raw


def _render_extra_variables(extra_variables: list[dict[str, Any]]) -> list[str]:
    if not extra_variables:
        return ["    []"]
    lines: list[str] = []
    for variable in extra_variables:
        lines.extend(
            [
                f"    - name: {yaml_scalar(variable.get('name', ''))}",
                f"      type: {yaml_scalar(variable.get('type', 'Imm'))}",
                f"      width: {int(variable.get('width', 64))}",
            ]
        )
    return lines


def _render_inference(metadata: dict[str, Any]) -> list[str]:
    if not metadata:
        return []
    lines = [
        "inference:",
        f"  engine: {yaml_scalar(metadata.get('engine', 'cryptobap2-heuristic-v1'))}",
        f"  scope: {yaml_scalar(metadata.get('scope', 'auto'))}",
        f"  discovered_function_count: {int(metadata.get('discovered_function_count', 0))}",
        f"  selected_function_count: {int(metadata.get('selected_function_count', 0))}",
        f"  selected_symbols: {yaml_inline_list(list(metadata.get('selected_symbols', [])))}",
        f"  library: {yaml_inline_list(list(metadata.get('library', [])))}",
        f"  adversary: {yaml_inline_list(list(metadata.get('adversary', [])))}",
        "  crypto:",
    ]
    crypto = metadata.get("crypto", {})
    if isinstance(crypto, dict) and crypto:
        for name, label in sorted(crypto.items()):
            lines.append(f"    {yaml_scalar(name)}: {yaml_scalar(label)}")
    else:
        lines.append("    {}")
    classifications = metadata.get("classifications", [])
    lines.append("  classifications:")
    if classifications:
        for item in classifications:
            if not isinstance(item, dict):
                continue
            lines.extend(
                [
                    f"    - name: {yaml_scalar(item.get('name', ''))}",
                    f"      label: {yaml_scalar(item.get('label', ''))}",
                    f"      confidence: {yaml_scalar(item.get('confidence', ''))}",
                    f"      reason: {yaml_scalar(item.get('reason', ''))}",
                ]
            )
    else:
        lines.append("    []")
    lines.append(f"  unresolved: {yaml_inline_list(list(metadata.get('unresolved', [])))}")
    lines.append(f"  unresolved_count: {int(metadata.get('unresolved_count', 0))}")
    lines.append(f"  warnings: {yaml_inline_list(list(metadata.get('warnings', [])))}")
    return lines


def _render_bool_field(execution: dict[str, Any], name: str) -> str:
    value = execution.get(name)
    if not isinstance(value, bool):
        raise ValueError(f"execution.{name} must be a boolean")
    return yaml_scalar(value)


def render_case_yaml(raw: dict[str, Any]) -> str:
    input_block = raw.get("input", {}) if isinstance(raw.get("input"), dict) else {}
    execution = raw.get("execution", {}) if isinstance(raw.get("execution"), dict) else {}
    functions = raw.get("functions", {}) if isinstance(raw.get("functions"), dict) else {}
    proof_status = raw.get("proof_status", {}) if isinstance(raw.get("proof_status"), dict) else {}
    fragments = execution.get("fragments", [])
    if not isinstance(fragments, list) or not fragments:
        fragments = []
        if "entry_label" in execution:
            fragments = [
                {
                    "name": "main",
                    "entry_label": execution.get("entry_label", 0),
                    "exit_labels": execution.get("exit_labels", []),
                }
            ]
    lines = [
        "# Generated by cryptobap2 inference.",
        "# Review inferred fragment boundaries and function classifications before relying on proof results.",
        f"name: {yaml_scalar(raw.get('name', 'generated-case'))}",
        f"description: {yaml_scalar(raw.get('description', 'Draft case inferred from binary input.'))}",
        f"arch: {yaml_scalar(raw.get('arch', 'arm8'))}",
        f"channel: {yaml_scalar(raw.get('channel', 'Channel'))}",
        "input:",
    ]
    if input_block.get("binary"):
        lines.append(f"  binary: {yaml_scalar(input_block['binary'])}")
    if input_block.get("da"):
        lines.append(f"  da: {yaml_scalar(input_block['da'])}")
    disassembly = input_block.get("disassembly", {})
    sections = [".text"]
    if isinstance(disassembly, dict):
        sections = [str(section) for section in disassembly.get("sections", [".text"])]
    lines.extend(
        [
            "  disassembly:",
            "    tool: ghidra",
            f"    sections: {yaml_inline_list(sections)}",
            f"  theory: {yaml_scalar(input_block.get('theory', raw.get('name', 'Generated')))}",
            f"  symbols: {yaml_inline_list([str(item) for item in input_block.get('symbols', [])])}",
            "execution:",
            "  fragments:",
        ]
    )
    for fragment in fragments:
        if not isinstance(fragment, dict):
            continue
        lines.extend(
            [
                f"    - name: {yaml_scalar(fragment.get('name', 'fragment'))}",
                f"      entry_label: {int(fragment.get('entry_label', 0))}",
                f"      exit_labels: {yaml_inline_list([int(item) for item in fragment.get('exit_labels', [])])}",
            ]
        )
        if fragment.get("end_label") is not None:
            lines.append(f"      end_label: {int(fragment.get('end_label', 0))}")
    lines.append("  extra_variables:")
    lines.extend(_render_extra_variables(execution.get("extra_variables", [])))
    if "stub_unclassified_calls" in execution:
        lines.append(f"  stub_unclassified_calls: {_render_bool_field(execution, 'stub_unclassified_calls')}")
    if "allow_unmapped_memory_overapprox" in execution:
        lines.append(
            "  allow_unmapped_memory_overapprox: "
            f"{_render_bool_field(execution, 'allow_unmapped_memory_overapprox')}"
        )
    lines.extend(
        [
            "functions:",
            f"  library: {yaml_inline_list([str(item) for item in functions.get('library', [])])}",
            f"  adversary: {yaml_inline_list([str(item) for item in functions.get('adversary', [])])}",
            "  crypto:",
        ]
    )
    crypto = functions.get("crypto", {})
    if isinstance(crypto, dict) and crypto:
        for name, label in sorted(crypto.items()):
            lines.append(f"    {yaml_scalar(name)}: {yaml_scalar(label)}")
    else:
        lines.append("    {}")
    lines.extend(
        [
            f"backends: {yaml_inline_list([str(item) for item in raw.get('backends', ['squirrel'])])}",
            "proof_status:",
        ]
    )
    if proof_status:
        for name, status in sorted(proof_status.items()):
            lines.append(f"  {yaml_scalar(name)}: {yaml_scalar(status)}")
    else:
        lines.append("  {}")
    lines.append(f"security_lemmas: {yaml_inline_list([str(item) for item in raw.get('security_lemmas', [])])}")
    lines.extend(_render_inference(raw.get("inference", {})))
    lines.append("")
    return "\n".join(lines)
