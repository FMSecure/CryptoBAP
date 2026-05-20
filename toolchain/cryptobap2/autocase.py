from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from pathlib import Path

from .inference import (
    FunctionAnalysis,
    InferenceError,
    default_case_name,
    default_theory_name,
    inferred_case_raw,
    looks_internal_symbol,
    looks_local_label,
    parse_da_function_analysis,
    render_case_yaml,
    sanitize_case_name,
)
from .paths import CRYPTOBAP2_ROOT


class ScaffoldError(ValueError):
    pass


@dataclass(frozen=True)
class FunctionCandidate:
    name: str
    entry_label: int
    instruction_labels: list[int]
    exit_labels: list[int]
    end_label: int | None = None
    local_labels: list[str] = field(default_factory=list)


@dataclass(frozen=True)
class ScaffoldedCase:
    text: str
    output_name: str
    discovered_functions: list[FunctionCandidate]
    selected_functions: list[FunctionCandidate]
    warnings: list[str]


def _sanitize_case_name(value: str) -> str:
    return sanitize_case_name(value)


def _looks_internal_symbol(name: str) -> bool:
    return looks_internal_symbol(name)


def _candidate(function: FunctionAnalysis) -> FunctionCandidate:
    return FunctionCandidate(
        name=function.name,
        entry_label=function.entry_label,
        instruction_labels=function.instruction_labels,
        exit_labels=function.exit_labels,
        end_label=function.end_label,
        local_labels=function.local_labels,
    )


def parse_da_functions(path: Path, *, group_local_labels: bool = False) -> list[FunctionCandidate]:
    try:
        return [
            _candidate(function)
            for function in parse_da_function_analysis(path, group_local_labels=group_local_labels)
        ]
    except InferenceError as exc:
        raise ScaffoldError(str(exc)) from exc


def _select_functions(
    functions: list[FunctionCandidate],
    *,
    symbols: list[str] | None,
    max_functions: int,
    scope: str = "auto",
) -> tuple[list[FunctionCandidate], list[str]]:
    try:
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
                if function.instruction_labels and not looks_local_label(function.name)
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
    except InferenceError as exc:
        raise ScaffoldError(str(exc)) from exc


def _yaml_scalar(value: object) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int):
        return str(value)
    return json.dumps(str(value))


def _yaml_inline_list(values: list[object]) -> str:
    if not values:
        return "[]"
    return "[" + ", ".join(_yaml_scalar(value) for value in values) + "]"


def _relative_or_absolute(path: Path) -> str:
    resolved = path.resolve()
    try:
        return str(resolved.relative_to(CRYPTOBAP2_ROOT))
    except ValueError:
        return str(resolved)


def _render_case(
    *,
    name: str,
    description: str,
    arch: str,
    theory: str,
    binary_path: Path | None,
    da_path: Path | None,
    sections: list[str],
    selected: list[FunctionCandidate],
    scope: str = "auto",
) -> str:
    input_symbols = (
        ["*"]
        if scope == "all-functions"
        else [symbol for function in selected for symbol in [function.name, *function.local_labels]]
    )
    lines = [
        "# Generated by cryptobap2 scaffold-case.",
        "# Review fragment boundaries and function classifications before relying on proof results.",
        f"name: {_yaml_scalar(name)}",
        f"description: {_yaml_scalar(description)}",
        f"arch: {_yaml_scalar(arch)}",
        "channel: Channel",
        "input:",
    ]
    if binary_path is not None:
        lines.append(f"  binary: {_yaml_scalar(_relative_or_absolute(binary_path))}")
    if da_path is not None:
        lines.append(f"  da: {_yaml_scalar(_relative_or_absolute(da_path))}")
    lines.extend(
        [
            "  disassembly:",
            "    tool: ghidra",
            f"    sections: {_yaml_inline_list(sections)}",
            f"  theory: {_yaml_scalar(theory)}",
            f"  symbols: {_yaml_inline_list(input_symbols)}",
            "execution:",
            "  fragments:",
        ]
    )
    for function in selected:
        lines.extend(
            [
                f"    - name: {_yaml_scalar(function.name)}",
                f"      entry_label: {function.entry_label}",
                f"      exit_labels: {_yaml_inline_list(function.exit_labels)}",
            ]
        )
        if function.end_label is not None:
            lines.append(f"      end_label: {function.end_label}")
    lines.extend(
        [
            "  extra_variables: []",
            f"  stub_unclassified_calls: {_yaml_scalar(scope == 'all-functions')}",
            "functions:",
            "  library: []",
            "  adversary: []",
            "  crypto: {}",
            "backends: [squirrel]",
            "proof_status:",
            "  hol: generated_unchecked",
            "  sapic: generated_unchecked",
            "  squirrel: generated_unchecked",
            "security_lemmas: []",
            "",
        ]
    )
    return "\n".join(lines)


def scaffold_case_from_da(
    da_path: Path,
    *,
    arch: str,
    name: str | None = None,
    theory: str | None = None,
    binary_path: Path | None = None,
    sections: list[str] | None = None,
    symbols: list[str] | None = None,
    max_functions: int = 16,
    infer_crypto: bool = True,
    scope: str = "auto",
) -> ScaffoldedCase:
    if max_functions < 1:
        raise ScaffoldError("--max-functions must be at least 1")
    case_name = _sanitize_case_name(name or default_case_name(binary_path or da_path))
    case_theory = theory or default_theory_name(case_name)
    try:
        if infer_crypto:
            raw, inference = inferred_case_raw(
                da_path=da_path,
                arch=arch,
                name=case_name,
                theory=case_theory,
                binary_path=binary_path,
                sections=sections or [".text"],
                symbols=symbols,
                max_functions=max_functions,
                infer_crypto=True,
                scope=scope,
            )
            text = render_case_yaml(raw)
            functions = [_candidate(function) for function in inference.discovered_functions]
            selected = [_candidate(function) for function in inference.selected_functions]
            warnings = list(inference.warnings)
        else:
            functions = parse_da_functions(da_path, group_local_labels=True)
            selected, warnings = _select_functions(
                functions,
                symbols=symbols,
                max_functions=max_functions,
                scope=scope,
            )
            warnings.append(
                "function classifications are intentionally empty; fill library/adversary/crypto entries before treating the model as security-meaningful"
            )
            description_source = binary_path or da_path
            text = _render_case(
                name=case_name,
                description=f"Draft case inferred from {description_source.name}.",
                arch=arch,
                theory=case_theory,
                binary_path=binary_path,
                da_path=da_path,
                sections=sections or [".text"],
                selected=selected,
                scope=scope,
            )
    except InferenceError as exc:
        raise ScaffoldError(str(exc)) from exc
    return ScaffoldedCase(
        text=text,
        output_name=case_name,
        discovered_functions=functions,
        selected_functions=selected,
        warnings=warnings,
    )
