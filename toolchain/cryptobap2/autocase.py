from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path

from .inference import (
    FunctionAnalysis,
    InferenceError,
    default_case_name,
    default_theory_name,
    inferred_case_raw,
    parse_da_function_analysis,
    render_case_yaml,
    sanitize_case_name,
)


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


def _keep_empty_classifications(raw: dict[str, object], warnings: list[str]) -> None:
    raw["functions"] = {"library": [], "adversary": [], "crypto": {}}
    metadata = raw.get("inference")
    if isinstance(metadata, dict):
        metadata["library"] = []
        metadata["adversary"] = []
        metadata["crypto"] = {}
        metadata["classifications"] = []
        metadata["warnings"] = warnings


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
        raw, inference = inferred_case_raw(
            da_path=da_path,
            arch=arch,
            name=case_name,
            theory=case_theory,
            binary_path=binary_path,
            sections=sections or [".text"],
            symbols=symbols,
            max_functions=max_functions,
            infer_crypto=infer_crypto,
            scope=scope,
        )
        warnings = list(inference.warnings)
        if not infer_crypto:
            warnings.append(
                "function classifications are intentionally empty; fill library/adversary/crypto entries before treating the model as security-meaningful"
            )
            _keep_empty_classifications(raw, warnings)
        text = render_case_yaml(raw)
        functions = [_candidate(function) for function in inference.discovered_functions]
        selected = [_candidate(function) for function in inference.selected_functions]
    except InferenceError as exc:
        raise ScaffoldError(str(exc)) from exc
    return ScaffoldedCase(
        text=text,
        output_name=case_name,
        discovered_functions=functions,
        selected_functions=selected,
        warnings=warnings,
    )
