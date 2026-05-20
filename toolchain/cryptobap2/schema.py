from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any


VALID_BACKENDS = {"tamarin", "squirrel"}
VALID_PROOF_STATUSES = {
    "configured",
    "proved",
    "generated_unchecked",
    "backend_partial",
    "contains_cheat",
    "contains_sorry",
    "validation_failed",
    "stale",
    "missing",
}
VALID_STATUS_VALUES = VALID_PROOF_STATUSES | {"ok"}


@dataclass(frozen=True)
class SchemaDiagnostic:
    severity: str
    code: str
    message: str
    field: str

    def as_dict(self) -> dict[str, str]:
        return {
            "severity": self.severity,
            "code": self.code,
            "message": self.message,
            "field": self.field,
        }


def _diag(code: str, message: str, field: str) -> SchemaDiagnostic:
    return SchemaDiagnostic("error", code, message, field)


def _is_nonempty_string(value: Any) -> bool:
    return isinstance(value, str) and value.strip() != ""


def _validate_string_list(raw: dict[str, Any], key: str, field: str) -> list[SchemaDiagnostic]:
    value = raw.get(key, [])
    if not isinstance(value, list):
        return [_diag("bad_type", f"{field} must be a list", field)]
    diagnostics: list[SchemaDiagnostic] = []
    for index, item in enumerate(value):
        if not _is_nonempty_string(item):
            diagnostics.append(_diag("bad_type", f"{field}[{index}] must be a non-empty string", f"{field}[{index}]"))
    return diagnostics


def _is_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def _validate_extra_variables(execution: dict[str, Any]) -> list[SchemaDiagnostic]:
    if "extra_variables" not in execution:
        return []
    value = execution.get("extra_variables")
    if not isinstance(value, list):
        return [_diag("bad_type", "execution.extra_variables must be a list", "execution.extra_variables")]
    diagnostics: list[SchemaDiagnostic] = []
    for index, variable in enumerate(value):
        field = f"execution.extra_variables[{index}]"
        if not isinstance(variable, dict):
            diagnostics.append(_diag("bad_type", "extra variable must be a mapping", field))
            continue
        if not _is_nonempty_string(variable.get("name")):
            diagnostics.append(_diag("bad_type", "extra variable name must be a non-empty string", f"{field}.name"))
        typ = variable.get("type", "Imm")
        if not _is_nonempty_string(typ) or str(typ).lower() not in {"imm", "mem"}:
            diagnostics.append(_diag("bad_type", "extra variable type must be 'Imm' or 'Mem'", f"{field}.type"))
        if not _is_int(variable.get("width", 64)):
            diagnostics.append(_diag("bad_type", "extra variable width must be an integer", f"{field}.width"))
        for width_key in ("cell_width", "value_width"):
            if width_key in variable and not _is_int(variable[width_key]):
                diagnostics.append(
                    _diag("bad_type", f"extra variable {width_key} must be an integer", f"{field}.{width_key}")
                )
    return diagnostics


def validate_case_schema(raw: dict[str, Any], *, path: Path | None = None) -> list[SchemaDiagnostic]:
    diagnostics: list[SchemaDiagnostic] = []
    if not isinstance(raw, dict):
        return [_diag("bad_type", "case file must contain a YAML mapping", "$")]

    name = raw.get("name")
    if not _is_nonempty_string(name):
        diagnostics.append(_diag("missing_field", "name must be a non-empty string", "name"))
    elif not re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]*", str(name)):
        diagnostics.append(
            _diag(
                "bad_name",
                "name must start with a letter and contain only letters, digits, '_' or '-'",
                "name",
            )
        )

    arch = raw.get("arch", "arm8")
    if not _is_nonempty_string(arch):
        diagnostics.append(_diag("missing_field", "arch must be a non-empty string", "arch"))

    input_block = raw.get("input")
    if not isinstance(input_block, dict):
        diagnostics.append(_diag("missing_field", "input must be a mapping", "input"))
        input_block = {}
    for key in ("da", "binary", "theory"):
        if key in input_block and input_block[key] is not None and not _is_nonempty_string(input_block[key]):
            diagnostics.append(_diag("bad_type", f"input.{key} must be a non-empty string", f"input.{key}"))
    disassembly = input_block.get("disassembly", {})
    if disassembly != {} and not isinstance(disassembly, dict):
        diagnostics.append(_diag("bad_type", "input.disassembly must be a mapping", "input.disassembly"))
    elif isinstance(disassembly, dict):
        tool = disassembly.get("tool", "ghidra")
        if tool != "ghidra":
            diagnostics.append(_diag("bad_disassembly_tool", "input.disassembly.tool must be 'ghidra'", "input.disassembly.tool"))
        sections = disassembly.get("sections", [".text"])
        if not isinstance(sections, list) or not sections:
            diagnostics.append(
                _diag("bad_type", "input.disassembly.sections must be a non-empty list", "input.disassembly.sections")
            )
        else:
            for index, section in enumerate(sections):
                if not _is_nonempty_string(section):
                    diagnostics.append(
                        _diag(
                            "bad_type",
                            "input.disassembly.sections entries must be non-empty strings",
                            f"input.disassembly.sections[{index}]",
                        )
                    )
    symbols = input_block.get("symbols", [])
    if not isinstance(symbols, list) or not symbols:
        diagnostics.append(_diag("missing_symbol", "input.symbols must be a non-empty list", "input.symbols"))
    else:
        for index, symbol in enumerate(symbols):
            if not _is_nonempty_string(symbol):
                diagnostics.append(
                    _diag("bad_symbol", "input.symbols entries must be non-empty strings", f"input.symbols[{index}]")
                )

    execution = raw.get("execution")
    if not isinstance(execution, dict):
        diagnostics.append(_diag("missing_field", "execution must be a mapping", "execution"))
        execution = {}
    if (
        "allow_unmapped_memory_overapprox" in execution
        and not isinstance(execution["allow_unmapped_memory_overapprox"], bool)
    ):
        diagnostics.append(
            _diag(
                "bad_type",
                "execution.allow_unmapped_memory_overapprox must be a boolean",
                "execution.allow_unmapped_memory_overapprox",
            )
        )
    if "stub_unclassified_calls" in execution and not isinstance(execution["stub_unclassified_calls"], bool):
        diagnostics.append(
            _diag(
                "bad_type",
                "execution.stub_unclassified_calls must be a boolean",
                "execution.stub_unclassified_calls",
            )
        )
    diagnostics.extend(_validate_extra_variables(execution))

    fragments = execution.get("fragments")
    if fragments is None:
        if "entry_label" not in execution:
            diagnostics.append(
                _diag("missing_label", "execution requires entry_label or execution.fragments", "execution")
            )
        elif not _is_int(execution.get("entry_label")):
            diagnostics.append(_diag("bad_label", "execution.entry_label must be an integer", "execution.entry_label"))
        exits = execution.get("exit_labels", [])
        if not isinstance(exits, list) or not all(_is_int(item) for item in exits):
            diagnostics.append(
                _diag("bad_label", "execution.exit_labels must be a list of integers", "execution.exit_labels")
            )
    elif not isinstance(fragments, list) or not fragments:
        diagnostics.append(_diag("bad_fragment", "execution.fragments must be a non-empty list", "execution.fragments"))
    else:
        for index, fragment in enumerate(fragments):
            field = f"execution.fragments[{index}]"
            if not isinstance(fragment, dict):
                diagnostics.append(_diag("bad_fragment", "fragment must be a mapping", field))
                continue
            if not _is_nonempty_string(fragment.get("name", "fragment")):
                diagnostics.append(_diag("bad_fragment", "fragment.name must be a non-empty string", f"{field}.name"))
            if not _is_int(fragment.get("entry_label")):
                diagnostics.append(_diag("bad_label", "fragment.entry_label must be an integer", f"{field}.entry_label"))
            if "end_label" in fragment and fragment["end_label"] is not None and not _is_int(fragment["end_label"]):
                diagnostics.append(_diag("bad_label", "fragment.end_label must be an integer", f"{field}.end_label"))
            exits = fragment.get("exit_labels", [])
            if not isinstance(exits, list) or not all(_is_int(item) for item in exits):
                diagnostics.append(
                    _diag("bad_label", "fragment.exit_labels must be a list of integers", f"{field}.exit_labels")
                )

    functions = raw.get("functions", {})
    if functions != {} and not isinstance(functions, dict):
        diagnostics.append(_diag("bad_type", "functions must be a mapping", "functions"))
        functions = {}
    if isinstance(functions, dict):
        diagnostics.extend(_validate_string_list(functions, "library", "functions.library"))
        diagnostics.extend(_validate_string_list(functions, "adversary", "functions.adversary"))
        crypto = functions.get("crypto", {})
        if crypto != {} and not isinstance(crypto, dict):
            diagnostics.append(_diag("bad_type", "functions.crypto must be a mapping", "functions.crypto"))
        elif isinstance(crypto, dict):
            for key, value in crypto.items():
                if not _is_nonempty_string(key) or not _is_nonempty_string(value):
                    diagnostics.append(
                        _diag("bad_type", "functions.crypto keys and values must be non-empty strings", "functions.crypto")
                    )

    artifacts = raw.get("artifacts", {})
    if artifacts != {} and not isinstance(artifacts, dict):
        diagnostics.append(_diag("bad_type", "artifacts must be a mapping", "artifacts"))

    backends = raw.get("backends", ["squirrel"])
    if not isinstance(backends, list) or not backends:
        diagnostics.append(_diag("bad_backend", "backends must be a non-empty list", "backends"))
    else:
        for index, backend in enumerate(backends):
            if backend not in VALID_BACKENDS:
                diagnostics.append(
                    _diag(
                        "bad_backend",
                        f"unknown backend {backend!r}; expected one of {', '.join(sorted(VALID_BACKENDS))}",
                        f"backends[{index}]",
                    )
                )

    proof_status = raw.get("proof_status", {})
    if proof_status != {} and not isinstance(proof_status, dict):
        diagnostics.append(_diag("bad_status", "proof_status must be a mapping", "proof_status"))
    elif isinstance(proof_status, dict):
        for key, value in proof_status.items():
            if value not in VALID_PROOF_STATUSES:
                diagnostics.append(
                    _diag(
                        "bad_status",
                        f"proof_status.{key} has unknown status {value!r}",
                        f"proof_status.{key}",
                    )
                )

    lemmas = raw.get("security_lemmas", [])
    if not isinstance(lemmas, list):
        diagnostics.append(_diag("bad_type", "security_lemmas must be a list", "security_lemmas"))
    else:
        for index, lemma in enumerate(lemmas):
            if not _is_nonempty_string(lemma):
                diagnostics.append(
                    _diag("bad_type", "security_lemmas entries must be non-empty strings", f"security_lemmas[{index}]")
                )

    return diagnostics
