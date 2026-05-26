from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from .config import CaseConfig
from .manifest import BuildLayout, sha256_file
from .readability import (
    call_targets_for_fragment,
    parse_da_call_targets,
    readable_return_name,
    readable_symbolic_name,
)


BINARY_MODEL_SCHEMA = "cryptobap2-binary-model-v1"


def binary_model_path(case: CaseConfig, layout: BuildLayout) -> Path:
    return layout.model / f"{case.name}.binary-model.json"


def _diag(code: str, message: str, field: str, *, severity: str = "error") -> dict[str, str]:
    return {
        "severity": severity,
        "code": code,
        "message": message,
        "field": field,
    }


def _is_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def _is_int_list(value: Any) -> bool:
    return isinstance(value, list) and all(_is_int(item) for item in value)


def validate_binary_model_data(data: Any) -> list[dict[str, str]]:
    diagnostics: list[dict[str, str]] = []
    if not isinstance(data, dict):
        return [_diag("bad_model", "binary model must be a JSON object", "$")]

    if data.get("schema") != BINARY_MODEL_SCHEMA:
        diagnostics.append(
            _diag(
                "bad_model_schema",
                f"binary model schema must be {BINARY_MODEL_SCHEMA!r}",
                "schema",
            )
        )

    fragments = data.get("fragments")
    if not isinstance(fragments, list) or not fragments:
        diagnostics.append(_diag("bad_model_fragments", "fragments must be a non-empty list", "fragments"))
        return diagnostics

    for index, fragment in enumerate(fragments):
        field = f"fragments[{index}]"
        if not isinstance(fragment, dict):
            diagnostics.append(_diag("bad_model_fragment", "fragment must be an object", field))
            continue
        if not isinstance(fragment.get("name"), str) or fragment.get("name") == "":
            diagnostics.append(_diag("bad_model_fragment", "fragment.name must be a non-empty string", f"{field}.name"))
        if not _is_int(fragment.get("entry_label")):
            diagnostics.append(_diag("bad_model_fragment", "fragment.entry_label must be an integer", f"{field}.entry_label"))
        if not _is_int_list(fragment.get("exit_labels")):
            diagnostics.append(
                _diag("bad_model_fragment", "fragment.exit_labels must be a list of integers", f"{field}.exit_labels")
            )
        for key in ("total_states", "assertion_clean_states"):
            if key in fragment and not _is_int(fragment[key]):
                diagnostics.append(_diag("bad_model_fragment", f"fragment.{key} must be an integer", f"{field}.{key}"))
        if "path_predicates" in fragment and not isinstance(fragment["path_predicates"], list):
            diagnostics.append(
                _diag("bad_model_fragment", "fragment.path_predicates must be a list", f"{field}.path_predicates")
            )
        if "symbolic_values" in fragment and not isinstance(fragment["symbolic_values"], list):
            diagnostics.append(
                _diag("bad_model_fragment", "fragment.symbolic_values must be a list", f"{field}.symbolic_values")
            )

    return diagnostics


def _safe_sha256(path: Path | None) -> str | None:
    if path is None or not path.exists():
        return None
    return sha256_file(path)


def _int_value(value: Any) -> int:
    return value if _is_int(value) else 0


def _enrich_readability_metadata(case: CaseConfig, data: dict[str, Any]) -> None:
    fragments = data.get("fragments")
    if not isinstance(fragments, list):
        return

    calls = parse_da_call_targets(case.input_da)
    for fragment in fragments:
        if not isinstance(fragment, dict):
            continue
        values = fragment.get("symbolic_values", [])
        symbolic_names: list[dict[str, str]] = []
        seen_names: set[str] = set()
        if isinstance(values, list):
            for value in values:
                if not isinstance(value, dict) or not isinstance(value.get("name"), str):
                    continue
                original = value["name"]
                if original in seen_names:
                    continue
                seen_names.add(original)
                symbolic_names.append(
                    {
                        "original": original,
                        "readable": readable_symbolic_name(original),
                    }
                )

        call_targets = [
            {
                "callsite": call.callsite,
                "callsite_hex": call.callsite_hex,
                "target": call.target,
                "readable_return": readable_return_name(call.target, call.callsite),
            }
            for call in call_targets_for_fragment(calls, fragment)
        ]
        fragment["readability"] = {
            "symbolic_names": symbolic_names,
            "call_targets": call_targets,
        }


def _fragment_sapic_is_empty(fragment: dict[str, Any]) -> bool:
    sapic = fragment.get("sapic")
    return not isinstance(sapic, str) or sapic.strip() in {"", "0"}


def _call_targets_from_fragment(fragment: dict[str, Any]) -> list[dict[str, Any]]:
    readability = fragment.get("readability", {})
    calls = readability.get("call_targets", []) if isinstance(readability, dict) else []
    return [call for call in calls if isinstance(call, dict)]


def _used_c_lib_indices(data: dict[str, Any]) -> set[int]:
    used: set[int] = set()
    fragments = data.get("fragments")
    if not isinstance(fragments, list):
        return used
    for fragment in fragments:
        if not isinstance(fragment, dict):
            continue
        sapic = fragment.get("sapic")
        if not isinstance(sapic, str):
            continue
        for match in re.finditer(r"\b([0-9]+)_C_Lib\b", sapic):
            used.add(int(match.group(1)))
    return used


def _fresh_c_lib_index(preferred: int, used: set[int]) -> int:
    value = preferred
    while value in used:
        value += 1
    used.add(value)
    return value


def _synthesize_missing_sapic_call_stubs(case: CaseConfig, data: dict[str, Any], sapic_path: Path) -> int:
    """Expose zero-process call fragments as explicit trace outputs.

    The HOL translator can reduce a selected fragment to Sapic ``0`` even when
    the fragment contains a classified/stubbed call.  Keeping only the JSON
    metadata makes the Squirrel export silently lose that call.  These stubs are
    intentionally shallow: they preserve the binary call boundary as an output
    while leaving primitive semantics abstract.
    """

    fragments = data.get("fragments")
    if not isinstance(fragments, list):
        return 0

    used = _used_c_lib_indices(data)
    additions: list[str] = []
    synthesized = 0

    for fragment in fragments:
        if not isinstance(fragment, dict) or not _fragment_sapic_is_empty(fragment):
            continue
        calls = _call_targets_from_fragment(fragment)
        if not calls:
            continue

        outputs: list[str] = []
        for call in calls:
            callsite = call.get("callsite")
            if not isinstance(callsite, int):
                continue
            index = _fresh_c_lib_index(callsite, used)
            outputs.append(f"(out({case.channel},{index}_C_Lib))")
        if not outputs:
            continue

        sapic_text = "\n".join(outputs)
        fragment["sapic"] = sapic_text
        fragment["sapic_synthesized"] = True
        fragment["sapic_synthesis_reason"] = "zero-process fragment with disassembly call target"
        additions.append(sapic_text)
        synthesized += len(outputs)

    if additions:
        existing = sapic_path.read_text(encoding="utf-8", errors="replace") if sapic_path.exists() else ""
        separator = "\n\n" if existing.strip() else ""
        sapic_path.parent.mkdir(parents=True, exist_ok=True)
        sapic_path.write_text(existing.rstrip() + separator + "\n\n".join(additions) + "\n", encoding="utf-8")

    return synthesized


def finalize_binary_model(
    case: CaseConfig,
    layout: BuildLayout,
    *,
    model_path: Path,
    sapic_path: Path,
) -> tuple[list[dict[str, str]], dict[str, Any]]:
    if not model_path.exists():
        return (
            [_diag("missing_binary_model", f"binary model was not generated: {model_path}", str(model_path))],
            {"model_schema": BINARY_MODEL_SCHEMA, "model_fragment_count": 0},
        )

    try:
        data = json.loads(model_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        return (
            [_diag("bad_binary_model_json", f"could not parse binary model JSON: {exc}", str(model_path))],
            {"model_schema": BINARY_MODEL_SCHEMA, "model_fragment_count": 0},
        )

    if isinstance(data, dict):
        _enrich_readability_metadata(case, data)
        synthesized_call_stubs = _synthesize_missing_sapic_call_stubs(case, data, sapic_path)
        if synthesized_call_stubs:
            data.setdefault("translation_notes", {})
            if isinstance(data["translation_notes"], dict):
                data["translation_notes"]["synthesized_sapic_call_stubs"] = synthesized_call_stubs

        provenance = data.setdefault("provenance", {})
        if isinstance(provenance, dict):
            provenance["input_da"] = str(case.input_da) if case.input_da is not None else None
            provenance["input_da_sha256"] = _safe_sha256(case.input_da)
            provenance["sapic"] = str(sapic_path)
            provenance["sapic_sha256"] = _safe_sha256(sapic_path)
        proof_status = data.setdefault("proof_status", {})
        if isinstance(proof_status, dict):
            proof_status.setdefault("binary_model", "generated_unchecked")
        model_path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    diagnostics = validate_binary_model_data(data)
    fragments = data.get("fragments", []) if isinstance(data, dict) else []
    good_fragments = [fragment for fragment in fragments if isinstance(fragment, dict)]
    metadata = {
        "model_schema": data.get("schema") if isinstance(data, dict) else BINARY_MODEL_SCHEMA,
        "model_fragment_count": len(fragments) if isinstance(fragments, list) else 0,
        "model_total_states": sum(_int_value(fragment.get("total_states")) for fragment in good_fragments),
        "model_assertion_clean_states": sum(
            _int_value(fragment.get("assertion_clean_states")) for fragment in good_fragments
        ),
    }
    return diagnostics, metadata
