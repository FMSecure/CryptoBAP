from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


_DA_CALL_RE = re.compile(
    r"^\s*([0-9A-Fa-f]+):\s+[0-9A-Fa-f]+\s+\b(?:bl|blr|call|callq)\b(?:\s+[0-9A-Fa-fx]+)?\s*<([^>]+)>"
)


@dataclass(frozen=True)
class CallTarget:
    callsite: int
    target: str

    @property
    def callsite_hex(self) -> str:
        return f"0x{self.callsite:x}"


def sanitize_readable_identifier(value: str, *, fallback: str = "value") -> str:
    cleaned = re.sub(r"[^A-Za-z0-9_]", "_", value).strip("_")
    cleaned = re.sub(r"_+", "_", cleaned)
    if not cleaned:
        cleaned = fallback
    if cleaned[0].isdigit():
        cleaned = f"{fallback}_{cleaned}"
    return cleaned


def readable_call_target_name(target: str) -> str:
    if "/" in target:
        target = target.rsplit("/", 1)[-1]
    return sanitize_readable_identifier(target, fallback="call")


def readable_return_name(target: str, callsite: int) -> str:
    return f"ret_{readable_call_target_name(target)}_{callsite:x}"


def parse_da_call_targets(da_path: Path | None) -> list[CallTarget]:
    if da_path is None or not da_path.exists():
        return []
    calls: list[CallTarget] = []
    with da_path.open("r", encoding="utf-8", errors="replace") as handle:
        for raw in handle:
            match = _DA_CALL_RE.match(raw)
            if not match:
                continue
            calls.append(CallTarget(callsite=int(match.group(1), 16), target=match.group(2)))
    return calls


def _int_or_none(value: Any) -> int | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    try:
        return int(str(value), 0)
    except (TypeError, ValueError):
        return None


def _fragment_bounds(fragment: dict[str, Any]) -> tuple[int | None, int | None]:
    start = _int_or_none(fragment.get("entry_label"))
    end = _int_or_none(fragment.get("end_label"))
    if end is None:
        exits = fragment.get("exit_labels", [])
        if isinstance(exits, list) and exits:
            exit_values = [_int_or_none(value) for value in exits]
            concrete = [value for value in exit_values if value is not None]
            if concrete:
                end = max(concrete) + 4
    return start, end


def call_targets_for_fragment(calls: Iterable[CallTarget], fragment: dict[str, Any]) -> list[CallTarget]:
    start, end = _fragment_bounds(fragment)
    if start is None:
        return list(calls)
    selected = []
    for call in calls:
        if call.callsite < start:
            continue
        if end is not None and call.callsite >= end:
            continue
        selected.append(call)
    return selected


def call_targets_for_fragments(da_path: Path | None, fragments: list[dict[str, Any]]) -> list[CallTarget]:
    calls = parse_da_call_targets(da_path)
    if not fragments:
        return calls
    selected: list[CallTarget] = []
    seen: set[int] = set()
    for fragment in fragments:
        for call in call_targets_for_fragment(calls, fragment):
            if call.callsite in seen:
                continue
            seen.add(call.callsite)
            selected.append(call)
    return sorted(selected, key=lambda call: call.callsite)


def readable_symbolic_name(name: str) -> str:
    if name.startswith("sy_"):
        return sanitize_readable_identifier("sym_" + name[3:], fallback="sym")

    match = re.fullmatch(r"([0-9]+)_(.+)", name)
    if not match:
        return sanitize_readable_identifier(name, fallback="value")

    index, suffix = match.groups()
    if suffix == "C_Lib":
        return f"ret_C_Lib_{index}"
    if suffix == "MEM":
        return f"mem_snapshot_{index}"
    if re.fullmatch(r"R[0-9]+", suffix):
        return f"reg_{suffix}_{index}"
    if suffix == "tmp_SP_EL0":
        return f"tmp_SP_EL0_{index}"
    if suffix.startswith("sy_"):
        return sanitize_readable_identifier(f"sym_{suffix[3:]}_{index}", fallback="sym")
    return sanitize_readable_identifier(f"{suffix}_{index}", fallback="value")
