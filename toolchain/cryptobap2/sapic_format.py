from __future__ import annotations


def _paren_delta(text: str) -> int:
    depth = 0
    quote: str | None = None
    for char in text:
        if quote:
            if char == quote:
                quote = None
            continue
        if char in {"'", '"'}:
            quote = char
        elif char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
    return depth


def format_sapic_text(raw: str) -> str:
    """Indent Sapic process text without changing tokens or branch structure."""

    lines: list[str] = []
    depth = 0
    for raw_line in raw.splitlines():
        stripped = raw_line.strip()
        if not stripped:
            continue
        leading_closes = len(stripped) - len(stripped.lstrip(")"))
        line_depth = max(depth - leading_closes, 0)
        if stripped in {"+", "|", "||", "else"}:
            line_depth = max(line_depth - 1, 0)
        lines.append("  " * line_depth + stripped)
        depth = max(depth + _paren_delta(stripped), 0)
    return "\n".join(lines) + ("\n" if lines else "")
