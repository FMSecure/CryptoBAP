from __future__ import annotations

import json


def yaml_scalar(value: object) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int):
        return str(value)
    if value is None:
        return "null"
    return json.dumps(str(value))


def yaml_inline_list(values: list[object]) -> str:
    if not values:
        return "[]"
    return "[" + ", ".join(yaml_scalar(value) for value in values) + "]"


def yaml_list(indent: int, values: list[object]) -> list[str]:
    pad = " " * indent
    if not values:
        return [f"{pad}[]"]
    return [f"{pad}- {yaml_scalar(value)}" for value in values]


def yaml_named_list(indent: int, name: str, values: list[object]) -> list[str]:
    pad = " " * indent
    if not values:
        return [f"{pad}{name}: []"]
    return [f"{pad}{name}:", *[f"{pad}  - {yaml_scalar(value)}" for value in values]]
