from __future__ import annotations

import json
import copy
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .paths import CRYPTOBAP2_ROOT, DEFAULT_CASE_DIR, resolve_config_path
from .schema import SchemaDiagnostic, validate_case_schema


class CaseConfigError(ValueError):
    pass


def load_yaml_subset(path: Path) -> dict[str, Any]:
    text = path.read_text(encoding="utf-8")
    try:
        import yaml  # type: ignore
    except Exception as exc:
        raise CaseConfigError("PyYAML is required to read CryptoBAP2 case files") from exc
    try:
        data = yaml.safe_load(text)
    except yaml.YAMLError as exc:  # type: ignore[attr-defined]
        raise CaseConfigError(f"could not parse case YAML {path}: {exc}") from exc
    if data is None:
        return {}
    if not isinstance(data, dict):
        raise CaseConfigError(f"case file must contain a mapping: {path}")
    return data


@dataclass(frozen=True)
class CaseConfig:
    path: Path
    raw: dict[str, Any]

    @property
    def name(self) -> str:
        value = self.raw.get("name")
        if not isinstance(value, str) or not value:
            raise CaseConfigError("case requires a non-empty 'name'")
        return value

    @property
    def arch(self) -> str:
        return str(self.raw.get("arch", "arm8"))

    def _resolve_path(self, value: object) -> Path:
        path = Path(str(value)).expanduser()
        if path.is_absolute():
            return path.resolve()

        root_candidate = CRYPTOBAP2_ROOT / path
        try:
            self.path.resolve().relative_to(CRYPTOBAP2_ROOT.resolve())
            case_is_in_repo = True
        except ValueError:
            case_is_in_repo = False
        if case_is_in_repo:
            return root_candidate.resolve()
        if self.path.suffix.lower() in {".yaml", ".yml"}:
            return (self.path.parent / path).resolve()
        return root_candidate.resolve()

    @property
    def input_da(self) -> Path | None:
        value = self.raw.get("input", {}).get("da") if isinstance(self.raw.get("input"), dict) else None
        return self._resolve_path(value) if value else None

    @property
    def input_binary(self) -> Path | None:
        value = self.raw.get("input", {}).get("binary") if isinstance(self.raw.get("input"), dict) else None
        return self._resolve_path(value) if value else None

    @property
    def theory(self) -> str:
        input_block = self.raw.get("input", {})
        if isinstance(input_block, dict) and input_block.get("theory"):
            return str(input_block["theory"])
        return self.name

    @property
    def symbols(self) -> list[str]:
        input_block = self.raw.get("input", {})
        value = input_block.get("symbols", []) if isinstance(input_block, dict) else []
        return [str(item) for item in value]

    @property
    def disassembly_sections(self) -> list[str]:
        input_block = self.raw.get("input", {})
        disassembly = input_block.get("disassembly", {}) if isinstance(input_block, dict) else {}
        if not isinstance(disassembly, dict):
            return [".text"]
        sections = disassembly.get("sections", [".text"])
        if not isinstance(sections, list) or not sections:
            return [".text"]
        return [str(section) for section in sections]

    @property
    def execution(self) -> dict[str, Any]:
        value = self.raw.get("execution", {})
        if not isinstance(value, dict):
            raise CaseConfigError("'execution' must be a mapping")
        return value

    @property
    def fragments(self) -> list[dict[str, Any]]:
        value = self.execution.get("fragments")
        if isinstance(value, list) and value:
            return [dict(item) for item in value if isinstance(item, dict)]
        entry = self.execution.get("entry_label")
        exits = self.execution.get("exit_labels", [])
        if entry is None:
            return []
        return [{"name": "main", "entry_label": entry, "exit_labels": exits}]

    @property
    def artifacts(self) -> dict[str, Path]:
        value = self.raw.get("artifacts", {})
        if not isinstance(value, dict):
            return {}
        return {
            key: self._resolve_path(path)
            for key, path in value.items()
            if path is not None and str(path) != ""
        }

    @property
    def backends(self) -> list[str]:
        value = self.raw.get("backends", ["squirrel"])
        return [str(item) for item in value]

    @property
    def proof_status(self) -> dict[str, str]:
        value = self.raw.get("proof_status", {})
        return {str(k): str(v) for k, v in value.items()} if isinstance(value, dict) else {}

    @property
    def channel(self) -> str:
        return str(self.raw.get("channel", "Channel"))

    def validate(self) -> list[str]:
        errors = [diagnostic.message for diagnostic in self.validation_diagnostics()]
        if self.input_da is not None and not self.input_da.exists():
            errors.append(f"input.da does not exist: {self.input_da}")
        if self.input_binary is not None and not self.input_binary.exists():
            errors.append(f"input.binary does not exist: {self.input_binary}")
        sapic_source = self.artifacts.get("sapic_source")
        if sapic_source is not None and not sapic_source.exists():
            errors.append(f"artifacts.sapic_source does not exist: {sapic_source}")
        tamarin_source = self.artifacts.get("tamarin_source")
        if tamarin_source is not None and not tamarin_source.exists():
            errors.append(f"artifacts.tamarin_source does not exist: {tamarin_source}")
        return errors

    def validation_diagnostics(self) -> list[SchemaDiagnostic]:
        return validate_case_schema(self.raw, path=self.path)

    def to_manifest_config(self) -> dict[str, Any]:
        return json.loads(json.dumps(self.raw, sort_keys=True, default=str))

    def with_input_da(self, path: Path) -> "CaseConfig":
        raw = copy.deepcopy(self.raw)
        input_block = raw.setdefault("input", {})
        if not isinstance(input_block, dict):
            input_block = {}
            raw["input"] = input_block
        input_block["da"] = str(path)
        return CaseConfig(path=self.path, raw=raw)


def resolve_case(value: str | Path) -> Path:
    path = Path(value)
    if path.exists():
        return path.resolve()
    if path.suffix:
        candidate = resolve_config_path(path)
    else:
        candidate = DEFAULT_CASE_DIR / f"{path}.yaml"
    if candidate.exists():
        return candidate.resolve()
    raise FileNotFoundError(f"case file not found: {value}")


def load_case(value: str | Path) -> CaseConfig:
    path = resolve_case(value)
    data = load_yaml_subset(path)
    return CaseConfig(path=path, raw=data)


def render_case_template(name: str, template: str = "xor") -> str:
    from .templates import CASE_TEMPLATES

    if template not in CASE_TEMPLATES:
        raise CaseConfigError(f"unknown template {template!r}; available: {', '.join(sorted(CASE_TEMPLATES))}")
    rendered = CASE_TEMPLATES[template].replace("name: " + template, "name: " + name, 1)
    return rendered
