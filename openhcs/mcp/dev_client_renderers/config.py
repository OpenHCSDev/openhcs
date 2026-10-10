"""Configuration-schema rendering for the OpenHCS MCP dev client."""

from __future__ import annotations

import json

from openhcs.agent.dto.config import (
    ConfigFieldSchema,
    ConfigSchema,
    ConfigTypeSchema,
)
from openhcs.mcp.dev_client_rendering import (
    CatalogRenderOptions,
    McpDevOutputRenderer,
)


class ConfigSchemaRenderer(McpDevOutputRenderer):
    """Render reflected config fields as a compact, searchable catalog."""

    output_contract = ConfigSchema
    render_options_type = CatalogRenderOptions
    unavailable_summary = "Config schema: unavailable"

    @classmethod
    def render_payload(
        cls,
        payload: ConfigSchema,
        options: CatalogRenderOptions,
    ) -> str:
        all_fields = payload.fields
        matched_fields, visible_fields = options.select(all_fields, cls._field_line)
        path_text = cls.text(payload.path_prefix, absent_text="<root>")
        lines = [
            (
                "Config schema: "
                f"type={payload.config_type} "
                f"path={path_text} "
                f"authoring={payload.authoring_path}"
            ),
            (
                "Fields: "
                f"total={len(all_fields)} matched={len(matched_fields)} "
                f"shown={len(visible_fields)} registries={len(payload.registries)} "
                f"types={len(payload.types)}"
            ),
        ]
        lines.extend(options.filter_lines())
        if visible_fields:
            lines.append("Field paths:")
            lines.extend(cls._field_line(field) for field in visible_fields)
        if len(visible_fields) < len(matched_fields):
            lines.append(
                f"...<truncated {len(matched_fields) - len(visible_fields)} fields>"
            )
        if payload.types:
            lines.append("Type inheritance (declaration-derived):")
            lines.extend(cls._type_line(type_schema) for type_schema in payload.types)
        return "\n".join(lines)

    @classmethod
    def _field_line(cls, field: ConfigFieldSchema) -> str:
        parts = [
            f"- {field.path}:",
            field.type_repr,
        ]
        value_type = field.value_type_repr
        if value_type is not None:
            parts.append(f"value={value_type}")
        default = field.default_repr
        if default is not None:
            parts.append(f"default={default}")
        parts.append(f"flags={','.join(cls._field_flags(field))}")
        nested_path = field.nested_schema_path
        if nested_path is not None:
            parts.append(f"nested={nested_path}")
        if field.authoring_value_path:
            parts.append("authoring=" + "/".join(field.authoring_value_path))
        enum_values = cls._scalar_values_text(field.enum_values)
        if enum_values:
            parts.append(f"enum={enum_values}")
        registry_values = cls._scalar_values_text(field.registry_values)
        if registry_values:
            parts.append(f"registry={registry_values}")
        description = field.description
        if description is not None and description.strip():
            parts.append(f"help={json.dumps(cls._compact_text(description))}")
        return " ".join(parts)

    @classmethod
    def _type_line(cls, type_schema: ConfigTypeSchema) -> str:
        type_repr = type_schema.type_repr
        base_types = cls._scalar_values_text(
            type_schema.base_types,
            limit=12,
        )
        return f"- {type_repr} extends={base_types or '<none>'}"

    @staticmethod
    def _field_flags(field: ConfigFieldSchema) -> tuple[str, ...]:
        return (
            "required" if field.required else "optional",
            *(
                name
                for enabled, name in (
                    (field.lazy, "lazy"),
                    (field.inheritable, "inheritable"),
                    (field.ui_hidden, "ui_hidden"),
                )
                if enabled
            ),
        )

    @staticmethod
    def _scalar_values_text(values: tuple[str, ...], limit: int = 8) -> str:
        visible_values = values[:limit]
        text = ",".join(visible_values)
        if len(visible_values) < len(values):
            text += f",+{len(values) - len(visible_values)}"
        return text

    @staticmethod
    def _compact_text(value: str, limit: int = 180) -> str:
        compact = " ".join(value.split())
        if len(compact) <= limit:
            return compact
        return f"{compact[: limit - 3]}..."
