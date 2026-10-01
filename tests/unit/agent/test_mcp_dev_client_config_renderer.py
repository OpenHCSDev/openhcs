"""Focused dev-client rendering tests for reflected configuration schemas."""

import ast
from dataclasses import dataclass, replace
from pathlib import Path

from openhcs.agent.dto.config import ConfigFieldSchema, ConfigSchema, ConfigTypeSchema
from openhcs.mcp.dev_client import McpDevCommandSpec, _build_parser, _calls_from_args
from openhcs.mcp.dev_client_core import (
    McpDevServerIdentity,
    McpDevToolBatchResponse,
    McpDevToolResult,
)
from openhcs.mcp.dev_client_rendering import (
    CatalogRenderOptions,
    McpDevOutputRenderer,
)


def _config_schema_response() -> dict:
    return {
        "server": {"command": "python", "module": "openhcs.mcp"},
        "errors": [],
        "results": [
            {
                "tool": "openhcs_describe_config_schema",
                "mcp_error": False,
                "payloads": [
                    {
                        "schema_version": "openhcs.agent.v1",
                        "config_type": "PipelineConfig",
                        "path_prefix": None,
                        "authoring_path": "ConfigPatch.values",
                        "fields": [
                            {
                                "path": "well_filter_config",
                                "type_repr": "LazyWellFilterConfig | None",
                                "default_repr": "None",
                                "required": False,
                                "description": "Filter wells before execution.",
                                "enum_values": [],
                                "registry_values": [
                                    "one",
                                    "two",
                                    "three",
                                    "four",
                                    "five",
                                    "six",
                                    "seven",
                                    "eight",
                                    "nine",
                                    "ten",
                                ],
                                "value_type_repr": "LazyWellFilterConfig",
                                "ui_hidden": False,
                                "lazy": True,
                                "inheritable": True,
                                "nested_schema_path": "well_filter_config",
                            },
                            {
                                "path": "fiji_streaming_config",
                                "type_repr": "LazyFijiStreamingConfig | None",
                                "default_repr": "None",
                                "required": False,
                                "description": "Stream selected results to Fiji.",
                                "enum_values": [],
                                "registry_values": [],
                                "value_type_repr": "LazyFijiStreamingConfig",
                                "ui_hidden": False,
                                "lazy": True,
                                "inheritable": True,
                                "nested_schema_path": "fiji_streaming_config",
                            },
                            {
                                "path": "default_component",
                                "type_repr": "AllComponents",
                                "default_repr": "AllComponents.CHANNEL",
                                "required": False,
                                "description": "Default source component.",
                                "enum_values": ["channel", "z_index"],
                                "registry_values": [],
                                "value_type_repr": None,
                                "ui_hidden": False,
                                "lazy": False,
                                "inheritable": False,
                                "nested_schema_path": None,
                            },
                        ],
                        "registries": [
                            {
                                "owner_type": "PipelineConfig",
                                "registered_types": [],
                            }
                        ],
                        "types": [
                            {
                                "type_repr": "LazyWellFilterConfig",
                                "description": "Well filtering configuration.",
                                "base_types": [],
                            }
                        ],
                    }
                ],
            }
        ],
    }


def _config_schema_error_response() -> dict:
    return {
        "server": {"command": "python", "module": "openhcs.mcp"},
        "errors": [],
        "results": [
            {
                "tool": "openhcs_describe_config_schema",
                "mcp_error": False,
                "payloads": [
                    {
                        "errors": [
                            {
                                "code": "mcp_server_stale",
                                "message": (
                                    "The OpenHCS MCP server source changed after "
                                    "this process started."
                                ),
                                "hint": "Restart the MCP client/server process.",
                            }
                        ],
                        "ok": False,
                        "restart_required": True,
                    }
                ],
            }
        ],
    }


def test_config_schema_renderer_is_keyed_by_nominal_output_contract() -> None:
    binding = McpDevOutputRenderer.for_output_contract(ConfigSchema)

    assert binding is not None
    assert binding.renderer_type.render_options_type is CatalogRenderOptions


def test_config_schema_renderer_preserves_shared_response_errors() -> None:
    binding = McpDevOutputRenderer.for_output_contract(ConfigSchema)

    assert binding is not None
    rendered = binding.render_with_options(
        _config_schema_error_response(),
        CatalogRenderOptions(),
    )

    assert rendered.startswith("Result: <unavailable>\n")
    assert (
        "- mcp_server_stale: The OpenHCS MCP server source changed after this "
        'process started. hint="Restart the MCP client/server process."'
    ) in rendered
    assert "type=<none>" not in rendered

    transport_rendered = binding.render_with_options(
        {
            "server": {"command": "python", "module": "openhcs.mcp"},
            "errors": [
                {
                    "code": "mcp_transport_failed",
                    "phase": "call_tool",
                    "exception_type": "EOFError",
                    "causes": [],
                    "message": "MCP stdio exchange ended during source reload.",
                    "hint": "Retry with a fresh server process.",
                }
            ],
            "results": [],
        },
        CatalogRenderOptions(),
    )
    assert transport_rendered.startswith("Result: <unavailable>\n")
    assert (
        "- mcp_transport_failed: MCP stdio exchange ended during source reload. "
        'hint="Retry with a fresh server process."'
    ) in transport_rendered


def test_config_schema_renderer_filters_and_bounds_reflected_fields() -> None:
    binding = McpDevOutputRenderer.for_output_contract(ConfigSchema)

    assert binding is not None
    rendered = binding.render_with_options(
        _config_schema_response(),
        CatalogRenderOptions(contains="lazy", limit=1),
    )

    assert (
        "Config schema: type=PipelineConfig path=<root> authoring=ConfigPatch.values"
    ) in rendered
    assert "Fields: total=3 matched=2 shown=1 registries=1 types=1" in rendered
    assert "Filter: contains=lazy" in rendered
    assert (
        "- well_filter_config: LazyWellFilterConfig | None "
        "value=LazyWellFilterConfig default=None "
        "flags=optional,lazy,inheritable nested=well_filter_config"
    ) in rendered
    assert "fiji_streaming_config" not in rendered
    assert "...<truncated 1 fields>" in rendered
    assert "Type inheritance (declaration-derived):" in rendered
    assert "- LazyWellFilterConfig extends=<none>" in rendered


def test_config_schema_renderer_declares_compact_catalog_defaults() -> None:
    binding = McpDevOutputRenderer.for_output_contract(ConfigSchema)

    assert binding is not None
    assert binding.default_cli_argument_values() == {
        "contains": None,
        "limit": 20,
    }
    rendered = binding.render_with_options(
        _config_schema_response(),
        CatalogRenderOptions(),
    )

    assert "Fields: total=3 matched=3 shown=3 registries=1 types=1" in rendered
    assert "enum=channel,z_index" in rendered
    assert "registry=one,two,three,four,five,six,seven,eight,+2" in rendered
    assert '"payloads"' not in rendered
    assert "Type inheritance (declaration-derived):" in rendered


def test_generated_config_schema_command_projects_request_and_render_options() -> None:
    parser = _build_parser()
    args = parser.parse_args(
        (
            "config-schema",
            "pipeline",
            "--path-prefix",
            "fiji_streaming_config",
            "--contains",
            "lazy",
            "--limit",
            "1",
        )
    )

    call = _calls_from_args(args)[0]

    assert call.name == "openhcs_describe_config_schema"
    assert call.arguments == {
        "config_type": "pipeline",
        "path_prefix": "fiji_streaming_config",
    }
    rendered = McpDevCommandSpec.for_name("config-schema").render_response(
        _config_schema_response(),
        args,
    )
    assert "Fields: total=3 matched=2 shown=1 registries=1 types=1" in rendered
    assert "...<truncated 1 fields>" in rendered

    call_args = parser.parse_args(
        (
            "call",
            "openhcs_describe_config_schema",
            "--arguments",
            '{"config_type":"pipeline"}',
        )
    )
    call_rendered = McpDevCommandSpec.for_name("call").render_response(
        _config_schema_response(),
        call_args,
    )
    assert "Fields: total=3 matched=3 shown=3 registries=1 types=1" in call_rendered
    assert '"payloads"' not in call_rendered


def test_config_schema_typed_boundary_reuses_nested_values(monkeypatch) -> None:
    response = McpDevToolBatchResponse.for_rendering(_config_schema_response())
    schema = response.results[0].first_decoded_payload()
    assert isinstance(schema, ConfigSchema)
    assert isinstance(schema.fields[0], ConfigFieldSchema)
    assert isinstance(schema.types[0], ConfigTypeSchema)
    assert schema.fields[0].lazy is True
    assert schema.fields[0].inheritable is True
    assert schema.fields[0].default_repr == "None"

    def unexpected_decode(*args, **kwargs):
        raise AssertionError("The decoded schema must not be reinterpreted.")

    monkeypatch.setattr(
        "openhcs.mcp.dev_client_rendering.dataclass_from_mapping", unexpected_decode
    )
    binding = McpDevOutputRenderer.for_output_contract(ConfigSchema)
    assert binding is not None
    assert binding.decode_payload(schema) is schema
    rendered = binding.render_result(response, CatalogRenderOptions())
    assert "flags=optional,lazy,inheritable" in rendered
    assert "default=None" in rendered


def test_config_schema_subtype_uses_ancestor_without_registry_edits() -> None:
    @dataclass(frozen=True, slots=True)
    class AnnotatedConfigSchema(ConfigSchema):
        annotation: str = "new declaration"

    schema = AnnotatedConfigSchema(
        config_type="PipelineConfig",
        schema_version="openhcs.agent.v1",
        fields=(
            ConfigFieldSchema(
                path="children[]",
                type_repr="LazyChildConfig",
                default_repr=None,
                required=True,
                description=" measured  source ",
                authoring_value_path=("children", "[]"),
                lazy=True,
                inheritable=True,
                ui_hidden=True,
            ),
        ),
        path_prefix="children",
    )
    binding = McpDevOutputRenderer.for_output_contract(AnnotatedConfigSchema)
    parent = McpDevOutputRenderer.for_output_contract(ConfigSchema)
    assert binding is not None and parent is not None
    assert binding.renderer_type is parent.renderer_type
    assert binding.decode_payload(schema) is schema
    response = McpDevToolBatchResponse(
        server=McpDevServerIdentity(
            command="python",
            module="openhcs.mcp",
        ),
        results=(
            McpDevToolResult(
                tool="openhcs_describe_config_schema",
                mcp_error=False,
                payloads=(schema,),
            ),
        ),
    )
    rendered = binding.render_result(response, CatalogRenderOptions(limit=1))
    assert "path=children" in rendered
    assert "flags=required,lazy,inheritable,ui_hidden" in rendered
    assert "authoring=children/[]" in rendered
    assert 'help="measured source"' in rendered
    assert "default=" not in rendered
    bounded = binding.render_result(response, CatalogRenderOptions(limit=-1))
    assert "Fields: total=1 matched=1 shown=0" in bounded
    assert "...<truncated 1 fields>" in bounded
    assert "- children[]:" not in bounded
    empty = replace(schema, fields=(), types=(), registries=())
    assert "total=0 matched=0 shown=0" in binding.render_result(
        replace(response, results=(replace(response.results[0], payloads=(empty,)),)),
        CatalogRenderOptions(),
    )


def test_config_schema_rejects_incomplete_nested_record() -> None:
    response = _config_schema_response()
    del response["results"][0]["payloads"][0]["fields"][0]["path"]
    binding = McpDevOutputRenderer.for_output_contract(ConfigSchema)
    assert binding is not None
    rendered = binding.render_with_options(response, CatalogRenderOptions())
    assert rendered.startswith("Result: <unavailable>\n")
    assert "mcp_payload_invalid" in rendered
    assert "Fields: total=" not in rendered


def test_config_schema_renderer_has_no_raw_payload_reader() -> None:
    from openhcs.mcp.dev_client_renderers import config

    source = ast.parse(Path(config.__file__).read_text())
    assert not any(
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr in {"get", "first_tool_payload", "sequence_of_mappings"}
        for node in ast.walk(source)
    )
    assert not any(
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id in {"getattr", "isinstance", "dataclass_from_mapping"}
        for node in ast.walk(source)
    )
