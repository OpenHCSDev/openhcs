"""Config-schema renderer behaviour over typed ConfigSchema fixtures."""

from dataclasses import dataclass, replace

from python_introspect import to_jsonable

from openhcs.agent.dto.config import (
    ConfigFieldSchema,
    ConfigRegistrySchema,
    ConfigSchema,
    ConfigTypeSchema,
)
from openhcs.mcp.dev_client import McpDevCommandSpec, _build_parser, _calls_from_args
from openhcs.mcp.dev_client_core import (
    McpDevServerIdentity,
    McpDevToolBatchResponse,
    McpDevToolResult,
)
from openhcs.mcp.dev_client_renderers.config import ConfigSchemaRenderer
from openhcs.mcp.dev_client_rendering import CatalogRenderOptions, McpDevOutputRenderer

TOOL = "openhcs_describe_config_schema"


def _batch(*payloads) -> McpDevToolBatchResponse:
    return McpDevToolBatchResponse(
        server=McpDevServerIdentity(command="python", module="openhcs.mcp"),
        results=(McpDevToolResult(tool=TOOL, mcp_error=False, payloads=payloads),),
    )


def _schema() -> ConfigSchema:
    return ConfigSchema(
        schema_version="openhcs.agent.v1",
        config_type="PipelineConfig",
        fields=(
            ConfigFieldSchema(
                path="well_filter_config",
                type_repr="LazyWellFilterConfig | None",
                default_repr="None",
                required=False,
                description="Filter wells before execution.",
                registry_values=tuple(
                    "one two three four five six seven eight nine ten".split()
                ),
                value_type_repr="LazyWellFilterConfig",
                lazy=True,
                inheritable=True,
                nested_schema_path="well_filter_config",
            ),
            ConfigFieldSchema(
                path="fiji_streaming_config",
                type_repr="LazyFijiStreamingConfig | None",
                default_repr="None",
                required=False,
                description="Stream selected results to Fiji.",
                value_type_repr="LazyFijiStreamingConfig",
                lazy=True,
                inheritable=True,
            ),
            ConfigFieldSchema(
                path="default_component",
                type_repr="type[Axis]",
                default_repr="Microscopy.Channel",
                required=False,
                description="Default source component.",
                enum_values=("channel", "z_index"),
            ),
        ),
        registries=(ConfigRegistrySchema(owner_type="PipelineConfig", registered_types=()),),
        types=(ConfigTypeSchema(type_repr="LazyWellFilterConfig", description="Wells."),),
    )


def test_config_schema_renderer_is_registered_for_the_contract_and_its_subtypes() -> None:
    @dataclass(frozen=True, slots=True)
    class AnnotatedConfigSchema(ConfigSchema):
        annotation: str = "new declaration"

    assert McpDevOutputRenderer.for_output_contract(ConfigSchema) is ConfigSchemaRenderer
    assert (
        McpDevOutputRenderer.for_output_contract(AnnotatedConfigSchema)
        is ConfigSchemaRenderer
    )
    assert ConfigSchemaRenderer.render_options_type is CatalogRenderOptions
    annotated = AnnotatedConfigSchema(**{
        name: getattr(_schema(), name) for name in ConfigSchema.__dataclass_fields__
    })
    assert "flags=optional,lazy,inheritable" in ConfigSchemaRenderer.render(
        _batch(annotated)
    )


def test_config_schema_renderer_filters_and_bounds_fields() -> None:
    rendered = ConfigSchemaRenderer.render(
        _batch(_schema()), CatalogRenderOptions(contains="lazy", limit=1)
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
    assert "- LazyWellFilterConfig extends=<none>" in rendered

    defaults = ConfigSchemaRenderer.render(_batch(_schema()))
    assert "Fields: total=3 matched=3 shown=3" in defaults
    assert "enum=channel,z_index" in defaults
    assert "registry=one,two,three,four,five,six,seven,eight,+2" in defaults

    hidden = ConfigSchemaRenderer.render(
        _batch(
            replace(
                _schema(),
                path_prefix="children",
                fields=(
                    ConfigFieldSchema(
                        path="children[]",
                        type_repr="LazyChildConfig",
                        default_repr=None,
                        required=True,
                        description=" measured  source ",
                        authoring_value_path=("children", "[]"),
                        ui_hidden=True,
                    ),
                ),
            )
        ),
        CatalogRenderOptions(limit=-1),
    )
    assert "path=children" in hidden
    assert "Fields: total=1 matched=1 shown=0" in hidden
    assert "...<truncated 1 fields>" in hidden


def test_config_schema_absent_values_render_as_declared() -> None:
    for prefix, expected in ((None, "<root>"), ("", ""), ("children", "children")):
        rendered = ConfigSchemaRenderer.render(
            _batch(replace(_schema(), path_prefix=prefix))
        )
        assert f"path={expected} authoring=ConfigPatch.values" in rendered
    for value, expected in ((None, "<none>"), ("", ""), (0, "0"), (False, "False")):
        assert McpDevOutputRenderer.text(value) == expected


def test_config_schema_failures_render_unavailable_with_diagnostics() -> None:
    wire = to_jsonable(_batch(_schema()))
    del wire["results"][0]["payloads"][0]["fields"][0]["path"]
    rejected = ConfigSchemaRenderer.render(wire)
    assert rejected.startswith("Config schema: unavailable\nErrors:\n")
    assert "mcp_payload_invalid" in rejected

    stale = to_jsonable(_batch(_schema()))
    stale["results"][0]["payloads"] = [
        {
            "ok": False,
            "restart_required": True,
            "errors": [
                {
                    "code": "mcp_server_stale",
                    "message": "The OpenHCS MCP server source changed.",
                    "hint": "Restart the MCP client/server process.",
                }
            ],
        }
    ]
    rendered = ConfigSchemaRenderer.render(stale)
    assert rendered.startswith("Config schema: unavailable\n")
    assert (
        "- mcp_server_stale: The OpenHCS MCP server source changed. "
        'hint="Restart the MCP client/server process."'
    ) in rendered


def test_config_schema_command_reads_render_options_from_its_renderer() -> None:
    parser = _build_parser()
    args = parser.parse_args(
        (
            "config-schema", "pipeline", "--path-prefix", "fiji_streaming_config",
            "--contains", "lazy", "--limit", "1",
        )
    )
    call = _calls_from_args(args)[0]
    assert call.name == TOOL
    assert call.arguments == {
        "config_type": "pipeline",
        "path_prefix": "fiji_streaming_config",
    }
    rendered = McpDevCommandSpec.for_name("config-schema").render_result(
        _batch(_schema()), args
    )
    assert "Fields: total=3 matched=2 shown=1" in rendered

    call_args = parser.parse_args(
        ("call", TOOL, "--arguments", '{"config_type":"pipeline"}')
    )
    call_rendered = McpDevCommandSpec.for_name("call").render_result(
        _batch(_schema()), call_args
    )
    assert "Fields: total=3 matched=3 shown=3" in call_rendered
    assert '"payloads"' not in call_rendered


def test_typed_batch_renders_without_decoding_again(monkeypatch) -> None:
    def unexpected_decode(*args, **kwargs):
        raise AssertionError("A decoded schema must not be decoded again.")

    monkeypatch.setattr(
        "openhcs.mcp.dev_client_core.dataclass_from_mapping", unexpected_decode
    )
    assert "flags=optional,lazy,inheritable" in ConfigSchemaRenderer.render(
        _batch(_schema())
    )
