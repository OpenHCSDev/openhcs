"""Family test: every registered dev-client renderer presents its own DTO.

Each renderer is exercised with an instance of its declared output contract
built from the DTO class itself (every field populated, one element per
collection), framed exactly as the dev client frames a tool batch. The test
protects the renderer contract: attribute access only, warnings and errors
appended by the base, and the unavailable summary when a call produced no
payload.
"""

from __future__ import annotations
from openhcs.agent.dto.session import DatasetRowState

import enum
import types
import typing
from dataclasses import MISSING, fields, is_dataclass

import pytest
from python_introspect import to_jsonable

from openhcs.agent.dto.common import AgentError, AgentWarning
from openhcs.mcp.dev_client_core import (
    McpDevServerIdentity,
    McpDevToolBatchResponse,
    McpDevToolResult,
)
from openhcs.mcp.dev_client_renderers import ensure_dev_client_renderers_registered
from openhcs.mcp.dev_client_rendering import McpDevOutputRenderer

SERVER = McpDevServerIdentity(command="python", module="openhcs.mcp")
MAX_DEPTH = 4


def sample_value(hint, depth: int):
    """A populated value of a declared field type."""
    origin = typing.get_origin(hint)
    if origin is typing.Annotated:
        return sample_value(typing.get_args(hint)[0], depth)
    if origin is typing.Literal:
        return typing.get_args(hint)[0]
    if origin in (typing.Union, types.UnionType):
        members = [arg for arg in typing.get_args(hint) if arg is not type(None)]
        return sample_value(members[0], depth)
    if origin is tuple:
        args = typing.get_args(hint)
        if depth >= MAX_DEPTH or not args:
            return ()
        if len(args) == 2 and args[1] is Ellipsis:
            if args[0] in (AgentError, AgentWarning):
                # Diagnostics are the base's presentation, covered below.
                return ()
            return tuple(sample_value(args[0], depth + 1) for _ in range(2))
        return tuple(sample_value(arg, depth + 1) for arg in args)
    if origin in (list, typing.get_origin(typing.Sequence[int])):
        return [] if depth >= MAX_DEPTH else [sample_value(typing.get_args(hint)[0], depth + 1)]
    if origin in (dict, typing.get_origin(typing.Mapping[str, int])):
        key_type, value_type = typing.get_args(hint) or (str, str)
        if depth >= MAX_DEPTH:
            return {}
        return {sample_value(key_type, depth + 1): sample_value(value_type, depth + 1)}
    if isinstance(hint, type):
        if issubclass(hint, enum.Enum):
            return next(iter(hint))
        if hint is bool:
            return True
        if hint is int:
            return 1
        if hint is float:
            return 1.0
        if hint is str:
            return "sample"
        if is_dataclass(hint):
            return sample_dto(hint, depth + 1)
    if isinstance(hint, typing.TypeAliasType if hasattr(typing, "TypeAliasType") else ()):
        return sample_value(hint.__value__, depth)
    # Dynamic JSON that no class models: an empty object.
    return {}


# JSON fields whose content a renderer decodes through a declared model.
JSON_FIELD_SAMPLES = {
    ("RuntimeExecutionStatus", "response"): lambda: {"status": "ok", "uptime": 1.0},
    ("*", "selected_plate"): lambda: to_jsonable(sample_dto(DatasetRowState)),
}


def sample_dto(dto_type: type, depth: int = 0):
    """Build ``dto_type`` with every field populated where its type allows."""
    hints = typing.get_type_hints(dto_type, include_extras=True)
    values = {}
    defaulted = set()
    for declaration in fields(dto_type):
        if not declaration.init:
            continue
        has_default = (
            declaration.default is not MISSING
            or declaration.default_factory is not MISSING
        )
        if has_default:
            defaulted.add(declaration.name)
            if depth >= MAX_DEPTH:
                continue
        declared_sample = JSON_FIELD_SAMPLES.get(
            (dto_type.__name__, declaration.name)
        ) or JSON_FIELD_SAMPLES.get(("*", declaration.name))
        if declared_sample is not None:
            values[declaration.name] = declared_sample()
            continue
        try:
            values[declaration.name] = sample_value(hints[declaration.name], depth)
        except (TypeError, ValueError, KeyError):
            if not has_default:
                raise
    try:
        return dto_type(**values)
    except (TypeError, ValueError, KeyError):
        return dto_type(
            **{name: value for name, value in values.items() if name not in defaulted}
        )


def framed(payload) -> McpDevToolBatchResponse:
    return McpDevToolBatchResponse(
        server=SERVER,
        results=(McpDevToolResult(tool="openhcs_test_tool", mcp_error=False, payloads=(payload,)),),
    )


def registered_renderers() -> tuple[type[McpDevOutputRenderer], ...]:
    ensure_dev_client_renderers_registered()
    return tuple(
        sorted(
            dict.fromkeys(McpDevOutputRenderer.__registry__.values()),
            key=lambda renderer: renderer.__qualname__,
        )
    )


@pytest.mark.parametrize(
    "renderer", registered_renderers(), ids=lambda renderer: renderer.__name__
)
def test_every_renderer_presents_its_declared_dto(renderer):
    payload = sample_dto(renderer.output_contract)

    rendered = renderer.render(framed(payload))

    assert rendered.strip()
    assert renderer.unavailable_summary not in rendered.splitlines()[:1]
    assert "Errors:" not in rendered


@pytest.mark.parametrize(
    "renderer", registered_renderers(), ids=lambda renderer: renderer.__name__
)
def test_every_renderer_reports_a_missing_payload_as_unavailable(renderer):
    failed = McpDevToolBatchResponse(
        server=SERVER,
        results=(McpDevToolResult(tool="openhcs_test_tool", mcp_error=True, payloads=()),),
    )

    rendered = renderer.render(failed)

    assert rendered.splitlines() == [
        renderer.unavailable_summary,
        "Errors:",
        "- mcp_tool_error: openhcs_test_tool failed.",
    ]


def test_base_appends_payload_warnings_and_declared_errors_once():
    from openhcs.agent.dto.ui_bridge import UiCodeDocumentValidationResult

    payload = UiCodeDocumentValidationResult(
        document_id="doc",
        schema_version="v1",
        valid=False,
        errors=(AgentError(code="bad_source", message="Source is invalid."),),
        warnings=(AgentWarning(code="slow", message="Validation was slow.", hint="wait"),),
    )

    rendered = McpDevOutputRenderer.for_output_contract(
        UiCodeDocumentValidationResult
    ).render(framed(payload))

    assert rendered.splitlines() == [
        "Code document validation: id=doc valid=False normalized_scopes=<none>",
        "Warnings:",
        '- slow: Validation was slow. hint="wait"',
        "Errors:",
        "- bad_source: Source is invalid.",
    ]
