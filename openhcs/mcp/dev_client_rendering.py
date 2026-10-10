"""Shared rendering contracts for the OpenHCS MCP dev client.

Every compact renderer is an ``McpDevOutputRenderer`` keyed by the output DTO
it presents. The base decodes the framed tool batch once, renders the decoded
payload through the renderer registered for its type, and appends the payload's
warnings and the batch diagnostics. Renderers read DTO attributes only.
"""

from __future__ import annotations

import argparse
import json
from collections.abc import Callable, Iterable, Mapping, Sequence
from dataclasses import dataclass, fields, is_dataclass
from enum import Enum
from typing import ClassVar, TypeAlias, TypeVar

from metaclass_registry import AutoRegisterMeta
from python_introspect import JsonValue

from openhcs.agent.capabilities import (
    AgentCapabilityDeclaration,
    CapabilityWorkflowGroup,
    get_agent_capability,
)
from openhcs.agent.dto.authoring import AuthoringContextRequest
from openhcs.agent.dto.common import AgentError, AgentWarning

DEFAULT_CODE_DOCUMENT_MAX_CHARS = 2_000
PresentationValue = TypeVar("PresentationValue")


class WidgetTreeOutputFormat(str, Enum):
    """CLI presentation formats for widget-tree command output."""

    JSON = "json"
    OUTLINE = "outline"

    @property
    def is_json(self) -> bool:
        return self is WidgetTreeOutputFormat.JSON

    @classmethod
    def choices(cls) -> tuple[str, ...]:
        return tuple(output_format.value for output_format in cls)


@dataclass(frozen=True, slots=True)
class McpDevOutputRenderOptions:
    """Typed presentation options for an output-contract renderer.

    Each options type declares its own CLI flags and reads them back; the
    dataclass defaults are the options used when a generic ``call`` renders.
    """

    @classmethod
    def configure_cli_parser(cls, parser: argparse.ArgumentParser) -> None:
        """Declare renderer-owned CLI presentation options."""
        del parser

    @classmethod
    def from_cli_args(cls, args: argparse.Namespace) -> "McpDevOutputRenderOptions":
        """Construct renderer options from its declared CLI arguments."""
        del args
        return cls()


@dataclass(frozen=True, slots=True)
class AuthoringContextRenderOptions(McpDevOutputRenderOptions):
    max_chars: int = AuthoringContextRequest().max_chars

    @classmethod
    def configure_cli_parser(cls, parser: argparse.ArgumentParser) -> None:
        parser.add_argument("--max-chars", type=int, default=cls().max_chars)

    @classmethod
    def from_cli_args(cls, args: argparse.Namespace) -> "AuthoringContextRenderOptions":
        return cls(max_chars=args.max_chars)


@dataclass(frozen=True, slots=True)
class CodeDocumentRenderOptions(McpDevOutputRenderOptions):
    include_source: bool = True
    max_source_chars: int = DEFAULT_CODE_DOCUMENT_MAX_CHARS

    @classmethod
    def configure_cli_parser(cls, parser: argparse.ArgumentParser) -> None:
        parser.add_argument(
            "--no-source",
            action="store_true",
            help="Only render document metadata, revision, and snapshot information.",
        )
        parser.add_argument(
            "--max-source-chars",
            type=int,
            default=cls().max_source_chars,
        )

    @classmethod
    def from_cli_args(cls, args: argparse.Namespace) -> "CodeDocumentRenderOptions":
        return cls(
            include_source=not args.no_source,
            max_source_chars=args.max_source_chars,
        )

    def source_text(self, source: str) -> str:
        """One bounded source-text policy shared by all source presentations."""
        if self.max_source_chars < 0:
            raise ValueError("max_source_chars must be nonnegative.")
        if len(source) <= self.max_source_chars:
            return source
        return (
            source[: self.max_source_chars]
            + f"\n...<truncated {len(source) - self.max_source_chars} chars>"
        )


@dataclass(frozen=True, slots=True)
class UiActionCatalogRenderOptions(McpDevOutputRenderOptions):
    widget_id: str | None = None

    @classmethod
    def configure_cli_parser(cls, parser: argparse.ArgumentParser) -> None:
        parser.add_argument(
            "widget_id",
            nargs="?",
            help="Optional widget id filter, for example plate_manager.",
        )

    @classmethod
    def from_cli_args(cls, args: argparse.Namespace) -> "UiActionCatalogRenderOptions":
        return cls(widget_id=args.widget_id)


@dataclass(frozen=True, slots=True)
class ViewerImageSampleRenderOptions(McpDevOutputRenderOptions):
    include_array_values_requested: bool | None = None

    @classmethod
    def from_cli_args(
        cls, args: argparse.Namespace
    ) -> "ViewerImageSampleRenderOptions":
        return cls(include_array_values_requested=args.include_array_values)


@dataclass(frozen=True, slots=True)
class CatalogRenderOptions(McpDevOutputRenderOptions):
    contains: str | None = None
    limit: int = 20

    @classmethod
    def configure_cli_parser(cls, parser: argparse.ArgumentParser) -> None:
        parser.add_argument(
            "--contains",
            help="Show only catalog entries containing this text.",
        )
        parser.add_argument(
            "--limit",
            type=int,
            default=cls().limit,
            help="Maximum catalog entries shown in compact output.",
        )

    @classmethod
    def from_cli_args(cls, args: argparse.Namespace) -> "CatalogRenderOptions":
        return cls(contains=args.contains, limit=args.limit)

    def select(
        self,
        entries: Sequence[PresentationValue],
        entry_text: Callable[[PresentationValue], str],
    ) -> tuple[tuple[PresentationValue, ...], tuple[PresentationValue, ...]]:
        """Return (matched, shown) entries for the ``--contains``/``--limit`` filter."""
        matched = tuple(entries)
        if self.contains:
            needle = self.contains.casefold()
            matched = tuple(
                entry for entry in matched if needle in entry_text(entry).casefold()
            )
        return matched, matched[: max(self.limit, 0)]

    def filter_lines(self) -> tuple[str, ...]:
        return (f"Filter: contains={self.contains}",) if self.contains else ()


@dataclass(frozen=True, slots=True)
class WidgetTreeRenderOptions(McpDevOutputRenderOptions):
    outline_root_class: str | None = None
    include_technical_widgets: bool = False

    @classmethod
    def configure_cli_parser(cls, parser: argparse.ArgumentParser) -> None:
        parser.add_argument(
            "--outline-root-class",
            help="When rendering outline output, start at the first node with this Qt class.",
        )
        parser.add_argument(
            "--include-technical-widgets",
            action="store_true",
            help="Include Qt infrastructure nodes such as scrollbars in outline output.",
        )

    @classmethod
    def from_cli_args(cls, args: argparse.Namespace) -> "WidgetTreeRenderOptions":
        return cls(
            outline_root_class=args.outline_root_class,
            include_technical_widgets=args.include_technical_widgets,
        )


def payload_warnings(value: object) -> tuple[AgentWarning, ...]:
    """Collect the declared warnings carried anywhere in a decoded payload."""
    if isinstance(value, AgentWarning):
        return (value,)
    if isinstance(value, list | tuple):
        return tuple(warning for item in value for warning in payload_warnings(item))
    if is_dataclass(value) and not isinstance(value, type):
        return tuple(
            warning
            for declaration in fields(value)
            for warning in payload_warnings(getattr(value, declaration.name))
        )
    return ()


McpDevOutputRendererKey: TypeAlias = type


def mcp_dev_output_renderer_key(
    name: str,
    renderer_type: type,
) -> McpDevOutputRendererKey | None:
    """A renderer registers the output contract its own class body declares."""
    del name
    declared_output_contract = vars(renderer_type).get("output_contract")
    if isinstance(declared_output_contract, type):
        return declared_output_contract
    return None


class McpDevOutputRenderer(metaclass=AutoRegisterMeta):
    """Compact renderer registered for one agent output DTO.

    ``render`` is the single ingress: it decodes the batch, renders the first
    decoded payload with the renderer registered for that payload's type (or
    ``unavailable_summary`` when the call produced none), then appends the
    payload's warnings and the batch's errors. Subclasses implement only
    ``render_payload`` over their DTO.
    """

    __registry__: ClassVar[
        dict[McpDevOutputRendererKey, type["McpDevOutputRenderer"]]
    ] = {}
    __registry_key__ = "renderer_key"
    __key_extractor__ = mcp_dev_output_renderer_key
    __skip_if_no_key__ = True

    renderer_key: ClassVar[McpDevOutputRendererKey | None] = None
    output_contract: ClassVar[type | None] = None
    render_options_type: ClassVar[type[McpDevOutputRenderOptions]] = (
        McpDevOutputRenderOptions
    )
    unavailable_summary: ClassVar[str] = "Result: <unavailable>"

    def __init_subclass__(cls, **kwargs):
        super().__init_subclass__(**kwargs)
        # AutoRegisterMeta prefers an explicit (including inherited) key. A
        # child registers its own declaration, never its parent's key.
        cls.renderer_key = mcp_dev_output_renderer_key(cls.__name__, cls)

    @classmethod
    def for_output_contract(
        cls,
        output_contract: type | None,
    ) -> type["McpDevOutputRenderer"] | None:
        if output_contract is None:
            return None
        from openhcs.mcp.dev_client_renderers import (
            ensure_dev_client_renderers_registered,
        )

        ensure_dev_client_renderers_registered()
        return next(
            (
                cls.__registry__[owner]
                for owner in output_contract.__mro__
                if owner in cls.__registry__
            ),
            None,
        )

    @classmethod
    def render(cls, response, options: McpDevOutputRenderOptions | None = None) -> str:
        from openhcs.mcp.dev_client_core import McpDevToolBatchResponse

        decoded = McpDevToolBatchResponse.for_rendering(response)
        payload = next(
            (result.first_decoded_payload() for result in decoded.results), None
        )
        lines = [
            cls.unavailable_summary
            if payload is None
            else cls.render_payload_value(
                payload, cls.render_options_type() if options is None else options
            )
        ]
        lines.extend(cls.diagnostic_lines(decoded.diagnostic_errors()))
        return "\n".join(lines)

    @classmethod
    def render_payload(cls, payload, options: McpDevOutputRenderOptions) -> str:
        raise NotImplementedError(f"{cls.__name__} declares no payload presentation.")

    @classmethod
    def render_payload_value(cls, payload, options: McpDevOutputRenderOptions) -> str:
        """Render one decoded payload by its own type, with its warnings."""
        renderer_type = McpDevOutputRenderer.for_output_contract(type(payload))
        if renderer_type is None:
            raise TypeError(f"No renderer declared for {type(payload).__name__}")
        if not isinstance(options, renderer_type.render_options_type):
            options = renderer_type.render_options_type()
        warnings = renderer_type.presented_warnings(payload, options)
        return "\n".join(
            (
                renderer_type.render_payload(payload, options),
                *(
                    ("Warnings:", *diagnostic_lines(warnings))
                    if warnings
                    else ()
                ),
            )
        )

    @classmethod
    def presented_warnings(
        cls, payload, options: McpDevOutputRenderOptions
    ) -> tuple[AgentWarning, ...]:
        """The payload warnings this presentation shows (all, by default)."""
        del options
        return payload_warnings(payload)

    @staticmethod
    def diagnostic_lines(errors: Iterable[AgentError]) -> tuple[str, ...]:
        errors = tuple(errors)
        return ("Errors:", *diagnostic_lines(errors)) if errors else ()

    # Shared text vocabulary for presenting DTO attribute values.

    @staticmethod
    def text(value: object, *, absent_text: str = "<none>") -> str:
        if value is None:
            return absent_text
        if isinstance(value, Enum):
            return str(value.value)
        return str(value)

    @staticmethod
    def quoted(value: object) -> str:
        if value is None:
            return "<none>"
        return json.dumps(str(value))

    @staticmethod
    def sequence_text(values: Iterable[object] | None) -> str:
        items = () if values is None else tuple(values)
        if not items:
            return "<none>"
        return ",".join(McpDevOutputRenderer.text(item) for item in items)

    @staticmethod
    def json_text(value: object) -> str:
        if value is None:
            return "<none>"
        from python_introspect import to_jsonable

        return json.dumps(to_jsonable(value), sort_keys=True)

    @classmethod
    def json_value_count(cls, value: JsonValue) -> int:
        """Count preview scalars in the declared dynamic JSON value algebra."""
        if isinstance(value, list | tuple):
            return sum(cls.json_value_count(item) for item in value)
        if isinstance(value, Mapping):
            return sum(cls.json_value_count(item) for item in value.values())
        return 0 if value is None else 1

    @staticmethod
    def optional_lines(
        value: PresentationValue | None,
        render_lines: Callable[[PresentationValue], Sequence[str]],
    ) -> Sequence[str]:
        """Compose a nullable declared fact without repeating omission policy.

        None is the native absence fact; false, zero and empty strings remain
        present. Members own only the presentation of a present value.
        """
        return () if value is None else render_lines(value)


def diagnostic_lines(errors) -> tuple[str, ...]:
    """Group declared errors or warnings by message, showing at most three."""
    grouped_codes: dict[str, list[str]] = {}
    grouped_hints: dict[str, list[str]] = {}
    for error in errors:
        message = error.message
        hint = getattr(error, "hint", None)
        codes = grouped_codes.setdefault(message, [])
        if error.code not in codes:
            codes.append(error.code)
        hints = grouped_hints.setdefault(message, [])
        if hint is not None and json.dumps(str(hint)) not in hints:
            hints.append(json.dumps(str(hint)))

    lines: list[str] = []
    for message, codes in tuple(grouped_codes.items())[:3]:
        line = f"- {', '.join(codes)}: {message}"
        hint_texts = grouped_hints[message]
        if len(hint_texts) == 1:
            line += f" hint={hint_texts[0]}"
        elif len(hint_texts) > 1:
            line += f" hints={len(hint_texts)} distinct; pass --json for details"
        lines.append(line)
    remaining_group_count = len(grouped_codes) - len(lines)
    if remaining_group_count > 0:
        lines.append(f"... {remaining_group_count} more diagnostics")
    return tuple(lines)


class ToolListRenderer:
    """Compact renderer for the MCP ``tools/list`` response."""

    @classmethod
    def selected_tools(
        cls,
        response,
        *,
        contains: str | None,
        limit: int,
    ):
        return CatalogRenderOptions(contains=contains, limit=limit).select(
            response.tools,
            lambda tool: f"{tool.name} {tool.description or ''}",
        )

    @classmethod
    def project_response(cls, response, *, contains: str | None, limit: int):
        """The JSON view keeps full metadata for the selected tools only."""
        from dataclasses import replace

        from python_introspect import to_jsonable

        matched, visible = cls.selected_tools(
            response, contains=contains, limit=limit
        )
        projected = to_jsonable(replace(response, tools=visible))
        projected.update(
            {
                "matched_tool_count": len(matched),
                "returned_tool_count": len(visible),
                "truncated_tool_count": len(matched) - len(visible),
                "filter": {"contains": contains, "limit": max(limit, 0)},
            }
        )
        return projected

    @classmethod
    def render(
        cls,
        response,
        *,
        contains: str | None = None,
        limit: int = 80,
        grouped: bool = True,
    ) -> str:
        if response.errors:
            return "\n".join(("Tools: failed", *diagnostic_lines(response.errors)))
        tools, visible_tools = cls.selected_tools(
            response, contains=contains, limit=limit
        )
        lines = [
            f"Tools: matched={len(tools)} total={response.tool_count} "
            f"shown={len(visible_tools)}"
        ]
        if contains:
            lines.append(f"Filter: contains={contains}")
        if visible_tools:
            lines.append("Tool names:")
            lines.extend(
                cls._grouped_tool_lines(visible_tools)
                if grouped
                else cls._tool_lines(visible_tools)
            )
        if len(visible_tools) < len(tools):
            lines.append(f"...<truncated {len(tools) - len(visible_tools)} tools>")
        return "\n".join(lines)

    @staticmethod
    def _tool_lines(tools) -> list[str]:
        return [
            f"- {tool.name}: {McpDevOutputRenderer.text(tool.description)}"
            for tool in tools
        ]

    @classmethod
    def _grouped_tool_lines(cls, tools) -> list[str]:
        entries = tuple((tool, cls._capability_for_tool(tool.name)) for tool in tools)
        lines: list[str] = []
        for workflow_group in CapabilityWorkflowGroup:
            group_tools = tuple(
                tool
                for tool, capability in entries
                if capability is not None
                and capability.exposition.workflow_group is workflow_group
            )
            if group_tools:
                lines.append(f"[{workflow_group.title}]")
                lines.extend(cls._tool_lines(group_tools))
        ungrouped_tools = tuple(
            tool for tool, capability in entries if capability is None
        )
        if ungrouped_tools:
            lines.append("[Ungrouped]")
            lines.extend(cls._tool_lines(ungrouped_tools))
        return lines

    @staticmethod
    def _capability_for_tool(
        tool_name: str,
    ) -> type[AgentCapabilityDeclaration] | None:
        try:
            return get_agent_capability(tool_name)
        except KeyError:
            return None
