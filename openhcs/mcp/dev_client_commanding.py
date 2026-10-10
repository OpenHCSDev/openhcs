"""Command declaration framework for the MCP dev client."""

from __future__ import annotations

import argparse
from abc import ABC, abstractmethod
from dataclasses import dataclass
from collections.abc import Callable, Mapping
from contextlib import AbstractContextManager, nullcontext
import inspect
import json
import sys
import tempfile
from typing import ClassVar

from metaclass_registry import AutoRegisterMeta

from openhcs.agent.capabilities import (
    AgentCapabilityDeclaration,
    get_agent_capability,
    get_capability_registry,
    require_agent_type_contract,
)
from openhcs.agent.dto.common import AgentCliArgumentSpec, AgentCliRequest
from python_introspect import JsonObject, JsonValue
from openhcs.agent.dto.execution import (
    RuntimeServerConnectionToolRequest,
)
from openhcs.mcp.control_timeout import McpUiBridgeTimeoutPolicy
from openhcs.mcp.dev_client_core import (
    DEFAULT_CALL_TIMEOUT_SECONDS,
    McpDevCliUsageError,
    McpDevClientPhase,
    McpDevServerSpec,
    McpDevStdioSession,
    McpDevToolBatchResponse,
    McpDevToolCall,
    McpDevToolListResponse,
    McpToolArgumentAuthority,
    open_mcp_dev_session,
    add_request_factory_option,
    add_runtime_connection_options,
    add_ui_connection_options,
    add_viewer_connection_options,
    add_viewer_port_argument,
    call_mcp_session,
    captured_server_stderr_tail,
    list_mcp_session_tools,
    mcp_dev_command_key,
    mcp_tool_timeout_seconds,
    ui_tool_arguments,
    viewer_connection_arguments,
)
from openhcs.mcp.dev_client_rendering import (
    McpDevOutputRenderOptions,
    McpDevOutputRenderer,
    ToolListRenderer,
)


class McpDevCommandSpec(ABC, metaclass=AutoRegisterMeta):
    """Nominal parser, execution, and rendering owner for one MCP dev command."""

    __registry__: ClassVar[dict[str, type["McpDevCommandSpec"]]] = {}
    __registry_key__ = "command"
    __key_extractor__ = mcp_dev_command_key
    __skip_if_no_key__ = True

    command: ClassVar[str]
    help: ClassVar[str | None] = None
    aliases: ClassVar[tuple[str, ...]] = ()
    execution_phase: ClassVar[McpDevClientPhase] = McpDevClientPhase.CALL_TOOL
    default_timeout_seconds: ClassVar[float] = DEFAULT_CALL_TIMEOUT_SECONDS

    @classmethod
    def all_specs(cls) -> tuple["McpDevCommandSpec", ...]:
        explicit_specs = tuple(
            command_spec_type() for command_spec_type in cls.__registry__.values()
        )
        return (*explicit_specs, *generated_mcp_dev_command_specs())

    @classmethod
    def for_name(cls, command_name: str) -> "McpDevCommandSpec":
        command_spec_type = cls.__registry__.get(command_name)
        if command_spec_type is not None:
            return command_spec_type()
        generated_spec = generated_mcp_dev_command_spec_for_name(command_name)
        if generated_spec is not None:
            return generated_spec
        raise KeyError(command_name)

    def register_parser(
        self,
        subparsers: argparse._SubParsersAction,
        command_options: argparse.ArgumentParser,
    ) -> None:
        parser = subparsers.add_parser(
            self.command,
            aliases=self.parser_aliases(),
            help=self.parser_help(),
            parents=[command_options],
        )
        parser.set_defaults(command=self.command)
        self.configure_parser(parser)
        self.configure_reflected_parser(parser)

    def parser_help(self) -> str:
        return self.help or self.command

    def parser_aliases(self) -> tuple[str, ...]:
        return self.aliases

    def configure_parser(self, parser: argparse.ArgumentParser) -> None:
        """Add command-specific CLI arguments."""

    def configure_reflected_parser(self, parser: argparse.ArgumentParser) -> None:
        """Add options reflected from declarations owned outside the command."""

    def prepare_input(
        self,
        args: argparse.Namespace,
        *,
        stdin_context: Callable[[], AbstractContextManager[None]] = nullcontext,
    ) -> None:
        """Resolve declaration-owned input before building or submitting calls."""

    @abstractmethod
    def calls_from_args(
        self,
        args: argparse.Namespace,
    ) -> tuple[McpDevToolCall, ...]:
        """Build MCP tool calls for this command."""

    async def run(
        self,
        server_spec: McpDevServerSpec,
        args: argparse.Namespace,
    ) -> McpDevToolBatchResponse | McpDevToolListResponse:
        """Execute this command through one initialized MCP dev session."""
        self.prepare_input(args)
        prepared_calls = self.calls_from_args(args)
        for call in prepared_calls:
            call.require_surface_profile(server_spec.surface_profile)
        phase = McpDevClientPhase.START_SERVER
        with tempfile.TemporaryFile(
            mode="w+",
            encoding="utf-8",
            errors="replace",
        ) as server_stderr:
            try:
                async with open_mcp_dev_session(
                    server_spec,
                    server_stderr,
                    initialize_timeout_seconds=self.timeout_seconds(args),
                    use_resident_server=getattr(args, "resident_server", None),
                ) as session:
                    phase = self.execution_phase
                    payload = await self.run_session(
                        session,
                        args,
                        prepared_calls=prepared_calls,
                    )
                    phase = McpDevClientPhase.TEARDOWN
                    return payload
            except McpDevCliUsageError:
                raise
            except Exception as exc:
                return self.transport_failure_response(
                    server_spec,
                    phase,
                    exc,
                    server_stderr_tail=captured_server_stderr_tail(server_stderr),
                )

    async def run_session(
        self,
        session: McpDevStdioSession,
        args: argparse.Namespace,
        *,
        prepared_calls: tuple[McpDevToolCall, ...] | None = None,
    ) -> McpDevToolBatchResponse | McpDevToolListResponse:
        """Execute this command through an already initialized stdio session."""
        return await call_mcp_session(
            session,
            (self.calls_from_args(args) if prepared_calls is None else prepared_calls),
            timeout_seconds=self.timeout_seconds(args),
        )

    def timeout_seconds(self, args: argparse.Namespace) -> float:
        """Return the timeout shared by initialization and this command's calls."""
        return max(args.timeout_seconds, self.default_timeout_seconds)

    def transport_failure_response(
        self,
        server_spec: McpDevServerSpec,
        phase: McpDevClientPhase,
        exception: BaseException,
        *,
        server_stderr_tail: str | None,
    ) -> McpDevToolBatchResponse | McpDevToolListResponse:
        """Project a transport exception into this command's response shape."""
        return McpDevToolBatchResponse.from_transport_failure(
            server_spec,
            phase,
            exception,
            server_stderr_tail=server_stderr_tail,
        )

    def render_response(
        self,
        payload: JsonObject,
        args: argparse.Namespace,
    ) -> str:
        del args
        return json.dumps(payload, indent=2, sort_keys=True)

    def render_result(self, response, args: argparse.Namespace) -> str:
        """Render a framed production result without requiring a JSON round trip."""
        from python_introspect import to_jsonable

        return self.render_response(to_jsonable(response), args)

    def requests_json_output(self, args: argparse.Namespace) -> bool:
        """Project this command's declared output selection for shared rendering."""
        return args.json


class StdinSourceCommandSpec(McpDevCommandSpec):
    """Independent source-input capability composed with execution/rendering."""

    def prepare_input(
        self,
        args: argparse.Namespace,
        *,
        stdin_context: Callable[[], AbstractContextManager[None]] = nullcontext,
    ) -> None:
        super().prepare_input(args, stdin_context=stdin_context)
        if args.source_file == "-":
            with stdin_context():
                args.source_text = sys.stdin.read()
            args.source_file = None


class TypedCompositeCommandSpec(McpDevCommandSpec):
    """Composite commands consume the same decoded batch as their wire ingress."""

    def render_result(self, response, args: argparse.Namespace) -> str:
        if self.requests_json_output(args):
            from python_introspect import to_jsonable

            return super().render_response(to_jsonable(response), args)
        return self.render_response(response, args)


class CapabilityBackedCommandSpec(McpDevCommandSpec):
    """Command whose primary MCP tool capability is declared on the command."""

    capability: ClassVar[type[AgentCapabilityDeclaration]]
    __capability_registry__: ClassVar[
        dict[type[AgentCapabilityDeclaration], type["CapabilityBackedCommandSpec"]]
    ] = {}

    def __init_subclass__(cls, **kwargs: JsonValue) -> None:
        super().__init_subclass__(**kwargs)
        try:
            capability = cls.capability
        except AttributeError:
            return
        cls.__capability_registry__[capability] = cls

    @classmethod
    def for_capability_name(
        cls,
        tool_name: str,
    ) -> "CapabilityBackedCommandSpec | None":
        try:
            capability = get_agent_capability(tool_name)
        except KeyError:
            return None
        command_spec_type = cls.__capability_registry__.get(capability)
        if command_spec_type is not None:
            return command_spec_type()
        return generated_mcp_dev_command_spec_for_capability(capability)

    def call_render_args(
        self,
        tool_arguments: Mapping[str, JsonValue],
    ) -> argparse.Namespace:
        del tool_arguments
        argument_values: dict[str, object] = {"json": False}
        renderer_binding = self.output_renderer_binding()
        if renderer_binding is not None:
            argument_values.update(renderer_binding.default_cli_argument_values())
        return argparse.Namespace(**argument_values)

    def parser_help(self) -> str:
        return self.help or self.capability.title

    def parser_aliases(self) -> tuple[str, ...]:
        return self.aliases or self.capability.cli_aliases

    def output_renderer_binding(self):
        output_contract = self.capability.output_contract
        return McpDevOutputRenderer.for_output_contract(
            None
            if output_contract is None
            else require_agent_type_contract(output_contract)
        )

    def configure_reflected_parser(self, parser: argparse.ArgumentParser) -> None:
        renderer_binding = self.output_renderer_binding()
        if renderer_binding is not None:
            renderer_binding.configure_cli_parser(parser)

    def render_call_response(
        self,
        payload: JsonObject,
        tool_arguments: Mapping[str, JsonValue],
    ) -> str:
        return self.render_response(
            payload,
            self.call_render_args(tool_arguments),
        )

    def render_call_result(
        self, response, tool_arguments: Mapping[str, JsonValue]
    ) -> str:
        """Generic calls use the same nominal command contract as named calls."""
        return self.render_result(response, self.call_render_args(tool_arguments))

    def renderer_options(
        self,
        args: argparse.Namespace,
    ) -> McpDevOutputRenderOptions:
        renderer_binding = self.output_renderer_binding()
        if renderer_binding is None:
            return McpDevOutputRenderOptions()
        return renderer_binding.options_from_cli_args(args)

    def render_response(
        self,
        payload: JsonObject,
        args: argparse.Namespace,
    ) -> str:
        if self.requests_json_output(args):
            return super().render_response(payload, args)
        renderer_binding = self.output_renderer_binding()
        if renderer_binding is None:
            return super().render_response(payload, args)
        return renderer_binding.render_with_options(
            payload, self.renderer_options(args)
        )

    def render_result(self, response, args: argparse.Namespace) -> str:
        binding = self.output_renderer_binding()
        if self.requests_json_output(args) or binding is None:
            return super().render_result(response, args)
        return binding.render_result(response, self.renderer_options(args))


class ToolsCommandSpec(McpDevCommandSpec):
    command = "tools"
    help = "List current-source MCP tools."
    execution_phase = McpDevClientPhase.LIST_TOOLS

    def configure_parser(self, parser: argparse.ArgumentParser) -> None:
        parser.add_argument("--contains")
        parser.add_argument("--limit", type=int, default=80)
        parser.add_argument(
            "--flat",
            action="store_true",
            help="Render a flat tool list instead of grouping by capability declarations.",
        )
        parser.add_argument(
            "--json",
            action="store_true",
            help=(
                "Render structured MCP JSON, preserving full metadata for entries "
                "selected by --contains and --limit."
            ),
        )

    def calls_from_args(
        self,
        args: argparse.Namespace,
    ) -> tuple[McpDevToolCall, ...]:
        return ()

    async def run_session(
        self,
        session: McpDevStdioSession,
        args: argparse.Namespace,
        *,
        prepared_calls: tuple[McpDevToolCall, ...] | None = None,
    ) -> McpDevToolListResponse:
        del prepared_calls
        return await list_mcp_session_tools(
            session,
            timeout_seconds=self.timeout_seconds(args),
        )

    def transport_failure_response(
        self,
        server_spec: McpDevServerSpec,
        phase: McpDevClientPhase,
        exception: BaseException,
        *,
        server_stderr_tail: str | None,
    ) -> McpDevToolListResponse:
        return McpDevToolListResponse.from_transport_failure(
            server_spec,
            phase,
            exception,
            server_stderr_tail=server_stderr_tail,
        )

    def render_response(
        self,
        payload: JsonObject,
        args: argparse.Namespace,
    ) -> str:
        if args.json:
            return super().render_response(
                ToolListRenderer.project_response(
                    payload,
                    contains=args.contains,
                    limit=args.limit,
                ),
                args,
            )
        return ToolListRenderer.render(
            payload,
            contains=args.contains,
            limit=args.limit,
            grouped=not args.flat,
        )

    def call_render_args(
        self,
        tool_arguments: Mapping[str, JsonValue],
    ) -> argparse.Namespace:
        del tool_arguments
        return argparse.Namespace(json=False, contains=None, limit=20, flat=False)


class SingleToolCommandSpec(CapabilityBackedCommandSpec):
    """Command that maps to one MCP tool call."""

    @property
    def tool_name(self) -> str:
        return self.capability.name

    def tool_arguments(self, args: argparse.Namespace) -> dict[str, JsonValue]:
        return {}

    def calls_from_args(
        self,
        args: argparse.Namespace,
    ) -> tuple[McpDevToolCall, ...]:
        try:
            tool_arguments = self.tool_arguments(args)
        except McpDevCliUsageError:
            raise
        except (TypeError, ValueError) as exc:
            # Manual command projections construct the same declaration-owned
            # request DTOs as generated commands. Preserve their validation as
            # a local usage failure instead of a transport failure or traceback.
            raise McpDevCliUsageError(str(exc)) from exc
        return (
            McpDevToolCall(
                self.tool_name,
                tool_arguments,
            ),
        )


class UiBridgeCommandSpec(McpDevCommandSpec):
    """Command specification that accepts live UI bridge connection options."""

    def configure_parser(self, parser: argparse.ArgumentParser) -> None:
        add_ui_connection_options(parser)


class SingleUiBridgeToolCommandSpec(UiBridgeCommandSpec, CapabilityBackedCommandSpec):
    """UI bridge command whose entire operation is one MCP tool call."""

    capability: ClassVar[type[AgentCapabilityDeclaration]]

    def configure_parser(self, parser: argparse.ArgumentParser) -> None:
        super().configure_parser(parser)
        parser.add_argument(
            "--json",
            action="store_true",
            help="Render the complete MCP JSON response instead of a compact summary.",
        )

    @property
    def tool_name(self) -> str:
        return self.capability.name

    def calls_from_args(
        self,
        args: argparse.Namespace,
    ) -> tuple[McpDevToolCall, ...]:
        return (
            McpDevToolCall(
                self.tool_name,
                ui_tool_arguments(args, timeout_ms=args.timeout_ms),
            ),
        )

    async def run_session(
        self,
        session: McpDevStdioSession,
        args: argparse.Namespace,
        *,
        prepared_calls: tuple[McpDevToolCall, ...] | None = None,
    ) -> McpDevToolBatchResponse:
        """Keep the MCP deadline outside the request-owned bridge deadline."""

        timeout_ms = McpUiBridgeTimeoutPolicy.resolve(args.timeout_ms)
        return await call_mcp_session(
            session,
            self.calls_from_args(args) if prepared_calls is None else prepared_calls,
            timeout_seconds=mcp_tool_timeout_seconds(
                timeout_ms,
                timeout_seconds=self.timeout_seconds(args),
            ),
        )


@dataclass(frozen=True, slots=True)
class AgentCliRequestProjection:
    """CLI options and tool arguments projected from one ``AgentCliRequest``.

    Runtime-server connection requests share the dev client's connection
    options instead of restating their connection fields per command.
    """

    request_type: type[AgentCliRequest]

    @property
    def request_factory(self):
        return self.request_type.agent_cli_factory()

    @property
    def uses_runtime_connection_options(self) -> bool:
        return issubclass(self.request_type, RuntimeServerConnectionToolRequest)

    @staticmethod
    def runtime_connection_parameter_names() -> frozenset[str]:
        return frozenset(
            inspect.signature(RuntimeServerConnectionToolRequest.from_fields).parameters
        )

    def request_factory_parameters(self) -> tuple[inspect.Parameter, ...]:
        runtime_connection_names = (
            self.runtime_connection_parameter_names()
            if self.uses_runtime_connection_options
            else frozenset()
        )
        return tuple(
            parameter
            for parameter in inspect.signature(self.request_factory).parameters.values()
            if parameter.name not in runtime_connection_names
        )

    def configure_parser(self, parser: argparse.ArgumentParser) -> None:
        if self.uses_runtime_connection_options:
            add_runtime_connection_options(parser, include_port=True)
        argument_specs = {
            argument_spec.field_name: argument_spec
            for argument_spec in self.request_type.agent_cli_argument_specs()
        }
        for parameter in self.request_factory_parameters():
            argument_spec = argument_specs.get(parameter.name)
            add_request_factory_option(
                parser,
                self.request_factory,
                parameter.name,
                *self.argument_flags(parameter.name, argument_spec),
                **self.argument_kwargs(argument_spec),
            )

    @staticmethod
    def argument_flags(
        field_name: str,
        argument_spec: AgentCliArgumentSpec | None,
    ) -> tuple[str, ...]:
        if argument_spec is not None and argument_spec.positional:
            return (field_name,)
        if argument_spec is not None and argument_spec.flags:
            return argument_spec.flags
        return (f"--{field_name.replace('_', '-')}",)

    @staticmethod
    def argument_kwargs(
        argument_spec: AgentCliArgumentSpec | None,
    ) -> dict[str, object]:
        if argument_spec is None:
            return {}
        declared = {
            "nargs": argument_spec.nargs,
            "action": argument_spec.action,
            "help": argument_spec.help,
        }
        return {key: value for key, value in declared.items() if value is not None}

    def tool_arguments(self, args: argparse.Namespace) -> dict[str, JsonValue]:
        argument_values = vars(args)
        field_names = (
            *(
                self.runtime_connection_parameter_names()
                if self.uses_runtime_connection_options
                else ()
            ),
            *(parameter.name for parameter in self.request_factory_parameters()),
        )
        try:
            request = self.request_factory(
                **{field_name: argument_values[field_name] for field_name in field_names}
            )
        except (TypeError, ValueError) as exc:
            raise McpDevCliUsageError(str(exc)) from exc
        return McpToolArgumentAuthority.from_payload(request.as_tool_arguments())


class McpDevCliProjection:
    """Dev-client argument primitives a capability invocation composes."""

    @staticmethod
    def configure_ui_connection(parser: argparse.ArgumentParser) -> None:
        add_ui_connection_options(parser)

    @staticmethod
    def ui_connection_arguments(args: argparse.Namespace) -> dict[str, JsonValue]:
        return ui_tool_arguments(args, timeout_ms=args.timeout_ms)

    @staticmethod
    def ui_timeout_seconds(args: argparse.Namespace, timeout_seconds: float) -> float:
        """Keep the MCP deadline outside the request-owned bridge deadline."""
        return mcp_tool_timeout_seconds(
            McpUiBridgeTimeoutPolicy.resolve(args.timeout_ms),
            timeout_seconds=timeout_seconds,
        )

    @staticmethod
    def configure_viewer_connection(parser: argparse.ArgumentParser) -> None:
        add_viewer_port_argument(parser)
        add_viewer_connection_options(parser)

    @staticmethod
    def viewer_connection_arguments(args: argparse.Namespace) -> dict[str, JsonValue]:
        return viewer_connection_arguments(args)

    @staticmethod
    def configure_request(parser: argparse.ArgumentParser, request_type: type) -> None:
        if issubclass(request_type, AgentCliRequest):
            AgentCliRequestProjection(request_type).configure_parser(parser)

    @staticmethod
    def request_tool_arguments(
        args: argparse.Namespace,
        request_type: type,
    ) -> dict[str, JsonValue]:
        if issubclass(request_type, AgentCliRequest):
            return AgentCliRequestProjection(request_type).tool_arguments(args)
        return {}


class GeneratedCapabilityCommandSpec(SingleToolCommandSpec):
    """Command projected from a capability declaration through its invocation."""

    def __init__(self, capability: type[AgentCapabilityDeclaration]) -> None:
        self.capability = capability
        self.command = capability.cli_command

    def configure_parser(self, parser: argparse.ArgumentParser) -> None:
        self.capability.invocation.configure_cli(
            self.capability, parser, McpDevCliProjection
        )
        parser.add_argument(
            "--json",
            action="store_true",
            help="Render the complete MCP JSON response instead of a compact summary.",
        )

    def tool_arguments(self, args: argparse.Namespace) -> dict[str, JsonValue]:
        return self.capability.invocation.cli_tool_arguments(
            self.capability, args, McpDevCliProjection
        )

    def timeout_seconds(self, args: argparse.Namespace) -> float:
        return self.capability.invocation.cli_timeout_seconds(
            args, super().timeout_seconds(args), McpDevCliProjection
        )


def generated_mcp_dev_command_specs() -> tuple[CapabilityBackedCommandSpec, ...]:
    explicit_capabilities = frozenset(
        CapabilityBackedCommandSpec.__capability_registry__
    )
    return tuple(
        GeneratedCapabilityCommandSpec(capability)
        for capability in get_capability_registry().capabilities
        if capability.cli_command is not None
        and capability not in explicit_capabilities
    )


def generated_mcp_dev_command_spec_for_name(
    command_name: str,
) -> CapabilityBackedCommandSpec | None:
    for command_spec in generated_mcp_dev_command_specs():
        if command_spec.command == command_name:
            return command_spec
    return None


def generated_mcp_dev_command_spec_for_capability(
    capability: type[AgentCapabilityDeclaration],
) -> CapabilityBackedCommandSpec | None:
    if (
        capability.cli_command is None
        or capability in CapabilityBackedCommandSpec.__capability_registry__
    ):
        return None
    return GeneratedCapabilityCommandSpec(capability)
