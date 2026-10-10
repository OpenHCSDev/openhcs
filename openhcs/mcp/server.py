"""MCP server adapter for the OpenHCS agent API."""

from __future__ import annotations

import asyncio
import faulthandler
import logging
import os
import sys
import time
from collections.abc import Awaitable, Callable, Mapping
from contextlib import contextmanager
from dataclasses import (
    dataclass,
    is_dataclass,
    replace,
)
from dataclasses import (
    fields as dataclass_fields,
)
from enum import Enum
from functools import cached_property, wraps
from inspect import (
    Parameter,
    Signature,
    getsourcefile,
    iscoroutinefunction,
)
from inspect import (
    signature as inspect_signature,
)
from pathlib import Path
from typing import Annotated, Any, Self, get_type_hints

from pydantic import Field as PydanticField
from pydantic import WithJsonSchema
from pyqt_reactive.services.window_snapshot import WindowSnapshotCaptureScope
from python_introspect import JsonValue, dataclass_from_mapping, to_jsonable
from zmqruntime.config import TransportMode
from zmqruntime.startup import EndpointStartupStatus

import openhcs as openhcs_package
from openhcs.agent.capabilities import (
    AgentCapabilityDeclaration,
    AgentCapabilityInvocation,
    AgentCapabilityRegistry,
    AgentCapabilitySurfaceSelection,
    CapabilityTransport,
    FullLocalCapabilitySurfaceProfile,
    LocalCapabilitySurfaceProfile,
    agent_capability_declarations,
    get_capability_registry,
    require_agent_type_contract,
)
from openhcs.agent.dto.common import (
    AGENT_PARAMETER_DESCRIPTION_METADATA_KEY,
    AGENT_PARAMETER_PRODUCER_OUTPUT_CONTRACT_METADATA_KEY,
    SCHEMA_VERSION,
    AgentError,
)
from openhcs.agent.dto.execution import (
    ExecutionConnectionSpec,
)
from openhcs.agent.dto.mcp import (
    McpServerHealthResult,
    McpServerStaleErrorResult,
    McpToolErrorResult,
)
from openhcs.agent.dto.ui_bridge import (
    UiBridgeConnectionRequest,
    UiBridgeConnectionSpec,
)
from openhcs.agent.dto.viewer import ViewerWindowControlRequest
from openhcs.agent.exceptions import AgentFacingErrorMixin
from openhcs.agent.knowledge_manifest import knowledge_base_source_paths_from_manifest
from openhcs.mcp.bootstrap import MCP_VERBOSE_ENVIRONMENT_VARIABLE
from openhcs.mcp.context import (
    OpenHCSAgentContext,
    create_agent_context,
)
from openhcs.mcp.control_timeout import (
    McpControlTimeoutPolicy,
    McpUiBridgeTimeoutPolicy,
    McpViewerTimeoutPolicy,
)
from openhcs.mcp.execution import McpMainThreadDispatcher
from openhcs.mcp.lifecycle import (
    McpProcessLifecycle,
    McpProcessRecoveryStatus,
)

MCP_SERVER_INSTRUCTIONS = CapabilityTransport.LOCAL_STDIO.server_instructions()


def _request_parameter_annotation(
    request_type: type,
    parameter_name: str,
    annotation,
):
    """Project declaration-owned request field help into FastMCP JSON Schema."""

    if not is_dataclass(request_type):
        return annotation
    request_field = next(
        (
            item
            for item in dataclass_fields(request_type)
            if item.name == parameter_name
        ),
        None,
    )
    if request_field is None:
        return annotation
    description = request_field.metadata.get(AGENT_PARAMETER_DESCRIPTION_METADATA_KEY)
    if not isinstance(description, str) or not description:
        return annotation
    producer_output_contract = request_field.metadata.get(
        AGENT_PARAMETER_PRODUCER_OUTPUT_CONTRACT_METADATA_KEY
    )
    if producer_output_contract is not None:
        producer_names = tuple(
            declaration.name
            for declaration in agent_capability_declarations()
            if declaration.output_contract is producer_output_contract
            and declaration.name is not None
        )
        if len(producer_names) != 1:
            raise TypeError(
                f"{request_type.__name__}.{parameter_name} requires exactly one "
                "capability producer for its declared output contract; found "
                f"{producer_names!r}."
            )
        description = (
            f"{description} Required producer capability: {producer_names[0]}."
        )
    return Annotated[annotation, PydanticField(description=description)]


def _timeout_parameter_annotation(
    timeout_policy: type[McpControlTimeoutPolicy],
):
    """Project one timeout policy's authoritative bounds into JSON Schema."""

    return Annotated[
        int | None,
        PydanticField(
            description=(
                f"Bounded {timeout_policy.label.lower()} timeout in milliseconds "
                f"({timeout_policy.min_ms}..{timeout_policy.max_ms})."
            )
        ),
        WithJsonSchema(
            {
                "anyOf": [
                    {
                        "type": "integer",
                        "minimum": timeout_policy.min_ms,
                        "maximum": timeout_policy.max_ms,
                    },
                    {"type": "null"},
                ]
            }
        ),
    ]


_McpUiBridgeTimeoutParameter = _timeout_parameter_annotation(McpUiBridgeTimeoutPolicy)


MCP_HOSTED_SERVER_INSTRUCTIONS = (
    CapabilityTransport.HOSTED_STREAMABLE_HTTP.server_instructions()
)


class McpInvocationOutcome(str, Enum):
    """Transport-neutral result observed for one MCP capability invocation."""

    SUCCEEDED = "succeeded"
    FAILED = "failed"
    BLOCKED_STALE = "blocked_stale"


McpInvocationObserver = Callable[
    [type[AgentCapabilityDeclaration], McpInvocationOutcome],
    None,
]
_LOGGER = logging.getLogger(__name__)


@dataclass(frozen=True, slots=True)
class McpSourceSnapshot:
    exists: bool
    mtime_ns: int | None

    @classmethod
    def from_path(cls, source_path: Path) -> "McpSourceSnapshot":
        try:
            stat_result = source_path.stat()
        except FileNotFoundError:
            return cls(exists=False, mtime_ns=None)
        return cls(
            exists=True,
            mtime_ns=stat_result.st_mtime_ns,
        )


def _source_path_for_type(source_type: type) -> Path:
    source_file = getsourcefile(source_type)
    if source_file is None:
        raise RuntimeError(f"No source file available for {source_type.__qualname__}")
    return Path(source_file).resolve()


def _deduplicate_source_paths(source_paths: tuple[Path, ...]) -> tuple[Path, ...]:
    return tuple(dict.fromkeys(source_paths))


def _package_python_source_paths(package) -> tuple[Path, ...]:
    return tuple(
        sorted(
            path.resolve()
            for location in package.__path__
            for path in Path(location).rglob("*.py")
        )
    )


MCP_SERVER_PACKAGED_RESOURCE_PATHS = knowledge_base_source_paths_from_manifest()
MCP_SERVER_SOURCE_PATHS = _deduplicate_source_paths(
    (
        Path(__file__).resolve(),
        Path(create_agent_context.__code__.co_filename).resolve(),
        Path(get_capability_registry.__code__.co_filename).resolve(),
        Path(to_jsonable.__code__.co_filename).resolve(),
        _source_path_for_type(WindowSnapshotCaptureScope),
        *_package_python_source_paths(openhcs_package),
        *MCP_SERVER_PACKAGED_RESOURCE_PATHS,
    )
)
MCP_SERVER_IMPORT_SOURCE_SNAPSHOTS = {
    source_path: McpSourceSnapshot.from_path(source_path)
    for source_path in MCP_SERVER_SOURCE_PATHS
}
MCP_SERVER_IMPORT_SOURCE_MTIMES_NS = {
    source_path: snapshot.mtime_ns
    for source_path, snapshot in MCP_SERVER_IMPORT_SOURCE_SNAPSHOTS.items()
    if snapshot.mtime_ns is not None
}
MCP_SERVER_SOURCE_PATH = MCP_SERVER_SOURCE_PATHS[0]
MCP_SERVER_OPENHCS_VERSION = openhcs_package.__version__


def _required_mcp_source_mtime_ns(source_path: Path) -> int:
    snapshot = MCP_SERVER_IMPORT_SOURCE_SNAPSHOTS[source_path]
    if snapshot.mtime_ns is None:
        raise RuntimeError(f"MCP source path is missing at import: {source_path}")
    return snapshot.mtime_ns


MCP_SERVER_IMPORT_MTIME_NS = _required_mcp_source_mtime_ns(MCP_SERVER_SOURCE_PATH)
MCP_SERVER_PROCESS_ID = os.getpid()
MCP_SERVER_IMPORTED_AT_UNIX = time.time()
MCP_SERVER_PROCESS_LIFECYCLE = McpProcessLifecycle.from_environment(
    fallback_restart_command=(sys.executable, "-m", "openhcs.mcp"),
)


def _mcp_server_current_source_mtime_ns() -> int | None:
    try:
        return MCP_SERVER_SOURCE_PATH.stat().st_mtime_ns
    except FileNotFoundError:
        return None


def _mcp_server_stale_source_paths() -> tuple[Path, ...]:
    return tuple(
        source_path
        for source_path, import_snapshot in MCP_SERVER_IMPORT_SOURCE_SNAPSHOTS.items()
        if McpSourceSnapshot.from_path(source_path) != import_snapshot
    )


def _mcp_server_recovery_status(
    stale_source_paths: tuple[Path, ...] | None = None,
) -> McpProcessRecoveryStatus:
    resolved_stale_paths = (
        _mcp_server_stale_source_paths()
        if stale_source_paths is None
        else stale_source_paths
    )
    return MCP_SERVER_PROCESS_LIFECYCLE.recovery_status(
        source_changed=bool(resolved_stale_paths),
    )


def _mcp_server_process_generation_changed_since_import() -> bool:
    return _mcp_server_recovery_status().restart_required


def _mcp_server_restart_command() -> tuple[str, ...]:
    """Return the current lifecycle-owned reconnect command."""
    return _mcp_server_recovery_status().restart_command


def _mcp_server_missing_packaged_resource_paths() -> tuple[Path, ...]:
    """Return declared knowledge resources absent from this installation."""
    return tuple(
        resource_path
        for resource_path in MCP_SERVER_PACKAGED_RESOURCE_PATHS
        if not resource_path.is_file()
    )


def _mcp_tool_annotations(capability: type[AgentCapabilityDeclaration]):
    """Project standard MCP hints from the authoritative capability metadata."""
    from mcp.types import ToolAnnotations

    open_world = bool(
        capability.side_effects
        or capability.requires_network
        or capability.data_exposure
        or capability.security_requirements
    )
    return ToolAnnotations(
        title=capability.title,
        readOnlyHint=capability.read_only,
        destructiveHint=not capability.read_only,
        idempotentHint=capability.read_only,
        openWorldHint=open_world,
    )


def _mcp_tool_meta(capability: type[AgentCapabilityDeclaration]) -> dict[str, str]:
    """Advertise the nominal result owner alongside the JSON object schema."""
    output_contract = require_agent_type_contract(capability.output_contract)
    return {"openhcs/outputContract": output_contract.__name__}


def _mcp_transport_projected_result(
    capability: type[AgentCapabilityDeclaration],
    result,
    selection: AgentCapabilitySurfaceSelection,
):
    """Project transport-sensitive nominal results without capability-name checks."""
    if capability.output_contract is AgentCapabilityRegistry:
        return to_jsonable(
            get_capability_registry(selection.transport, selection.local_profile)
        )
    return result


async def _await_with_declared_progress(
    capability: type[AgentCapabilityDeclaration],
    mcp_context,
    operation: Awaitable[object],
) -> object:
    """Relay original endpoint statuses while awaiting one declared operation."""

    heartbeat_seconds = capability.progress_heartbeat_seconds
    if heartbeat_seconds is None:
        return await operation
    await _report_progress_if_available(
        mcp_context,
        0.0,
        message=f"{capability.title}: started",
    )
    loop = asyncio.get_running_loop()
    started = loop.time()
    statuses: asyncio.Queue[EndpointStartupStatus] = asyncio.Queue()
    active = True

    def publish(status: EndpointStartupStatus) -> None:
        # A cancelled to_thread await cannot stop its worker. Late callbacks
        # must not report into a terminal MCP request or a closed event loop.
        if active:
            loop.call_soon_threadsafe(statuses.put_nowait, status)

    message = capability.title

    async def report_status(status: EndpointStartupStatus) -> None:
        nonlocal message
        message = f"{capability.title}: {status.phase.value}: {status.message}"
        await _report_progress_if_available(
            mcp_context, loop.time() - started, message=message
        )

    with EndpointStartupStatus.callback_scope(publish):
        task = asyncio.ensure_future(operation)
        next_status = asyncio.create_task(statuses.get())
        try:
            while True:
                completed, _ = await asyncio.wait(
                    {task, next_status},
                    timeout=heartbeat_seconds,
                    return_when=asyncio.FIRST_COMPLETED,
                )
                if next_status in completed:
                    await report_status(next_status.result())
                    next_status = asyncio.create_task(statuses.get())
                if task in completed:
                    # Flush already emitted terminal statuses before returning
                    # the original result/error. No endpoint observation here.
                    while not statuses.empty():
                        await report_status(statuses.get_nowait())
                    return task.result()
                if not completed:
                    await _report_progress_if_available(
                        mcp_context,
                        loop.time() - started,
                        message=f"{message}: still running",
                    )
        finally:
            active = False
            next_status.cancel()
            task.cancel()
            await asyncio.gather(next_status, task, return_exceptions=True)


async def _report_progress_if_available(
    mcp_context,
    progress: float,
    *,
    message: str,
) -> None:
    """Report standard MCP progress when execution has a request context."""

    try:
        mcp_context.request_context
    except ValueError:
        # FastMCP's direct ``call_tool`` test/application seam has no request
        # context. The same tool still needs to execute correctly there.
        return
    await mcp_context.report_progress(progress, message=message)


@contextmanager
def _verbose_blocking_operation_diagnostics(capability: type[AgentCapabilityDeclaration]):
    """Dump a blocked invocation without affecting normal MCP output."""

    heartbeat_seconds = capability.progress_heartbeat_seconds
    if heartbeat_seconds is None or os.getenv(MCP_VERBOSE_ENVIRONMENT_VARIABLE) is None:
        yield
        return
    dump_after_seconds = max(30.0, heartbeat_seconds * 3.0)
    faulthandler.dump_traceback_later(
        dump_after_seconds,
        repeat=False,
        file=sys.stderr,
    )
    try:
        yield
    finally:
        faulthandler.cancel_dump_traceback_later()


def _mcp_server_health() -> McpServerHealthResult:
    """Report this serving process's identity, freshness and recovery contract."""
    current_source_mtime_ns = _mcp_server_current_source_mtime_ns()
    stale_source_paths = _mcp_server_stale_source_paths()
    recovery = _mcp_server_recovery_status(stale_source_paths)
    missing_packaged_resource_paths = _mcp_server_missing_packaged_resource_paths()
    return McpServerHealthResult(
        schema_version=SCHEMA_VERSION,
        status="ok",
        started_at_unix=MCP_SERVER_IMPORTED_AT_UNIX,
        service="openhcs.mcp",
        openhcs_version=MCP_SERVER_OPENHCS_VERSION,
        packaged_resources_ready=not missing_packaged_resource_paths,
        packaged_resource_count=len(MCP_SERVER_PACKAGED_RESOURCE_PATHS),
        missing_packaged_resource_paths=tuple(
            str(resource_path) for resource_path in missing_packaged_resource_paths
        ),
        server_process_id=MCP_SERVER_PROCESS_ID,
        server_source_path=str(MCP_SERVER_SOURCE_PATH),
        server_import_mtime_ns=MCP_SERVER_IMPORT_MTIME_NS,
        server_current_mtime_ns=current_source_mtime_ns,
        server_source_changed_since_import=bool(stale_source_paths),
        stale_source_paths=tuple(str(source_path) for source_path in stale_source_paths),
        recovery_reason=recovery.reason.value,
        installation_pointer_path=recovery.installation_pointer_path,
        installation_pointer_changed_since_import=(
            recovery.installation_pointer_changed_since_import
        ),
        installation_pointer_available=recovery.installation_pointer_available,
        restart_required=recovery.restart_required,
        restart_command=recovery.restart_command,
        restart_command_is_stable=recovery.restart_command_is_stable,
        reconnect_required=recovery.reconnect_required,
        reconnect_owner=(
            None if recovery.reconnect_owner is None else recovery.reconnect_owner.value
        ),
        retry_after_reconnect=recovery.retry_after_reconnect,
        automatic_recovery_on_reconnect=(recovery.automatic_recovery_on_reconnect),
        restart_hint=recovery.hint,
    )


def _mcp_resource_function_name(resource_name: str) -> str:
    return (
        resource_name.replace("://", "_")
        .replace("/", "_")
        .replace("-", "_")
        .replace(":", "_")
    )


class McpCapabilityBinder:
    """MCP transport primitives an invocation composes into its tool or resource.

    Each capability's invocation decides its parameters, decoding and execution;
    this port supplies what only the MCP server owns: FastMCP registration, JSON
    Schema annotation, connection resolution, the surface-selected registry and
    the serving process's health.
    """

    def __init__(
        self,
        *,
        context: OpenHCSAgentContext,
        server,
        selection: AgentCapabilitySurfaceSelection,
        openhcs_tool,
        observe_invocation,
    ) -> None:
        self.context = context
        self._server = server
        self._selection = selection
        self._openhcs_tool = openhcs_tool
        self._observe_invocation = observe_invocation

    @cached_property
    def selected_registry(self) -> AgentCapabilityRegistry:
        return get_capability_registry(
            self._selection.transport,
            self._selection.local_profile,
        )

    def register_tool(
        self,
        declaration: type[AgentCapabilityDeclaration],
        invocation: AgentCapabilityInvocation,
    ) -> None:
        tool_signature = Signature(
            parameters=invocation.tool_parameters(declaration, self),
            return_annotation=dict,
        )

        def tool(**kwargs: JsonValue) -> dict:
            bound_arguments = tool_signature.bind_partial(**kwargs)
            bound_arguments.apply_defaults()
            return to_jsonable(
                invocation.invoke(declaration, self, bound_arguments.arguments)
            )

        self._describe(tool, declaration.name, declaration, tool_signature)
        self._openhcs_tool(
            capability=declaration,
            allow_stale_server=invocation.allow_stale_server,
        )(tool)

    def register_resource(
        self,
        declaration: type[AgentCapabilityDeclaration],
        invocation: AgentCapabilityInvocation,
    ) -> None:
        def resource() -> dict:
            if _mcp_server_process_generation_changed_since_import():
                self._observe_invocation(
                    declaration, McpInvocationOutcome.BLOCKED_STALE
                )
                return _mcp_server_stale_error(declaration.name)
            try:
                projected_result = _mcp_transport_projected_result(
                    declaration,
                    to_jsonable(invocation.invoke(declaration, self, {})),
                    self._selection,
                )
            except Exception:
                self._observe_invocation(declaration, McpInvocationOutcome.FAILED)
                raise
            self._observe_invocation(declaration, McpInvocationOutcome.SUCCEEDED)
            return projected_result

        self._describe(
            resource,
            _mcp_resource_function_name(declaration.name),
            declaration,
            Signature(return_annotation=dict),
        )
        self._server.resource(declaration.name)(resource)

    @staticmethod
    def _describe(function, name: str, declaration, function_signature) -> None:
        function.__name__ = name
        function.__qualname__ = name
        function.__doc__ = declaration.description
        function.__annotations__ = {
            parameter.name: parameter.annotation
            for parameter in function_signature.parameters.values()
        } | {"return": dict}
        function.__signature__ = function_signature

    @staticmethod
    def request_annotation(request_type: type, parameter_name: str, annotation):
        return _request_parameter_annotation(request_type, parameter_name, annotation)

    @staticmethod
    def ui_connection_parameter() -> Parameter:
        return Parameter(
            "connection",
            Parameter.KEYWORD_ONLY,
            default=None,
            annotation=McpUiBridgeConnectionRequest | None,
        )

    def ui_connection(self, arguments: Mapping[str, JsonValue]) -> UiBridgeConnectionSpec:
        return UiBridgeConnectionToolArgs.from_request(arguments["connection"]).resolve(
            self.context
        )

    @staticmethod
    def viewer_connection_parameters() -> tuple[Parameter, ...]:
        return McpViewerConnectionToolFields.signature_parameters(McpViewerTimeoutPolicy)

    @staticmethod
    def viewer_control(
        arguments: Mapping[str, JsonValue],
    ) -> "McpViewerConnectionToolArgs":
        return McpViewerConnectionToolFields.from_tool_arguments(
            arguments
        ).to_control_args(McpViewerTimeoutPolicy)

    @staticmethod
    def server_health() -> McpServerHealthResult:
        return _mcp_server_health()


def build_server(
    context: OpenHCSAgentContext | None = None,
    *,
    fastmcp_factory=None,
    capability_transport: CapabilityTransport = CapabilityTransport.LOCAL_STDIO,
    capability_surface_profile: LocalCapabilitySurfaceProfile | None = None,
    invocation_observer: McpInvocationObserver | None = None,
    main_thread_dispatcher: McpMainThreadDispatcher | None = None,
):
    """Build the transport-neutral FastMCP surface without importing GUI services.

    ``fastmcp_factory`` is the construction seam for a separately configured
    transport wrapper. It must accept the canonical server name and instructions;
    authentication and transport security remain the wrapper's responsibility.
    """
    if fastmcp_factory is None:
        try:
            from mcp.server.fastmcp import FastMCP
        except ImportError as exc:
            raise RuntimeError(
                "The OpenHCS MCP server requires the optional 'mcp' dependency. "
                "Install with `pip install -e .[mcp]`."
            ) from exc
        fastmcp_factory = FastMCP

    ctx = context or create_agent_context()
    dispatcher = (
        main_thread_dispatcher
        if main_thread_dispatcher is not None
        else McpMainThreadDispatcher()
    )
    from openhcs.authoring.session.session import DispatcherThread

    ctx.bind_main_thread(DispatcherThread(dispatcher))
    capability_surface_selection = AgentCapabilitySurfaceSelection(
        transport=capability_transport,
        local_profile=(
            FullLocalCapabilitySurfaceProfile()
            if capability_surface_profile is None
            else capability_surface_profile
        ),
    )
    server = fastmcp_factory(
        "OpenHCS",
        instructions=capability_transport.server_instructions(),
    )

    def observe_invocation(
        capability: type[AgentCapabilityDeclaration],
        outcome: McpInvocationOutcome,
    ) -> None:
        if invocation_observer is None:
            return
        try:
            invocation_observer(capability, outcome)
        except Exception:
            _LOGGER.exception(
                "OpenHCS MCP invocation observer failed for %s",
                capability.name,
            )

    def openhcs_tool(
        *,
        capability: type[AgentCapabilityDeclaration],
        allow_stale_server: bool = False,
    ):
        def decorator(fn):
            def stale_result():
                if (
                    allow_stale_server
                    or not _mcp_server_process_generation_changed_since_import()
                ):
                    return None
                observe_invocation(
                    capability,
                    McpInvocationOutcome.BLOCKED_STALE,
                )
                return _mcp_server_stale_error(fn.__name__)

            def project_success(result):
                projected_result = _mcp_transport_projected_result(
                    capability,
                    result,
                    capability_surface_selection,
                )
                observe_invocation(
                    capability,
                    McpInvocationOutcome.SUCCEEDED,
                )
                return projected_result

            def project_failure(exception: Exception):
                observe_invocation(
                    capability,
                    McpInvocationOutcome.FAILED,
                )
                return _mcp_tool_error(fn.__name__, exception)

            if capability.progress_heartbeat_seconds is not None:
                from mcp.server.fastmcp import Context

                @wraps(fn)
                async def guarded_tool(mcp_context: Context, *args, **kwargs):
                    stale = stale_result()
                    if stale is not None:
                        return stale

                    async def invoke():
                        if iscoroutinefunction(fn):
                            return await fn(*args, **kwargs)
                        if capability.progress_worker_thread_safe:
                            return await asyncio.to_thread(fn, *args, **kwargs)
                        return await dispatcher.invoke(lambda: fn(*args, **kwargs))

                    try:
                        with _verbose_blocking_operation_diagnostics(capability):
                            result = await _await_with_declared_progress(
                                capability,
                                mcp_context,
                                invoke(),
                            )
                        return project_success(result)
                    except Exception as exc:
                        return project_failure(exc)

                guarded_annotations = {
                    "mcp_context": Context,
                    **fn.__annotations__,
                }
                guarded_signature = Signature(
                    parameters=(
                        Parameter(
                            "mcp_context",
                            Parameter.POSITIONAL_OR_KEYWORD,
                            annotation=Context,
                        ),
                        *inspect_signature(fn).parameters.values(),
                    ),
                    return_annotation=inspect_signature(fn).return_annotation,
                )
            elif iscoroutinefunction(fn):

                @wraps(fn)
                async def guarded_tool(*args, **kwargs):
                    stale = stale_result()
                    if stale is not None:
                        return stale
                    try:
                        result = await fn(*args, **kwargs)
                        return project_success(result)
                    except Exception as exc:
                        return project_failure(exc)

                guarded_annotations = dict(fn.__annotations__)
                guarded_signature = inspect_signature(fn)

            else:

                @wraps(fn)
                async def guarded_tool(*args, **kwargs):
                    stale = stale_result()
                    if stale is not None:
                        return stale
                    try:
                        result = await dispatcher.invoke(lambda: fn(*args, **kwargs))
                        return project_success(result)
                    except Exception as exc:
                        return project_failure(exc)

                guarded_annotations = dict(fn.__annotations__)
                guarded_signature = inspect_signature(fn)

            guarded_tool.__annotations__ = guarded_annotations
            result_contract = _mcp_tool_result_contract(capability)
            guarded_tool.__annotations__["return"] = result_contract
            guarded_tool.__signature__ = guarded_signature.replace(
                return_annotation=result_contract
            )
            server.tool(
                name=capability.name,
                title=capability.title,
                description=capability.description,
                annotations=_mcp_tool_annotations(capability),
                meta=_mcp_tool_meta(capability),
                structured_output=True,
            )(guarded_tool)
            # Keep the SDK's declaration-generated model as the argument owner.
            # Its default extra-ignore policy otherwise drops endpoint intent
            # before our request DTO can reject an undeclared parameter.
            registered_tool = server._tool_manager.get_tool(capability.name)
            argument_model = registered_tool.fn_metadata.arg_model
            argument_model.model_config["extra"] = "forbid"
            argument_model.model_rebuild(force=True)
            registered_tool.parameters = argument_model.model_json_schema(by_alias=True)
            return guarded_tool

        return decorator

    binder = McpCapabilityBinder(
        context=ctx,
        server=server,
        selection=capability_surface_selection,
        openhcs_tool=openhcs_tool,
        observe_invocation=observe_invocation,
    )
    for declaration in agent_capability_declarations():
        if capability_surface_selection.includes(declaration):
            declaration.invocation.bind_mcp(declaration, binder)

    return server


def _mcp_tool_result_contract(capability: type[AgentCapabilityDeclaration]):
    """Return the JSON-object wire contract for one nominal capability result."""
    require_agent_type_contract(capability.output_contract)
    return dict[str, Any]


def _mcp_tool_error(tool_name: str, exception: Exception) -> JsonValue:
    return to_jsonable(
        McpToolErrorResult(
            schema_version=SCHEMA_VERSION,
            ok=False,
            tool=tool_name,
            errors=(_mcp_tool_agent_error(exception),),
        )
    )


def _mcp_tool_agent_error(exception: Exception) -> AgentError:
    if isinstance(exception, AgentFacingErrorMixin):
        return exception.to_agent_error()
    return AgentError.from_exception(
        "mcp_tool_failed",
        exception,
        hint="The MCP server caught this exception at the tool boundary.",
    )


def _mcp_server_stale_error(tool_name: str) -> JsonValue:
    stale_source_paths = _mcp_server_stale_source_paths()
    recovery = _mcp_server_recovery_status(stale_source_paths)
    if stale_source_paths:
        stale_path = str(stale_source_paths[0])
    elif recovery.installation_pointer_path is not None:
        stale_path = recovery.installation_pointer_path
    else:
        stale_path = str(MCP_SERVER_SOURCE_PATH)
    return to_jsonable(
        McpServerStaleErrorResult(
            schema_version=SCHEMA_VERSION,
            ok=False,
            tool=tool_name,
            errors=(
                AgentError(
                    code="mcp_server_stale",
                    message=(
                        "The OpenHCS MCP process generation changed after this "
                        "process started. Reconnect before using agent tools."
                    ),
                    hint=recovery.hint,
                    path=stale_path,
                ),
            ),
            server_process_id=MCP_SERVER_PROCESS_ID,
            server_started_at_unix=MCP_SERVER_IMPORTED_AT_UNIX,
            stale_source_paths=tuple(
                str(source_path) for source_path in stale_source_paths
            ),
            recovery_reason=recovery.reason.value,
            installation_pointer_path=recovery.installation_pointer_path,
            installation_pointer_changed_since_import=(
                recovery.installation_pointer_changed_since_import
            ),
            installation_pointer_available=recovery.installation_pointer_available,
            restart_required=recovery.restart_required,
            restart_command=recovery.restart_command,
            restart_command_is_stable=recovery.restart_command_is_stable,
            reconnect_required=recovery.reconnect_required,
            reconnect_owner=(
                None
                if recovery.reconnect_owner is None
                else recovery.reconnect_owner.value
            ),
            retry_after_reconnect=recovery.retry_after_reconnect,
            automatic_recovery_on_reconnect=(recovery.automatic_recovery_on_reconnect),
            restart_hint=recovery.hint or "",
        )
    )


@dataclass(frozen=True, slots=True, kw_only=True)
class McpViewerConnectionToolFields:
    """Raw MCP viewer connection arguments before policy resolution."""

    port: int
    host: str = "localhost"
    transport_mode: TransportMode | None = None
    timeout_ms: int | None = None

    @classmethod
    def from_tool_arguments(
        cls,
        arguments: Mapping[str, JsonValue],
    ) -> Self:
        """Reconstruct this record from its own declared tool fields."""
        declared_names = tuple(
            declared_field.name
            for declared_field in dataclass_fields(cls)
            if declared_field.init
        )
        return dataclass_from_mapping(
            cls,
            {
                field_name: arguments[field_name]
                for field_name in declared_names
                if field_name in arguments
            },
        )

    @classmethod
    def signature_parameters(
        cls,
        timeout_policy: type[McpControlTimeoutPolicy],
    ) -> tuple[Parameter, ...]:
        """Project the public tool signature from the declared field types."""
        annotations = get_type_hints(cls)
        return tuple(
            parameter.replace(
                annotation=(
                    _timeout_parameter_annotation(timeout_policy)
                    if parameter.name == "timeout_ms"
                    else annotations[parameter.name]
                )
            )
            for parameter in inspect_signature(cls).parameters.values()
        )

    def to_control_args(
        self,
        timeout_policy: type[McpControlTimeoutPolicy] = McpViewerTimeoutPolicy,
    ) -> "McpViewerConnectionToolArgs":
        return McpViewerConnectionToolArgs.from_fields(
            port=self.port,
            host=self.host,
            transport_mode=self.transport_mode,
            timeout_ms=self.timeout_ms,
            timeout_policy=timeout_policy,
        )


@dataclass(frozen=True, slots=True)
class McpViewerConnectionToolArgs(ViewerWindowControlRequest):
    """MCP viewer connection fields projected into agent viewer request DTOs."""

    @classmethod
    def from_fields(
        cls,
        *,
        port: int,
        host: str,
        transport_mode: TransportMode | None,
        timeout_ms: int | None,
        timeout_policy: type[McpControlTimeoutPolicy] = McpViewerTimeoutPolicy,
    ) -> Self:
        return cls(
            connection=ExecutionConnectionSpec(
                host=host,
                port=port,
                transport_mode=transport_mode,
            ),
            timeout_ms=timeout_policy.resolve(timeout_ms),
        )


@dataclass(frozen=True, slots=True)
class McpUiBridgeConnectionRequest(UiBridgeConnectionRequest):
    """UI bridge request with the MCP timeout schema annotation."""

    timeout_ms: _McpUiBridgeTimeoutParameter = None


class UiBridgeConnectionToolArgs:
    """MCP tool argument adapter for a UI bridge connection request."""

    def __init__(self, request: UiBridgeConnectionRequest) -> None:
        self._request = request

    @classmethod
    def from_request(
        cls,
        value: McpUiBridgeConnectionRequest | UiBridgeConnectionRequest | None,
    ) -> Self:
        if isinstance(value, UiBridgeConnectionRequest):
            return cls(value)
        if value is None:
            return cls(UiBridgeConnectionRequest())
        raise TypeError(
            "UI bridge connection must use the declared MCP connection request."
        )

    def resolve(
        self,
        context: OpenHCSAgentContext,
        *,
        timeout_policy: type[McpControlTimeoutPolicy] = McpUiBridgeTimeoutPolicy,
    ) -> UiBridgeConnectionSpec:
        return context.ui_bridge_service.connection_from_fields(
            replace(
                self._request,
                timeout_ms=timeout_policy.resolve(self._request.timeout_ms),
            )
        )
