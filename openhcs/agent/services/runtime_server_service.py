"""Read-only runtime server discovery for OpenHCS agent integrations."""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import replace

from openhcs.agent.dto.common import AgentError, JsonObject, SCHEMA_VERSION
from openhcs.agent.dto.execution import (
    RuntimeDebugArtifactExportRequest,
    RuntimeDebugArtifactExportResult,
    RuntimeDebugCommandRequest,
    RuntimeDebugCommandResult,
    ExecutionConnectionSpec,
    RuntimeDebugInspectionRequest,
    RuntimeDebugInspectionResult,
    RuntimeServerExecutionStatusRequest,
    RuntimeServerInfoRequest,
    RuntimeExecutionStatus,
    RuntimeServerInfo,
    RuntimeServerScanRequest,
    RuntimeServerScanResult,
    RuntimeBootstrapStartRequest,
    RuntimeBootstrapHandle,
    RuntimeBootstrapObserveRequest,
    RuntimeBootstrapState,
    RuntimeBootstrapCloseRequest,
    RuntimeBootstrapCloseResult,
    runtime_execution_status_error,
    runtime_execution_status_from_response,
    unreachable_runtime_server_info,
)
from openhcs.core.debug_view_models import DebugViewModel
from openhcs.core.debug import DebugPausedWorkerStatus
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG, OpenHCSZMQConfig
from openhcs.runtime.zmq_execution_client import ZMQExecutionClient
from zmqruntime.config import TransportMode
from zmqruntime.messages import PongResponse, ServerRole
from zmqruntime.startup import (
    EndpointStartupPhase,
    EndpointStartupStatus,
    EndpointStartupStatusReader,
)
from zmqruntime.timeouts import OperationDeadline
from zmqruntime.client import EndpointStartupUncertainError

RUNTIME_SERVER_KIND_HINT = (
    "Use openhcs_scan_runtime_servers to discover endpoints. Viewer ports should "
    "be queried with viewer tools, and UI bridge ports should be queried with UI "
    "bridge tools."
)


class RuntimeServerWrongKindError(ValueError):
    """Raised when a pong endpoint is not an execution runtime server."""

    def __init__(
        self,
        *,
        server_name: str | None,
        server_type: str | None,
        port: int | None,
    ) -> None:
        self.server_name = server_name
        self.server_type = server_type
        self.port = port
        super().__init__(
            f"Port {port} responded as {server_name or 'unknown server'} "
            f"with server_type={server_type or 'unknown'}, not a ZMQ execution "
            "runtime server."
        )


class RuntimeServerGatewayABC(ABC):
    """Transport boundary for querying OpenHCS runtime servers."""

    @abstractmethod
    def server_info(
        self,
        connection: ExecutionConnectionSpec,
        *,
        timeout_ms: int,
    ) -> PongResponse:
        raise NotImplementedError

    @abstractmethod
    def execution_status(
        self,
        connection: ExecutionConnectionSpec,
        execution_id: str | None = None,
        *,
        timeout_ms: int,
    ) -> JsonObject:
        raise NotImplementedError

    def runtime_debug_inspection(
        self,
        connection: ExecutionConnectionSpec,
        debug_session_id: str,
        *,
        timeout_ms: int,
    ) -> DebugViewModel:
        """Return the exact paused-worker runtime view when supported."""
        raise NotImplementedError

    @abstractmethod
    def send_debug_command(
        self,
        connection: ExecutionConnectionSpec,
        debug_session_id: str,
        command_type: str,
        *,
        timeout_ms: int,
    ) -> "DebugPausedWorkerStatus":
        """Send one debug-worker command and return the resulting status."""
        raise NotImplementedError

    @abstractmethod
    def export_debug_artifact(
        self,
        connection: ExecutionConnectionSpec,
        debug_session_id: str,
        artifact_ref: str,
        export_root: str,
        snapshot_store_ref: str | None,
        snapshot_store_backend: str | None,
        *,
        timeout_ms: int,
    ) -> str:
        """Export one paused debug worker's artifact and return its ref."""
        raise NotImplementedError

    @abstractmethod
    def scan(
        self,
        *,
        host: str,
        ports: tuple[int, ...],
        transport_mode: TransportMode | None,
        timeout_ms: int,
    ) -> tuple[PongResponse, ...]:
        raise NotImplementedError


class ZMQRuntimeServerGateway(RuntimeServerGatewayABC):
    """Runtime server gateway backed by the existing ZMQ execution client."""

    def __init__(
        self,
        config: OpenHCSZMQConfig = OPENHCS_ZMQ_CONFIG,
    ) -> None:
        self._config = config

    def server_info(
        self,
        connection: ExecutionConnectionSpec,
        *,
        timeout_ms: int,
    ) -> PongResponse:
        port = connection.require_port("Runtime server info")
        responses = self.scan(
            host=connection.host,
            ports=(port,),
            transport_mode=connection.transport_mode,
            timeout_ms=timeout_ms,
        )
        if not responses:
            raise TimeoutError(
                f"No OpenHCS ZMQ endpoint responded on port {port} within {timeout_ms}ms."
            )
        return responses[0]

    def execution_status(
        self,
        connection: ExecutionConnectionSpec,
        execution_id: str | None = None,
        *,
        timeout_ms: int,
    ) -> JsonObject:
        return dict(
            self._client(connection).get_status(
                execution_id,
                timeout_ms=timeout_ms,
            )
        )

    def runtime_debug_inspection(
        self,
        connection: ExecutionConnectionSpec,
        debug_session_id: str,
        *,
        timeout_ms: int,
    ) -> DebugViewModel:
        return self._client(
            connection,
            timeout_ms=timeout_ms,
        ).get_debug_runtime_inspection(debug_session_id=debug_session_id)

    def send_debug_command(
        self,
        connection: ExecutionConnectionSpec,
        debug_session_id: str,
        command_type: str,
        *,
        timeout_ms: int,
    ) -> "DebugPausedWorkerStatus":
        return (
            self._client(
                connection,
                timeout_ms=timeout_ms,
            )
            .send_debug_worker_command(
                debug_session_id=debug_session_id,
                command_type=command_type,
            )
            .status
        )

    def export_debug_artifact(
        self,
        connection: ExecutionConnectionSpec,
        debug_session_id: str,
        artifact_ref: str,
        export_root: str,
        snapshot_store_ref: str | None,
        snapshot_store_backend: str | None,
        *,
        timeout_ms: int,
    ) -> str:
        return (
            self._client(
                connection,
                timeout_ms=timeout_ms,
            )
            .export_debug_artifact(
                debug_session_id=debug_session_id,
                artifact_ref=artifact_ref,
                export_root=export_root,
                snapshot_store_ref=snapshot_store_ref,
                snapshot_store_backend=snapshot_store_backend,
            )
            .exported_ref
        )

    def scan(
        self,
        *,
        host: str,
        ports: tuple[int, ...],
        transport_mode: TransportMode | None,
        timeout_ms: int,
    ) -> tuple[PongResponse, ...]:
        return tuple(
            ZMQExecutionClient.scan_servers(
                ports,
                host=host,
                timeout_ms=timeout_ms,
                transport_mode=transport_mode,
                config=self._config,
            )
        )

    def _client(
        self,
        connection: ExecutionConnectionSpec,
        *,
        timeout_ms: int | None = None,
    ) -> ZMQExecutionClient:
        config = (
            self._config
            if timeout_ms is None
            else replace(self._config, control_timeout_ms=timeout_ms)
        )
        return connection.execution_client(config)


class RuntimeServerService:
    """Own explicit bootstrap admission and read-only runtime observation."""

    def __init__(
        self,
        gateway: RuntimeServerGatewayABC | None = None,
        config: OpenHCSZMQConfig = OPENHCS_ZMQ_CONFIG,
        path_policy: AgentPathPolicy | None = None,
    ) -> None:
        self._config = config
        self._gateway = gateway or ZMQRuntimeServerGateway(config)
        self._path_policy = path_policy or AgentPathPolicy.from_environment()

    def start_from_request(
        self, request: RuntimeBootstrapStartRequest
    ) -> RuntimeBootstrapState:
        connection = request.connection.resolved(self._config)
        config = replace(self._config, server_host=connection.host)
        client = connection.execution_client(config)
        endpoint = client.endpoint
        if not endpoint.transport_mode.declaration.endpoint_is_local(
            endpoint.host, endpoint.port
        ):
            raise ValueError("Runtime bootstrap requires an explicit local connection")
        plan = client.runtime_launch_plan()
        for path in plan.writable_paths():
            self._path_policy.assert_writable(path)
        deadline = OperationDeadline.after_milliseconds(
            request.timeout_ms,
            operation="explicit runtime bootstrap",
        )
        errors = ()
        try:
            process = client.start_owned_process(operation_deadline=deadline)
        except EndpointStartupUncertainError as error:
            process = error.process
            errors = (AgentError.from_exception("runtime_bootstrap_uncertain", error),)
        handle = RuntimeBootstrapHandle(connection, process.identity, plan)
        # No waiting for endpoint readiness or catalogue preparation here.
        return RuntimeBootstrapState(
            schema_version=SCHEMA_VERSION,
            handle=handle,
            progress=EndpointStartupStatus(
                EndpointStartupPhase.STARTING_PROCESS,
                "Native child spawned; retain this exact handle",
            ),
            ready=False,
            process_alive=process.is_alive(),
            errors=errors,
        )

    def observe_bootstrap(
        self, request: RuntimeBootstrapObserveRequest
    ) -> RuntimeBootstrapState:
        handle = request.handle
        for path in handle.launch_plan.writable_paths():
            self._path_policy.assert_writable(path)
        self._path_policy.assert_readable_location(
            handle.launch_plan.startup_status_file
        )
        alive = handle.process_identity.is_alive()
        statuses = (
            EndpointStartupStatusReader(handle.launch_plan.startup_status_file)
            .read()
            .statuses
        )
        endpoint = handle.connection.transport_endpoint(self._config)
        pong = (
            endpoint.ping(self._config, timeout_ms=self._config.server_info_timeout_ms)
            if alive
            else None
        )
        return RuntimeBootstrapState.from_observation(
            handle,
            process_alive=alive,
            statuses=statuses,
            pong=pong,
        )

    def close_bootstrap(
        self, request: RuntimeBootstrapCloseRequest
    ) -> RuntimeBootstrapCloseResult:
        """Admit native lifecycle writes, then close one proven owned incarnation."""
        handle = request.handle
        config = replace(self._config, server_host=handle.connection.host)
        client = handle.connection.execution_client(config)
        # Resolve actual transport writes in THIS launch environment, not only
        # the caller's serialized plan. Never let a forged path admit a lock.
        for path in client.runtime_launch_plan().transport_write_paths:
            self._path_policy.assert_writable(path)
        for path in handle.launch_plan.writable_paths():
            self._path_policy.assert_writable(path)
        outcome = client.close_owned_process(
            handle.process_identity,
            mode=request.mode,
            operation_deadline=OperationDeadline.after_milliseconds(
                request.timeout_ms, operation="owned runtime close"
            ),
        )
        return RuntimeBootstrapCloseResult(
            schema_version=SCHEMA_VERSION,
            handle=handle,
            outcome=outcome,
            errors=()
            if outcome.succeeded
            else (
                AgentError(
                    code="runtime_close_unresolved",
                    message="Exact owner close is unresolved; retain this handle and observe without replay.",
                ),
            ),
        )

    def server_info(
        self,
        *,
        host: str = "localhost",
        port: int | None = None,
        transport_mode: TransportMode | None = None,
        persistent: bool = True,
        timeout_ms: int | None = None,
    ) -> RuntimeServerInfo:
        timeout_ms = (
            self._config.server_info_timeout_ms if timeout_ms is None else timeout_ms
        )
        connection = ExecutionConnectionSpec(host, port, transport_mode, persistent)
        try:
            pong = self._gateway.server_info(
                connection,
                timeout_ms=timeout_ms,
            )
            if pong.server_role is not ServerRole.EXECUTION:
                raise RuntimeServerWrongKindError(
                    server_name=pong.server,
                    server_type=pong.server_type,
                    port=pong.port,
                )
        except RuntimeServerWrongKindError as exc:
            return unreachable_runtime_server_info(
                connection=connection,
                error=AgentError.from_exception(
                    "runtime_server_wrong_type",
                    exc,
                    hint=RUNTIME_SERVER_KIND_HINT,
                ),
            )
        except Exception as exc:
            return unreachable_runtime_server_info(
                connection=connection,
                error=AgentError.from_exception(
                    "runtime_server_unreachable",
                    exc,
                    hint=RUNTIME_SERVER_KIND_HINT,
                ),
            )
        return RuntimeServerInfo.from_pong(
            connection=connection,
            pong=pong,
        )

    def server_info_from_request(
        self,
        request: RuntimeServerInfoRequest,
    ) -> RuntimeServerInfo:
        return self.server_info(
            host=request.connection.host,
            port=request.connection.port,
            transport_mode=request.connection.transport_mode,
            persistent=request.connection.persistent,
            timeout_ms=request.timeout_ms,
        )

    def scan(
        self,
        *,
        ports: tuple[int, ...] | None = None,
        host: str = "localhost",
        transport_mode: TransportMode | None = None,
        timeout_ms: int | None = None,
    ) -> RuntimeServerScanResult:
        timeout_ms = (
            self._config.server_scan_timeout_ms if timeout_ms is None else timeout_ms
        )
        scanned_ports = self._scan_ports(ports)
        responses = self._gateway.scan(
            host=host,
            ports=scanned_ports,
            transport_mode=transport_mode,
            timeout_ms=timeout_ms,
        )
        servers = tuple(
            RuntimeServerInfo.from_pong(
                connection=ExecutionConnectionSpec(
                    host=host,
                    transport_mode=transport_mode,
                ),
                pong=pong,
            )
            for pong in responses
            if pong.server_role is ServerRole.EXECUTION
        )
        return RuntimeServerScanResult(
            schema_version=SCHEMA_VERSION,
            connection=ExecutionConnectionSpec(
                host=host,
                transport_mode=transport_mode,
            ),
            ports=scanned_ports,
            timeout_ms=timeout_ms,
            servers=servers,
        )

    def scan_from_request(
        self,
        request: RuntimeServerScanRequest,
    ) -> RuntimeServerScanResult:
        return self.scan(
            ports=request.ports,
            host=request.host,
            transport_mode=request.transport_mode,
            timeout_ms=request.timeout_ms,
        )

    def execution_status(
        self,
        *,
        execution_id: str | None = None,
        host: str = "localhost",
        port: int | None = None,
        transport_mode: TransportMode | None = None,
        persistent: bool = True,
        timeout_ms: int | None = None,
    ) -> RuntimeExecutionStatus:
        timeout_ms = (
            self._config.control_timeout_ms if timeout_ms is None else timeout_ms
        )
        connection = ExecutionConnectionSpec(host, port, transport_mode, persistent)
        try:
            response = self._gateway.execution_status(
                connection,
                execution_id,
                timeout_ms=timeout_ms,
            )
        except Exception as exc:
            return runtime_execution_status_error(
                connection=connection,
                execution_id=execution_id,
                error=AgentError.from_exception(
                    "runtime_execution_status_error",
                    exc,
                    hint=(
                        "Check that the port is an OpenHCS execution server and "
                        "increase timeout_ms only if the server is known to be busy."
                    ),
                ),
            )
        return runtime_execution_status_from_response(
            connection=connection,
            execution_id=execution_id,
            response=response,
        )

    def execution_status_from_request(
        self,
        request: RuntimeServerExecutionStatusRequest,
    ) -> RuntimeExecutionStatus:
        return self.execution_status(
            execution_id=request.execution_id,
            host=request.connection.host,
            port=request.connection.port,
            transport_mode=request.connection.transport_mode,
            persistent=request.connection.persistent,
            timeout_ms=request.timeout_ms,
        )

    def runtime_debug_inspection(
        self,
        *,
        debug_session_id: str,
        host: str = "localhost",
        port: int | None = None,
        transport_mode: TransportMode | None = None,
        persistent: bool = True,
        timeout_ms: int | None = None,
    ) -> RuntimeDebugInspectionResult:
        timeout_ms = (
            self._config.control_timeout_ms if timeout_ms is None else timeout_ms
        )
        connection = ExecutionConnectionSpec(host, port, transport_mode, persistent)
        try:
            view_model = self._gateway.runtime_debug_inspection(
                connection,
                debug_session_id,
                timeout_ms=timeout_ms,
            )
        except Exception as exc:
            return RuntimeDebugInspectionResult(
                schema_version=SCHEMA_VERSION,
                connection=connection,
                debug_session_id=debug_session_id,
                errors=(
                    AgentError.from_exception(
                        "runtime_debug_inspection_error",
                        exc,
                        hint=(
                            "Inspect execution status for the exact paused "
                            "debug_session_id, and confirm the port is the "
                            "OpenHCS execution server that owns that session."
                        ),
                    ),
                ),
            )
        return RuntimeDebugInspectionResult(
            schema_version=SCHEMA_VERSION,
            connection=connection,
            debug_session_id=debug_session_id,
            view_model=view_model,
        )

    def runtime_debug_inspection_from_request(
        self,
        request: RuntimeDebugInspectionRequest,
    ) -> RuntimeDebugInspectionResult:
        return self.runtime_debug_inspection(
            debug_session_id=request.debug_session_id,
            host=request.connection.host,
            port=request.connection.port,
            transport_mode=request.connection.transport_mode,
            persistent=request.connection.persistent,
            timeout_ms=request.timeout_ms,
        )

    def debug_command(
        self,
        *,
        debug_session_id: str,
        command_type: str,
        host: str = "localhost",
        port: int | None = None,
        transport_mode: TransportMode | None = None,
        persistent: bool = True,
        timeout_ms: int | None = None,
    ) -> RuntimeDebugCommandResult:
        timeout_ms = (
            self._config.control_timeout_ms if timeout_ms is None else timeout_ms
        )
        connection = ExecutionConnectionSpec(host, port, transport_mode, persistent)
        try:
            status = self._gateway.send_debug_command(
                connection,
                debug_session_id,
                command_type,
                timeout_ms=timeout_ms,
            )
        except Exception as exc:
            return RuntimeDebugCommandResult(
                schema_version=SCHEMA_VERSION,
                connection=connection,
                debug_session_id=debug_session_id,
                command_type=command_type,
                errors=(
                    AgentError.from_exception(
                        "runtime_debug_command_error",
                        exc,
                        hint=(
                            "Confirm the command type against the "
                            "DebugCommandType authority and that the session "
                            "is a paused OpenHCS debug worker owned by this "
                            "execution server."
                        ),
                    ),
                ),
            )
        status_record = status.to_dict() if hasattr(status, "to_dict") else {}
        return RuntimeDebugCommandResult(
            schema_version=SCHEMA_VERSION,
            connection=connection,
            debug_session_id=debug_session_id,
            command_type=command_type,
            worker_state=(
                str(status_record.get("state"))
                if status_record.get("state") is not None
                else None
            ),
            cursor=status_record.get("cursor"),
        )

    def debug_command_from_request(
        self,
        request: RuntimeDebugCommandRequest,
    ) -> RuntimeDebugCommandResult:
        return self.debug_command(
            debug_session_id=request.debug_session_id,
            command_type=request.command_type,
            host=request.connection.host,
            port=request.connection.port,
            transport_mode=request.connection.transport_mode,
            persistent=request.connection.persistent,
            timeout_ms=request.timeout_ms,
        )

    def debug_artifact_export(
        self,
        *,
        debug_session_id: str,
        artifact_ref: str,
        export_root: str,
        snapshot_store_ref: str | None = None,
        snapshot_store_backend: str | None = None,
        host: str = "localhost",
        port: int | None = None,
        transport_mode: TransportMode | None = None,
        persistent: bool = True,
        timeout_ms: int | None = None,
    ) -> RuntimeDebugArtifactExportResult:
        connection = ExecutionConnectionSpec(host, port, transport_mode, persistent)

        def failure(exc: Exception) -> RuntimeDebugArtifactExportResult:
            return RuntimeDebugArtifactExportResult(
                schema_version=SCHEMA_VERSION,
                connection=connection,
                debug_session_id=debug_session_id,
                artifact_ref=artifact_ref,
                export_root=export_root,
                errors=(
                    AgentError.from_exception(
                        "runtime_debug_export_error",
                        exc,
                        hint=(
                            "Confirm the artifact ref against "
                            "runtime-debug-values and that export_root is "
                            "inside the agent writable roots."
                        ),
                    ),
                ),
            )

        try:
            AgentPathPolicy.from_environment().assert_writable(export_root)
        except Exception as exc:
            return failure(exc)
        timeout_ms = (
            self._config.control_timeout_ms if timeout_ms is None else timeout_ms
        )
        try:
            exported_ref = self._gateway.export_debug_artifact(
                connection,
                debug_session_id,
                artifact_ref,
                export_root,
                snapshot_store_ref,
                snapshot_store_backend,
                timeout_ms=timeout_ms,
            )
        except Exception as exc:
            return failure(exc)
        return RuntimeDebugArtifactExportResult(
            schema_version=SCHEMA_VERSION,
            connection=connection,
            debug_session_id=debug_session_id,
            artifact_ref=artifact_ref,
            export_root=export_root,
            exported_ref=exported_ref,
        )

    def debug_artifact_export_from_request(
        self,
        request: RuntimeDebugArtifactExportRequest,
    ) -> RuntimeDebugArtifactExportResult:
        return self.debug_artifact_export(
            debug_session_id=request.debug_session_id,
            artifact_ref=request.artifact_ref,
            export_root=request.export_root,
            snapshot_store_ref=request.snapshot_store_ref,
            snapshot_store_backend=request.snapshot_store_backend,
            host=request.connection.host,
            port=request.connection.port,
            transport_mode=request.connection.transport_mode,
            persistent=request.connection.persistent,
            timeout_ms=request.timeout_ms,
        )

    def _scan_ports(self, ports: tuple[int, ...] | None) -> tuple[int, ...]:
        if ports is None:
            return (self._config.default_port,)
        return tuple(dict.fromkeys(int(port) for port in ports))
