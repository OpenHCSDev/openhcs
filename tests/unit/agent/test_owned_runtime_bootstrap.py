from dataclasses import replace
from unittest.mock import Mock

import pytest
from python_introspect import dataclass_from_mapping
from openhcs.serialization.json import to_jsonable
from zmqruntime.config import TransportMode
from zmqruntime.messages import ProcessIdentity, PongResponse, ServerRole
from zmqruntime.startup import EndpointStartupPhase, EndpointStartupStatus
from zmqruntime.transport import TransportEndpoint

from openhcs.agent.capabilities import agent_capabilities
from openhcs.agent.dto.execution_connection import ExecutionConnectionSpec
from openhcs.agent.dto.execution import (
    RuntimeBootstrapStartRequest,
    RuntimeBootstrapObserveRequest,
    RuntimeBootstrapHandle,
    RuntimeBootstrapCloseRequest,
    RuntimeBootstrapCloseResult,
    RuntimeBootstrapState,
)
from openhcs.agent.path_policy import AgentPathPolicy, AgentPathPolicyError
from openhcs.agent.services.runtime_server_service import RuntimeServerService
from openhcs.mcp.context import OpenHCSAgentContext
from openhcs.runtime.zmq_config import OpenHCSZMQConfig
from openhcs.runtime.zmq_execution_client import (
    ExecutionRuntimeLaunchPlan,
    ZMQExecutionClient,
)
from zmqruntime.client import (
    EndpointProcess,
    EndpointShutdownMode,
    EndpointShutdownResult,
)

_PRODUCTION_SPAWN = ZMQExecutionClient._spawn_server_process


class Child(EndpointProcess):
    identity = ProcessIdentity.current()

    def is_alive(self):
        return True

    def exit(self):
        return None

    def wait_for_exit(self, timeout):
        return None

    def stop(self, timeout=5, kill_timeout=2):
        raise AssertionError("No process shutdown in source tests")


@pytest.fixture
def setup(tmp_path, monkeypatch):
    monkeypatch.setenv("HOME", str(tmp_path))
    monkeypatch.setenv("XDG_DATA_HOME", str(tmp_path / "data"))
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path / "cache"))
    policy = AgentPathPolicy.with_roots(
        readable_roots=(tmp_path,), writable_roots=(tmp_path,)
    )
    request = RuntimeBootstrapStartRequest.from_fields(
        host="127.0.0.1", port=5913, transport_mode=TransportMode.TCP
    )
    spawn = Mock(return_value=Child())
    monkeypatch.setattr(ZMQExecutionClient, "_spawn_server_process", spawn)
    monkeypatch.setattr(TransportEndpoint, "occupied_ports", lambda *_: frozenset())
    monkeypatch.setattr(
        TransportMode.TCP.declaration, "data_control_pair_is_available", lambda *_: True
    )
    return RuntimeServerService(path_policy=policy), request, spawn


@pytest.mark.parametrize("mode", [TransportMode.TCP, TransportMode.IPC])
def test_launch_plan_projects_native_owners_without_materialization(
    setup, tmp_path, mode
):
    from metaclass_registry.cache import get_cache_file_path
    from openhcs.core.xdg_paths import get_openhcs_data_dir, get_openhcs_log_dir
    from openhcs.processing.custom_functions.manager import CustomFunctionManager

    _, _, spawn = setup
    config = OpenHCSZMQConfig(
        app_name="bootstrap-projection-test",
        control_port_offset=1700,
        ipc_socket_dir="selected-ipc",
        ipc_socket_prefix="selected-prefix",
        transport_mode=mode,
    )
    endpoint = config.client_endpoint(5914)
    plan = ExecutionRuntimeLaunchPlan.resolve(endpoint, config)
    declaration = mode.declaration
    ports = endpoint.port_pair(config).ports
    assert plan.transport_write_paths == (
        *(declaration.startup_lock_path(port, config) for port in ports),
        *(
            path
            for port in ports
            if (path := declaration.socket_path(port, config)) is not None
        ),
    )
    assert plan.runtime_dir == get_openhcs_data_dir(create=False)
    assert plan.log_file.parent == get_openhcs_log_dir(create=False)
    assert plan.startup_status_file == plan.log_file.with_suffix(".startup.jsonl")
    assert plan.storage_dir == CustomFunctionManager.default_storage_directory()
    assert plan.registry_cache_dir == get_cache_file_path("", create=False)
    assert not tuple(tmp_path.iterdir())
    spawn.assert_not_called()


def test_client_retains_same_admitted_launch_plan(setup, monkeypatch):
    _, request, spawn = setup
    client = request.connection.execution_client(OpenHCSZMQConfig())
    resolve = Mock(wraps=ExecutionRuntimeLaunchPlan.resolve)
    monkeypatch.setattr(ExecutionRuntimeLaunchPlan, "resolve", resolve)
    plan = client.runtime_launch_plan()
    assert client.runtime_launch_plan() is plan
    resolve.assert_called_once_with(client.endpoint, client.config)
    spawn.assert_not_called()


@pytest.mark.parametrize("mode", tuple(TransportMode))
@pytest.mark.parametrize("persistent", [False, True])
def test_admitted_plan_owns_materialization_and_child_configuration(
    setup, tmp_path, monkeypatch, mode, persistent
):
    import subprocess
    import sys
    from openhcs.core.config_document import ConfigDocumentAuthority
    from openhcs.runtime import zmq_execution_client as module
    from openhcs.runtime.import_authority import OpenHCSRuntimeImportAuthority

    _, _, intercepted_spawn = setup
    config = OpenHCSZMQConfig(
        transport_mode=mode,
        default_port=5997,
        persistent=not persistent,
        control_port_offset=1700,
        app_name="plan-materialization-test",
        ipc_socket_prefix="selected-materialization",
        server_host="127.0.0.1",
    )
    endpoint = config.client_endpoint(5914)
    plan = ExecutionRuntimeLaunchPlan.resolve(endpoint, config)
    assert not tuple(tmp_path.iterdir())
    plan.startup_status_file.parent.mkdir(parents=True)
    plan.startup_status_file.write_text("old journal", encoding="utf-8")
    native_process = Mock(spec=subprocess.Popen)
    launch = Mock(return_value=native_process)
    policy = Mock()
    policy.popen_arguments.return_value = {"start_new_session": persistent}
    policy_selection = Mock(return_value=policy)
    monkeypatch.setattr(
        module.BackgroundProcessLaunchPolicy, "current", policy_selection
    )
    monkeypatch.setattr(module.subprocess, "Popen", launch)
    environment = {"PLAN_TEST": "owned"}
    monkeypatch.setattr(
        module.MemoryType, "subprocess_environment", lambda: environment
    )

    assert plan.spawn(endpoint, config, persistent=persistent) is native_process
    intercepted_spawn.assert_not_called()
    launch.assert_called_once()
    policy_selection.assert_called_once_with(detached=persistent)
    args, kwargs = launch.call_args
    command = args[0]
    assert command[:4] == [sys.executable, "-B", "-X", "faulthandler"]
    assert command[4:6] == list(
        OpenHCSRuntimeImportAuthority.current().module_process_arguments(
            "openhcs.runtime.zmq_execution_server_launcher"
        )
    )
    child_config = ConfigDocumentAuthority.from_source(
        command[command.index("--config-source") + 1],
        expected_config_type=OpenHCSZMQConfig,
    )
    assert child_config == replace(
        config, default_port=endpoint.port, transport_mode=mode, persistent=persistent
    )
    assert command[command.index("--log-file-path") + 1] == str(plan.log_file)
    assert command[command.index("--startup-status-path") + 1] == str(
        plan.startup_status_file
    )
    assert kwargs["cwd"] == plan.runtime_dir
    assert kwargs["env"] is environment
    assert kwargs["stderr"] is subprocess.STDOUT
    assert kwargs["stdout"].name == str(plan.log_file)
    assert kwargs["stdout"].closed  # Including after Popen returns.
    assert kwargs["start_new_session"] is persistent
    assert plan.log_file.is_file()
    assert not plan.startup_status_file.exists()
    assert not plan.storage_dir.exists()  # Storage/cache stay native-owned.
    assert not plan.registry_cache_dir.exists()
    assert all(not path.exists() for path in plan.transport_write_paths)


def test_client_consumes_exact_admitted_plan_on_spawn_failure(setup, monkeypatch):
    _, request, intercepted_spawn = setup
    client = request.connection.execution_client(OpenHCSZMQConfig())
    plan = client.runtime_launch_plan()

    calls = []

    def consume(selected_plan, endpoint, config, *, persistent):
        calls.append((selected_plan, endpoint, config, persistent))
        raise OSError("controlled no-child spawn failure")

    monkeypatch.setattr(ExecutionRuntimeLaunchPlan, "spawn", consume)
    # Exercise the original production hook rather than setup's interception.
    with pytest.raises(OSError, match="no-child spawn failure"):
        _PRODUCTION_SPAWN(client)
    assert calls == [(plan, client.endpoint, client.config, client.persistent)]
    assert calls[0][0] is plan
    assert client._runtime_launch_plan is None
    assert client._startup_status_path == plan.startup_status_file
    intercepted_spawn.assert_not_called()


def test_plan_closes_materialized_log_when_child_creation_fails(setup, monkeypatch):
    from openhcs.runtime import zmq_execution_client as module

    _, request, intercepted_spawn = setup
    client = request.connection.execution_client(OpenHCSZMQConfig())
    plan = client.runtime_launch_plan()
    launch = Mock(side_effect=OSError("controlled child creation failure"))
    monkeypatch.setattr(module.subprocess, "Popen", launch)
    with pytest.raises(OSError, match="child creation failure"):
        _PRODUCTION_SPAWN(client)
    launch.assert_called_once()
    assert launch.call_args.kwargs["stdout"].closed
    assert plan.log_file.exists()
    assert client._runtime_launch_plan is None
    assert client._startup_status_path == plan.startup_status_file
    intercepted_spawn.assert_not_called()


def test_connection_urls_share_effective_endpoint_owner(setup, tmp_path, monkeypatch):
    _, _, spawn = setup
    config = OpenHCSZMQConfig(
        transport_mode=TransportMode.TCP, control_port_offset=1700
    )
    connection = ExecutionConnectionSpec(host="127.0.0.1", port=5968)
    monkeypatch.setattr(
        TransportMode,
        "default",
        Mock(side_effect=AssertionError("No platform fallback for URL projection")),
    )
    endpoint = connection.execution_client(config).endpoint
    assert connection.zmq_data_url(config) == endpoint.data_url(config)
    assert connection.zmq_control_url(config) == endpoint.control_url(config)
    assert connection.zmq_control_port(config) == endpoint.control_port(config)
    assert not tuple(tmp_path.iterdir())
    spawn.assert_not_called()


@pytest.mark.parametrize("configured_mode", tuple(TransportMode))
@pytest.mark.parametrize("requested_mode", (None, *TransportMode))
def test_effective_connection_matches_configured_native_endpoint(
    monkeypatch, configured_mode, requested_mode
):
    config = OpenHCSZMQConfig(
        client_host="unselected-config-host",
        default_port=5997,
        transport_mode=configured_mode,
    )
    connection = ExecutionConnectionSpec(
        host="127.0.0.1", port=5968, transport_mode=requested_mode
    )
    monkeypatch.setattr(
        TransportMode,
        "default",
        Mock(side_effect=AssertionError("Do not recover a platform default")),
    )
    endpoint = connection.transport_endpoint(config)
    assert endpoint == connection.execution_client(config).endpoint
    assert endpoint.host == connection.host and endpoint.port == connection.port
    assert endpoint.transport_mode is (
        configured_mode if requested_mode is None else requested_mode
    )
    resolved = connection.resolved(config)
    assert resolved.transport_endpoint() == endpoint
    assert resolved.execution_client(config).endpoint == endpoint
    assert connection.transport_mode is requested_mode  # Input stays immutable.
    assert ZMQExecutionClient(config=config).endpoint == config.client_endpoint()


@pytest.mark.parametrize("configured_mode", tuple(TransportMode))
@pytest.mark.parametrize("requested_mode", (None, *TransportMode))
def test_start_observe_close_retain_one_effective_route(
    setup, tmp_path, monkeypatch, configured_mode, requested_mode
):
    _, request, spawn = setup
    request = replace(
        request,
        connection=replace(
            request.connection, host="127.0.0.1", transport_mode=requested_mode
        ),
    )
    config = OpenHCSZMQConfig(
        transport_mode=configured_mode,
        control_port_offset=1700,
        app_name="owned-route-test",
        ipc_socket_prefix="selected-route",
    )
    expected = request.connection.transport_endpoint(config)
    monkeypatch.setattr(
        expected.transport_mode.declaration,
        "data_control_pair_is_available",
        Mock(return_value=True),
    )
    monkeypatch.setattr(
        TransportMode,
        "default",
        Mock(side_effect=AssertionError("No omitted-mode re-resolution")),
    )
    routes = []
    original_start = ZMQExecutionClient.start_owned_process

    def start(client, *, operation_deadline):
        routes.append(client.endpoint)
        return original_start(client, operation_deadline=operation_deadline)

    def ping(endpoint, actual_config, *, timeout_ms):
        routes.append(endpoint)
        return PongResponse(
            port=endpoint.port,
            control_port=endpoint.control_port(actual_config),
            ready=True,
            server="fixture",
            server_role=ServerRole.EXECUTION,
            process_identity=Child.identity,
        )

    def close(client, identity, *, mode, operation_deadline):
        routes.append(client.endpoint)
        assert identity == Child.identity
        return EndpointShutdownResult(True, True, identity, True)

    monkeypatch.setattr(ZMQExecutionClient, "start_owned_process", start)
    monkeypatch.setattr(TransportEndpoint, "ping", ping)
    monkeypatch.setattr(ZMQExecutionClient, "close_owned_process", close)
    policy = AgentPathPolicy.with_roots(
        readable_roots=(tmp_path,), writable_roots=(tmp_path,)
    )
    service = RuntimeServerService(config=config, path_policy=policy)
    started = service.start_from_request(request)
    handle = dataclass_from_mapping(RuntimeBootstrapHandle, to_jsonable(started.handle))
    assert handle.connection.transport_mode is expected.transport_mode
    assert handle.connection.transport_endpoint() == expected
    assert not handle.launch_plan.startup_status_file.exists()
    # Retained explicit routing wins even if another observer has a different
    # configured default. No second transport record or mutable mode cache.
    observer_config = replace(
        config,
        transport_mode=next(
            mode for mode in TransportMode if mode is not configured_mode
        ),
    )
    observer = RuntimeServerService(config=observer_config, path_policy=policy)
    observed = observer.observe_bootstrap(RuntimeBootstrapObserveRequest(handle))
    closed = observer.close_bootstrap(RuntimeBootstrapCloseRequest(handle))
    assert observed.ready and observed.handle == handle
    assert closed.outcome.succeeded and closed.handle == handle
    assert routes == [expected, expected, expected]
    assert not handle.launch_plan.startup_status_file.exists()
    spawn.assert_called_once()


@pytest.mark.parametrize("configured_mode", tuple(TransportMode))
def test_locality_uses_effective_endpoint_before_plan_or_write(
    setup, tmp_path, monkeypatch, configured_mode
):
    _, request, spawn = setup
    request = replace(
        request, connection=replace(request.connection, transport_mode=None)
    )
    config = OpenHCSZMQConfig(transport_mode=configured_mode)
    admission = Mock(return_value=False)
    monkeypatch.setattr(configured_mode.declaration, "endpoint_is_local", admission)
    plan = Mock(side_effect=AssertionError("No plan before locality admission"))
    monkeypatch.setattr(ZMQExecutionClient, "runtime_launch_plan", plan)
    service = RuntimeServerService(config=config)
    with pytest.raises(ValueError, match="local connection"):
        service.start_from_request(request)
    admission.assert_called_once_with(request.connection.host, request.connection.port)
    plan.assert_not_called()
    spawn.assert_not_called()
    assert not tuple(tmp_path.iterdir())


def test_omitted_tcp_mode_cannot_borrow_ipc_locality(setup, tmp_path):
    _, request, spawn = setup
    request = replace(
        request,
        connection=replace(request.connection, host="203.0.113.7", transport_mode=None),
    )
    service = RuntimeServerService(
        config=OpenHCSZMQConfig(transport_mode=TransportMode.TCP)
    )
    with pytest.raises(ValueError, match="local connection"):
        service.start_from_request(request)
    assert not tuple(tmp_path.iterdir())
    spawn.assert_not_called()


@pytest.mark.parametrize("configured_mode", tuple(TransportMode))
@pytest.mark.parametrize("requested_mode", (None, *TransportMode))
def test_catalog_route_uses_injected_config_owner(configured_mode, requested_mode):
    from openhcs.agent.services.endpoint_function_catalog_service import (
        ZMQFunctionCatalogService,
    )

    config = OpenHCSZMQConfig(transport_mode=configured_mode)
    provider = Mock(return_value=config)
    factory = Mock(side_effect=AssertionError("No catalog startup or network"))
    service = ZMQFunctionCatalogService(provider, client_factory=factory)
    connection = ExecutionConnectionSpec(
        host="127.0.0.1", port=5968, transport_mode=requested_mode
    )
    projected = service._endpoint_for_connection(connection)
    assert projected.client_endpoint() == connection.execution_client(config).endpoint
    provider.assert_called_once()
    factory.assert_not_called()


def test_startup_returns_typed_native_handle_without_catalogue_or_wait(
    setup, monkeypatch
):
    service, request, spawn = setup
    monkeypatch.setattr(
        ZMQExecutionClient,
        "_wait_for_endpoint_ready",
        Mock(side_effect=AssertionError("No inline warming/wait")),
    )
    state = service.start_from_request(request)
    assert not state.ready
    assert state.handle.process_identity == ProcessIdentity.current()
    assert state.handle.connection == request.connection
    assert (
        dataclass_from_mapping(RuntimeBootstrapHandle, to_jsonable(state.handle))
        == state.handle
    )
    spawn.assert_called_once()


@pytest.mark.parametrize("target", ["data", "cache", "transport"])
def test_owner_derived_denied_writes_precede_spawn(setup, tmp_path, target):
    _, request, spawn = setup
    roots = (tmp_path / "data", tmp_path / "cache", tmp_path / ".openhcs")
    excluded = {"data": roots[0], "cache": roots[1], "transport": roots[2]}[target]
    service = RuntimeServerService(
        path_policy=AgentPathPolicy.with_roots(
            readable_roots=(tmp_path,),
            writable_roots=tuple(root for root in roots if root != excluded),
        )
    )
    with pytest.raises(AgentPathPolicyError):
        service.start_from_request(request)
    spawn.assert_not_called()
    assert not (tmp_path / "data").exists()


def test_symlink_escape_rejected_before_any_launch_write(setup, tmp_path, monkeypatch):
    _, request, spawn = setup
    allowed = tmp_path / "allowed"
    allowed.mkdir()
    outside = tmp_path / "outside"
    outside.mkdir()
    sentinel = outside / "sentinel"
    sentinel.write_text("unchanged", encoding="utf-8")
    (allowed / "data").symlink_to(outside, target_is_directory=True)
    monkeypatch.setenv("XDG_DATA_HOME", str(allowed / "data"))
    service = RuntimeServerService(
        path_policy=AgentPathPolicy.with_roots(
            readable_roots=(allowed,), writable_roots=(allowed,)
        )
    )
    with pytest.raises(AgentPathPolicyError):
        service.start_from_request(request)
    spawn.assert_not_called()
    assert sentinel.read_text() == "unchanged"
    assert not (outside / "openhcs").exists()


def test_foreign_endpoint_rejected_before_spawn(setup):
    service, request, spawn = setup
    with pytest.raises(ValueError, match="local"):
        service.start_from_request(
            replace(request, connection=replace(request.connection, host="203.0.113.7"))
        )
    spawn.assert_not_called()


def test_explicit_port_and_bounded_deadline():
    with pytest.raises(ValueError, match="explicit port"):
        RuntimeBootstrapStartRequest.from_fields()
    with pytest.raises(ValueError, match="control budget"):
        RuntimeBootstrapStartRequest.from_fields(port=5913, timeout_ms=10_000)


def test_no_response_preserves_same_pending_handle(setup, monkeypatch):
    service, request, spawn = setup
    started = service.start_from_request(request)
    monkeypatch.setattr(TransportEndpoint, "ping", lambda *_args, **_kwargs: None)
    observed = service.observe_bootstrap(RuntimeBootstrapObserveRequest(started.handle))
    assert observed.handle == started.handle
    assert observed.process_alive
    assert not observed.ready
    assert observed.progress.phase is EndpointStartupPhase.STARTING_PROCESS
    spawn.assert_called_once()


@pytest.mark.parametrize("phase", [None, *EndpointStartupPhase])
@pytest.mark.parametrize("heartbeat_ready", [None, False, True])
def test_bootstrap_state_derives_readiness_from_typed_native_observations(
    setup, phase, heartbeat_ready
):
    service, request, spawn = setup
    handle = service.start_from_request(request).handle
    statuses = (
        ()
        if phase is None
        else (EndpointStartupStatus(phase, "original child activity", sequence=17),)
    )
    pong = (
        None
        if heartbeat_ready is None
        else PongResponse(
            port=handle.connection.port,
            control_port=6913,
            ready=heartbeat_ready,
            server="fixture",
            server_role=ServerRole.EXECUTION,
            process_identity=handle.process_identity,
        )
    )
    result = RuntimeBootstrapState.from_observation(
        handle, process_alive=True, statuses=statuses, pong=pong
    )
    assert result.handle is handle
    assert result.ready is (heartbeat_ready is True)
    assert result.process_alive is True
    if heartbeat_ready is True:
        assert result.progress.phase is EndpointStartupPhase.CONNECTED
    elif statuses:
        assert result.progress is statuses[-1]
    else:
        assert result.progress.phase is EndpointStartupPhase.STARTING_PROCESS
    assert dataclass_from_mapping(RuntimeBootstrapState, to_jsonable(result)) == result
    spawn.assert_called_once()  # Projection never starts or resubmits.


@pytest.mark.parametrize("alive", [False, None])
def test_bootstrap_state_preserves_terminal_vs_unknown_process_identity(setup, alive):
    service, request, _ = setup
    handle = service.start_from_request(request).handle
    result = RuntimeBootstrapState.from_observation(
        handle, process_alive=alive, statuses=(), pong=None
    )
    assert result.handle is handle and not result.ready
    assert result.process_alive is alive
    assert result.progress.phase is (
        EndpointStartupPhase.FAILED
        if alive is False
        else EndpointStartupPhase.STARTING_PROCESS
    )


@pytest.mark.parametrize("wrong_identity", [False, True])
def test_bootstrap_state_rejects_foreign_incarnation_or_role(setup, wrong_identity):
    service, request, _ = setup
    handle = service.start_from_request(request).handle
    identity = replace(
        handle.process_identity, create_time=handle.process_identity.create_time - 1
    )
    pong = PongResponse(
        port=5913,
        control_port=6913,
        ready=True,
        server="fixture",
        server_role=ServerRole.EXECUTION if wrong_identity else ServerRole.VIEWER,
        process_identity=identity if wrong_identity else handle.process_identity,
    )
    with pytest.raises(RuntimeError, match="different native owner"):
        RuntimeBootstrapState.from_observation(
            handle, process_alive=True, statuses=(), pong=pong
        )


def test_normal_context_injects_path_admission(setup, tmp_path):
    _, request, spawn = setup
    denied = AgentPathPolicy.with_roots(readable_roots=(tmp_path,), writable_roots=())
    context = OpenHCSAgentContext(path_policy=denied)
    with pytest.raises(AgentPathPolicyError):
        context.runtime_server_service.start_from_request(request)
    spawn.assert_not_called()


def test_declaration_projects_startup_mcp_and_cli_contract():
    declaration = agent_capabilities.start_owned_runtime
    assert declaration.input_contract is RuntimeBootstrapStartRequest
    assert declaration.cli_command == "runtime-start-owned"
    assert declaration.mutating
    assert (
        agent_capabilities.observe_owned_runtime.input_contract
        is RuntimeBootstrapObserveRequest
    )
    assert (
        agent_capabilities.close_owned_runtime.input_contract
        is RuntimeBootstrapCloseRequest
    )
    assert agent_capabilities.close_owned_runtime.mutating


@pytest.mark.parametrize("exited", [False, True, None])
def test_close_preserves_native_outcome_and_original_handle(setup, monkeypatch, exited):
    service, request, spawn = setup
    started = service.start_from_request(request)
    outcome = EndpointShutdownResult(
        succeeded=exited is True,
        endpoint_terminated=True,
        process_identity=started.handle.process_identity,
        process_exited=exited,
        request_attempted=True,
        acknowledged=True,
    )
    close = Mock(return_value=outcome)
    monkeypatch.setattr(ZMQExecutionClient, "close_owned_process", close)
    result = service.close_bootstrap(RuntimeBootstrapCloseRequest(started.handle))
    assert result.handle == started.handle
    assert result.outcome == outcome
    assert bool(result.errors) is (exited is not True)
    assert (
        dataclass_from_mapping(RuntimeBootstrapCloseResult, to_jsonable(result))
        == result
    )
    close.assert_called_once()
    assert close.call_args.args == (started.handle.process_identity,)
    assert close.call_args.kwargs["mode"] is EndpointShutdownMode.FORCE
    assert close.call_args.kwargs["operation_deadline"].timeout_ms == 5000
    spawn.assert_called_once()


def test_close_native_transport_write_admission_precedes_lifecycle(
    setup, tmp_path, monkeypatch
):
    service, request, _ = setup
    started = service.start_from_request(request)
    close = Mock(
        side_effect=AssertionError("No lifecycle after denied native lock path")
    )
    monkeypatch.setattr(ZMQExecutionClient, "close_owned_process", close)
    # The serialized plan cannot confer admission to native paths in a changed
    # launch environment. The actual declaration is checked before lock writes.
    new_home = tmp_path / "not-authorised"
    new_home.mkdir()
    monkeypatch.setenv("HOME", str(new_home))
    policy = AgentPathPolicy.with_roots(
        readable_roots=(tmp_path,),
        writable_roots=(tmp_path / "data", tmp_path / "cache", tmp_path / ".openhcs"),
    )
    denied = RuntimeServerService(path_policy=policy)
    with pytest.raises(AgentPathPolicyError):
        denied.close_bootstrap(RuntimeBootstrapCloseRequest(started.handle))
    close.assert_not_called()
    assert not (new_home / ".openhcs").exists()


def test_close_timeout_and_typed_mode_contract(setup):
    from typing import get_type_hints

    service, request, _ = setup
    started = service.start_from_request(request)
    hints = get_type_hints(RuntimeBootstrapCloseRequest, include_extras=True)
    assert hints["mode"] is EndpointShutdownMode
    assert (
        dataclass_from_mapping(
            RuntimeBootstrapCloseRequest,
            {
                "handle": to_jsonable(started.handle),
                "mode": "graceful",
                "timeout_ms": 500,
            },
        ).mode
        is EndpointShutdownMode.GRACEFUL
    )
    for timeout in (0, -1, 10000, True):
        with pytest.raises((ValueError, TypeError)):
            RuntimeBootstrapCloseRequest(started.handle, timeout_ms=timeout)


@pytest.mark.parametrize("ready", [False, True])
def test_readiness_uses_native_declaration_not_just_a_ping(setup, monkeypatch, ready):
    service, request, spawn = setup
    started = service.start_from_request(request)
    pong = PongResponse(
        port=5913,
        control_port=5914,
        ready=ready,
        server="fixture",
        server_role=ServerRole.EXECUTION,
        process_identity=started.handle.process_identity,
    )
    monkeypatch.setattr(TransportEndpoint, "ping", lambda *_args, **_kwargs: pong)
    observed = service.observe_bootstrap(RuntimeBootstrapObserveRequest(started.handle))
    assert observed.ready is ready
    assert observed.handle == started.handle
    spawn.assert_called_once()


def test_changed_incarnation_is_never_readiness(setup, monkeypatch):
    service, request, spawn = setup
    started = service.start_from_request(request)
    other = replace(
        started.handle.process_identity,
        create_time=started.handle.process_identity.create_time - 1,
    )
    pong = PongResponse(
        port=5913,
        control_port=5914,
        ready=True,
        server="fixture",
        server_role=ServerRole.EXECUTION,
        process_identity=other,
    )
    monkeypatch.setattr(TransportEndpoint, "ping", lambda *_args, **_kwargs: pong)
    with pytest.raises(RuntimeError, match="different native owner"):
        service.observe_bootstrap(RuntimeBootstrapObserveRequest(started.handle))
    spawn.assert_called_once()


def test_failed_reservation_keeps_exact_child_and_uncertainty(setup, monkeypatch):
    service, request, spawn = setup
    monkeypatch.setattr(
        TransportMode.TCP.declaration,
        "record_startup_owner",
        Mock(side_effect=[None, None, OSError("readonly reservation")]),
    )
    result = service.start_from_request(request)
    assert result.handle.process_identity == ProcessIdentity.current()
    assert result.errors[0].code == "runtime_bootstrap_uncertain"
    assert not result.ready
    spawn.assert_called_once()


def test_real_cli_projection_builds_explicit_connection_without_dispatch():
    from openhcs.mcp.dev_client import _build_parser, _calls_from_args

    parser = _build_parser()
    args = parser.parse_args(
        [
            "runtime-start-owned",
            "5913",
            "--host",
            "127.0.0.1",
            "--transport-mode",
            "tcp",
        ]
    )
    calls = _calls_from_args(args)
    assert len(calls) == 1
    assert calls[0].name == agent_capabilities.start_owned_runtime.name
    assert calls[0].arguments["port"] == 5913
    assert calls[0].arguments["transport_mode"] == "tcp"


def test_bootstrap_is_exposed_on_existing_authoring_and_core_surfaces():
    from openhcs.agent.capabilities import (
        AuthoringLocalCapabilitySurfaceProfile,
        CoreLocalCapabilitySurfaceProfile,
    )

    for profile in (
        AuthoringLocalCapabilitySurfaceProfile(),
        CoreLocalCapabilitySurfaceProfile(),
    ):
        assert profile.includes(agent_capabilities.start_owned_runtime)
        assert profile.includes(agent_capabilities.observe_owned_runtime)
        assert profile.includes(agent_capabilities.close_owned_runtime)


def test_close_uses_standard_context_and_declared_service_invocation(
    setup, tmp_path, monkeypatch
):
    service, request, _ = setup
    handle = service.start_from_request(request).handle
    close = Mock(
        return_value=EndpointShutdownResult(True, True, handle.process_identity, True)
    )
    monkeypatch.setattr(ZMQExecutionClient, "close_owned_process", close)
    context = OpenHCSAgentContext(
        path_policy=AgentPathPolicy.with_roots(
            readable_roots=(tmp_path,), writable_roots=(tmp_path,)
        )
    )
    typed_request = dataclass_from_mapping(
        RuntimeBootstrapCloseRequest, {"handle": to_jsonable(handle)}
    )
    from openhcs.agent.capabilities import get_agent_capability_declaration

    declaration = get_agent_capability_declaration(
        agent_capabilities.close_owned_runtime.name
    )
    result = declaration.request_invocation.execute(context, typed_request)
    assert result.handle == handle and result.outcome.process_exited is True
    close.assert_called_once()
