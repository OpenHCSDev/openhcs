from dataclasses import replace
from unittest.mock import Mock

import pytest
from python_introspect import dataclass_from_mapping
from openhcs.serialization.json import to_jsonable
from zmqruntime.config import TransportMode
from zmqruntime.messages import ProcessIdentity, PongResponse, ServerRole
from zmqruntime.startup import EndpointStartupPhase
from zmqruntime.transport import TransportEndpoint

from openhcs.agent.capabilities import agent_capabilities
from openhcs.agent.dto.execution import (
    RuntimeBootstrapStartRequest,
    RuntimeBootstrapObserveRequest,
    RuntimeBootstrapHandle,
    RuntimeBootstrapCloseRequest,
    RuntimeBootstrapCloseResult,
)
from openhcs.agent.path_policy import AgentPathPolicy, AgentPathPolicyError
from openhcs.agent.services.runtime_server_service import RuntimeServerService
from openhcs.mcp.context import OpenHCSAgentContext
from openhcs.runtime.zmq_execution_client import ZMQExecutionClient
from zmqruntime.client import (
    EndpointProcess,
    EndpointShutdownMode,
    EndpointShutdownResult,
)


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
