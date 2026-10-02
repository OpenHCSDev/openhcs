"""Built-in destination and route admission before custom source side effects."""

import asyncio
import json
from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest
from zmqruntime.config import TransportMode
from zmqruntime.messages import ProcessIdentity
from zmqruntime.startup import EndpointStartupPhase, EndpointStartupStatus

from openhcs.agent.dto.common import SCHEMA_VERSION
from openhcs.agent.dto.functions import (
    CustomFunctionRegistrationDestination,
    CustomFunctionRegistrationDestinationRequest,
    CustomFunctionRegistrationRequest,
    CustomFunctionRegistrationResult,
    FunctionCatalogNotReadyError,
    FunctionCatalogPreparationHandle,
    FunctionCatalogPreparationOutcome,
    FunctionCatalogPreparationState,
)
from openhcs.agent.path_policy import AgentPathPolicy, AgentPathPolicyError
from openhcs.agent.services.endpoint_function_catalog_service import (
    CustomFunctionRegistrationUncertainError,
    ZMQFunctionCatalogService,
)
from openhcs.agent.services.function_catalog_service import FunctionCatalogService
from openhcs.processing.custom_functions.manager import CustomFunctionManager
from openhcs.processing.custom_functions.runtime_registry import (
    CustomFunctionRuntimeRegistry,
)
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG
from openhcs.runtime.zmq_execution_client import FunctionCatalogEndpointUnavailableError


def request(root, **changes):
    return replace(
        CustomFunctionRegistrationRequest.from_fields(
            source_code="@numpy\ndef boundary_probe(image):\n    return image\n",
            function_name="boundary_probe",
            storage_dir=str(root),
            port=15993,
            transport_mode=TransportMode.TCP,
        ),
        **changes,
    )


def policy(root):
    return AgentPathPolicy.with_roots(readable_roots=(root,), writable_roots=(root,))


def preparation_state(handle, outcome=FunctionCatalogPreparationOutcome.READY):
    return FunctionCatalogPreparationState(
        schema_version=SCHEMA_VERSION,
        handle=handle,
        outcome=outcome,
        progress=EndpointStartupStatus(
            phase=EndpointStartupPhase.PREPARING_CAPABILITIES, message="Witness"
        ),
    )


def test_missing_explicit_route_rejects_before_client_creation(tmp_path):
    made = []
    catalog = ZMQFunctionCatalogService(
        lambda: OPENHCS_ZMQ_CONFIG,
        client_factory=lambda endpoint: made.append(endpoint),
        path_policy=policy(tmp_path),
    )
    with pytest.raises(ValueError, match="explicit port"):
        catalog.register_custom_function(
            CustomFunctionRegistrationRequest(source_code="not evaluated")
        )
    assert not made


@pytest.mark.parametrize("escape", ("ordinary", "ancestor", "destination"))
def test_write_escape_rejects_before_endpoint_dispatch(tmp_path, escape):
    owned = tmp_path / "owned"
    outside = tmp_path / "outside"
    owned.mkdir()
    outside.mkdir()
    sentinel = outside / "boundary_probe.py"
    sentinel.write_text("preserve")
    root = outside if escape == "ordinary" else owned / "custom"
    if escape == "ancestor":
        root.symlink_to(outside, target_is_directory=True)
    elif escape == "destination":
        root.mkdir()
        (root / sentinel.name).symlink_to(sentinel)
    made = []
    catalog = ZMQFunctionCatalogService(
        lambda: OPENHCS_ZMQ_CONFIG,
        client_factory=lambda endpoint: made.append(endpoint),
        path_policy=policy(owned),
    )
    with pytest.raises(AgentPathPolicyError):
        catalog.register_custom_function(request(root))
    assert not made
    assert sentinel.read_text() == "preserve"


@pytest.mark.parametrize(
    "wrong_store, timeout",
    ((False, False), (True, False), (False, True), (False, "owner_closed")),
)
def test_exact_owned_route_and_store_precede_mutation(tmp_path, wrong_store, timeout):
    root = tmp_path / "custom"
    mutations = []
    endpoints = []

    class Client:
        def custom_function_registration_destination(
            self, probe, *, operation_deadline=None
        ):
            assert probe.function_name == "boundary_probe"
            native = tmp_path / "foreign" if wrong_store else root
            return CustomFunctionRegistrationDestination(
                str(native), str(native / "boundary_probe.py")
            )

        def register_custom_function(self, admitted, *, operation_deadline=None):
            if timeout == "owner_closed":
                raise FunctionCatalogEndpointUnavailableError(
                    "Admission rejected before source dispatch"
                )
            mutations.append(admitted)
            assert admitted.admission_policy == policy(tmp_path)
            assert admitted.server_identity == ProcessIdentity.current()
            if timeout:
                raise TimeoutError("controlled post-dispatch observation")
            return CustomFunctionRegistrationResult(
                schema_version=SCHEMA_VERSION,
                connection=admitted.connection,
                server_identity=admitted.server_identity,
                storage_dir=str(root),
                source_file_paths=(str(root / "boundary_probe.py"),),
            )

        def function_catalog_preparation(
            self, read_request, *, operation_deadline=None
        ):
            assert not hasattr(read_request, "source_code")
            assert not mutations
            return preparation_state(read_request.handle)

        def disconnect(self):
            pass

    def factory(endpoint):
        endpoints.append(endpoint)
        return Client()

    catalog = ZMQFunctionCatalogService(
        lambda: OPENHCS_ZMQ_CONFIG, client_factory=factory, path_policy=policy(tmp_path)
    )
    if wrong_store:
        with pytest.raises(ValueError, match="no source was dispatched"):
            catalog.register_custom_function(request(root))
        assert not mutations
    elif timeout == "owner_closed":
        with pytest.raises(
            FunctionCatalogEndpointUnavailableError, match="before source dispatch"
        ):
            catalog.register_custom_function(request(root))
        assert not mutations
    elif timeout:
        with pytest.raises(CustomFunctionRegistrationUncertainError, match="uncertain"):
            catalog.register_custom_function(request(root))
        assert len(mutations) == 1
        assert catalog._config_provider().default_port == 15993
    else:
        result = catalog.register_custom_function(request(root))
        assert result.connection.port == 15993
        assert len(mutations) == 1
        assert catalog._config_provider().default_port == 15993
    assert [endpoint.default_port for endpoint in endpoints] == [15993]
    assert not root.exists()
    catalog.close()


def test_native_destination_query_does_not_create_storage(tmp_path, monkeypatch):
    monkeypatch.setenv("XDG_DATA_HOME", str(tmp_path / "absent"))
    result = FunctionCatalogService(
        path_policy=policy(tmp_path)
    ).custom_function_registration_destination(
        CustomFunctionRegistrationDestinationRequest(function_name="boundary_probe")
    )
    assert Path(result.storage_dir) == CustomFunctionManager.default_storage_directory()
    assert Path(result.source_file_path) == CustomFunctionManager.source_path_for_name(
        Path(result.storage_dir), "boundary_probe"
    )
    assert not (tmp_path / "absent").exists()


def test_local_denial_precedes_manager_evaluation_and_creation(tmp_path, monkeypatch):
    monkeypatch.setenv("XDG_DATA_HOME", str(tmp_path / "foreign"))
    evaluated = []
    monkeypatch.setattr(
        CustomFunctionManager, "_prepare_source", lambda *args: evaluated.append(args)
    )
    root = CustomFunctionManager.default_storage_directory()
    with pytest.raises(AgentPathPolicyError):
        FunctionCatalogService(
            path_policy=policy(tmp_path / "owned")
        ).register_custom_function(request(root))
    assert not evaluated
    assert not (tmp_path / "foreign").exists()


@pytest.mark.parametrize("escape", ("ordinary", "ancestor", "destination"))
def test_native_escape_denial_preserves_registry_and_sentinel(
    tmp_path, monkeypatch, escape
):
    owned = tmp_path / "owned"
    outside = tmp_path / "outside"
    owned.mkdir()
    outside.mkdir()
    sentinel = outside / "boundary_probe.py"
    sentinel.write_text("preserve native sentinel")
    data_home = outside if escape == "ordinary" else owned
    monkeypatch.setenv("XDG_DATA_HOME", str(data_home))
    root = CustomFunctionManager.default_storage_directory()
    if escape == "ancestor":
        root.parent.mkdir()
        root.symlink_to(outside, target_is_directory=True)
    elif escape == "destination":
        root.mkdir(parents=True)
        (root / sentinel.name).symlink_to(sentinel)
    before = CustomFunctionRuntimeRegistry.metadata_by_name()
    evaluated = []
    monkeypatch.setattr(
        CustomFunctionManager, "_prepare_source", lambda *args: evaluated.append(args)
    )
    with pytest.raises(AgentPathPolicyError):
        FunctionCatalogService(path_policy=policy(owned)).register_custom_function(
            request(root, server_identity=ProcessIdentity.current())
        )
    assert not evaluated
    assert CustomFunctionRuntimeRegistry.metadata_by_name() == before
    assert sentinel.read_text() == "preserve native sentinel"


def test_public_factory_cannot_expand_write_authority(tmp_path):
    with pytest.raises(TypeError, match="admission_policy"):
        CustomFunctionRegistrationRequest.from_fields(
            source_code="", admission_policy=policy(tmp_path)
        )
    with pytest.raises(TypeError, match="server_identity"):
        CustomFunctionRegistrationRequest.from_fields(
            source_code="", server_identity=ProcessIdentity.current()
        )


@pytest.mark.parametrize(
    "identity", (None, replace(ProcessIdentity.current(), create_time=0))
)
def test_changed_or_missing_native_owner_rejects_before_evaluation(
    tmp_path, monkeypatch, identity
):
    monkeypatch.setenv("XDG_DATA_HOME", str(tmp_path))
    evaluated = []
    monkeypatch.setattr(
        CustomFunctionManager, "_prepare_source", lambda *args: evaluated.append(args)
    )
    root = CustomFunctionManager.default_storage_directory()
    with pytest.raises(ValueError, match="no source was evaluated"):
        FunctionCatalogService(path_policy=policy(tmp_path)).register_custom_function(
            request(root, server_identity=identity)
        )
    assert not evaluated
    assert not root.exists()


def test_caller_admission_cannot_expand_native_server_policy(tmp_path, monkeypatch):
    monkeypatch.setenv("XDG_DATA_HOME", str(tmp_path))
    root = CustomFunctionManager.default_storage_directory()
    admitted = request(root, server_identity=ProcessIdentity.current()).admitted(
        policy(tmp_path)
    )
    with pytest.raises(AgentPathPolicyError):
        FunctionCatalogService(
            path_policy=policy(tmp_path / "restricted")
        ).register_custom_function(admitted)
    assert not root.exists()


def test_native_destination_file_must_match_admitted_name(tmp_path):
    destination = CustomFunctionRegistrationDestination(
        str(tmp_path), str(tmp_path / "other.py")
    )
    with pytest.raises(ValueError, match="no source was dispatched"):
        destination.require_request(request(tmp_path))


def test_wrong_owner_mutation_receipt_is_uncertain_not_replayed(tmp_path):
    mutations = []

    class Client:
        def custom_function_registration_destination(
            self, probe, *, operation_deadline=None
        ):
            return CustomFunctionRegistrationDestination(
                str(tmp_path), str(tmp_path / "boundary_probe.py")
            )

        def register_custom_function(self, admitted, *, operation_deadline=None):
            mutations.append(admitted)
            return CustomFunctionRegistrationResult(
                schema_version=SCHEMA_VERSION,
                connection=admitted.connection,
                server_identity=replace(ProcessIdentity.current(), create_time=0),
            )

        def function_catalog_preparation(
            self, read_request, *, operation_deadline=None
        ):
            assert not hasattr(read_request, "source_code")
            assert not mutations
            return preparation_state(read_request.handle)

        def disconnect(self):
            pass

    catalog = ZMQFunctionCatalogService(
        lambda: OPENHCS_ZMQ_CONFIG,
        client_factory=lambda endpoint: Client(),
        path_policy=policy(tmp_path),
    )
    try:
        with pytest.raises(
            CustomFunctionRegistrationUncertainError, match="Selected server"
        ):
            catalog.register_custom_function(request(tmp_path))
        assert len(mutations) == 1
        assert catalog._config_provider().default_port == 15993
    finally:
        catalog.close()


@pytest.mark.parametrize(
    "outcome",
    tuple(state for state in FunctionCatalogPreparationOutcome if not state.ready),
)
def test_readiness_failure_precedes_mutation_and_is_not_postdispatch_uncertainty(
    tmp_path,
    outcome,
):
    observed = []

    class Client:
        def custom_function_registration_destination(
            self, probe, *, operation_deadline=None
        ):
            observed.append("destination")
            return CustomFunctionRegistrationDestination(
                str(tmp_path), str(tmp_path / "boundary_probe.py")
            )

        def function_catalog_preparation(
            self, read_request, *, operation_deadline=None
        ):
            assert not hasattr(read_request, "source_code")
            observed.append("read-only-preparation")
            return preparation_state(read_request.handle, outcome)

        def register_custom_function(self, admitted, *, operation_deadline=None):
            pytest.fail("Source must not be dispatched after readiness failure")

        def disconnect(self):
            pass

    catalog = ZMQFunctionCatalogService(
        lambda: OPENHCS_ZMQ_CONFIG,
        client_factory=lambda endpoint: Client(),
        path_policy=policy(tmp_path),
    )
    try:
        with pytest.raises(FunctionCatalogNotReadyError) as failure:
            catalog.register_custom_function(request(tmp_path))
        assert not isinstance(failure.value, CustomFunctionRegistrationUncertainError)
        assert observed == ["destination", "read-only-preparation"]
        assert catalog._config_provider().default_port == 15993
    finally:
        catalog.close()


def test_registration_cli_projects_declarations_and_rejects_missing_route(tmp_path):
    from openhcs.mcp.dev_client import _build_parser, _calls_from_args
    from openhcs.mcp.dev_client_core import McpDevCliUsageError

    parser = _build_parser()
    missing = parser.parse_args(("register-custom-function", "--source-code", "source"))
    with pytest.raises(McpDevCliUsageError, match="explicit port"):
        _calls_from_args(missing)
    args = parser.parse_args(
        (
            "register-custom-function",
            "--source-code",
            "source",
            "--port",
            "15993",
            "--storage-dir",
            str(tmp_path),
            "--function-name",
            "boundary_probe",
            "--transport-mode",
            "tcp",
        )
    )
    (call,) = _calls_from_args(args)
    assert call.name == "openhcs_register_custom_function"
    assert call.arguments["port"] == 15993
    assert call.arguments["transport_mode"] == "tcp"
    assert call.arguments["storage_dir"] == str(tmp_path)
    assert call.arguments["function_name"] == "boundary_probe"
    assert "server_identity" not in call.arguments


def test_manager_admitted_persistence_uses_existing_registry_and_source_owner(
    tmp_path, monkeypatch
):
    monkeypatch.setenv("XDG_DATA_HOME", str(tmp_path))
    for name in (
        "_declarations_by_name",
        "_published_exports",
        "_preparation_outcomes",
        "_preparation_threads",
    ):
        monkeypatch.setattr(CustomFunctionRuntimeRegistry, name, {})
    monkeypatch.setattr(CustomFunctionRuntimeRegistry, "_source_revision", None)
    manager = CustomFunctionManager(create_storage=False)
    try:
        [function] = manager.register_from_code(
            request(manager.storage_dir).source_code,
            expected_function_name="boundary_probe",
            write_admission=policy(tmp_path).assert_writable,
            clear_caches=False,
            emit_signal=False,
        )
        source = manager.source_path_for_function(function)
        assert source == manager.source_path_for_name(
            manager.storage_dir, "boundary_probe"
        )
        assert source.read_text() == request(manager.storage_dir).source_code
        assert (
            CustomFunctionRuntimeRegistry.metadata_by_name()["boundary_probe"].func
            is function
        )
        import numpy as np

        image = np.arange(4).reshape(2, 2)
        np.testing.assert_array_equal(function(image), image)
        CustomFunctionRuntimeRegistry.clear()
        from openhcs.processing.custom_functions import boundary_probe

        assert boundary_probe.__module__ == "openhcs.processing.custom_functions"
        np.testing.assert_array_equal(boundary_probe(image), image)
    finally:
        CustomFunctionRuntimeRegistry.clear()


@pytest.mark.parametrize("operation", ("require", "load", "read", "delete", "update"))
def test_manager_named_source_operations_use_filename_owner(
    tmp_path, monkeypatch, operation
):
    from openhcs.processing.custom_functions.source_namespace import (
        CustomFunctionSource,
    )

    monkeypatch.setenv("XDG_DATA_HOME", str(tmp_path))
    manager = CustomFunctionManager(create_storage=False)
    selected = []

    def own_path(root, name):
        selected.append((root, name))
        raise LookupError("filename-owner-witness")

    monkeypatch.setattr(manager, "source_path_for_name", own_path)
    operations = {
        "require": lambda: manager.require_source(
            CustomFunctionSource(
                function_name="boundary_probe", content_sha256="0" * 64
            )
        ),
        "load": lambda: manager.load_custom_function("boundary_probe"),
        "read": lambda: manager.get_function_code("boundary_probe"),
        "delete": lambda: manager.delete_custom_function("boundary_probe"),
        "update": lambda: manager.update_custom_function(
            "boundary_probe", "not evaluated"
        ),
    }
    with pytest.raises(LookupError, match="filename-owner-witness"):
        operations[operation]()
    assert selected == [(manager.storage_dir, "boundary_probe")]
    assert not manager.storage_dir.exists()


@pytest.mark.parametrize("missing_route", (False, True))
def test_real_generated_mcp_boundary_excludes_authority_and_denies_before_client(
    tmp_path, missing_route
):
    from openhcs.mcp.server import build_server

    made = []
    catalog = ZMQFunctionCatalogService(
        lambda: OPENHCS_ZMQ_CONFIG,
        client_factory=lambda endpoint: made.append(endpoint),
        path_policy=policy(tmp_path / "owned"),
    )

    async def invoke():
        built = build_server(SimpleNamespace(function_catalog=catalog))
        tool = next(
            tool
            for tool in await built.list_tools()
            if tool.name == "openhcs_register_custom_function"
        )
        properties = tool.inputSchema["properties"]
        assert {"port", "host", "storage_dir", "function_name"} <= properties.keys()
        assert {"admission_policy", "server_identity"}.isdisjoint(properties)
        arguments = {
            "source_code": "not evaluated",
            "function_name": "boundary_probe",
            "storage_dir": str(tmp_path / "outside"),
        }
        if not missing_route:
            arguments["port"] = 15993
        return await built.call_tool("openhcs_register_custom_function", arguments)

    result = asyncio.run(invoke())
    content = result[0] if isinstance(result, tuple) else result.content
    payload = json.loads(content[0].text)
    error = payload["errors"][0]
    assert error["code"] == (
        "mcp_tool_failed" if missing_route else "agent_path_policy_rejected"
    )
    assert not made
    catalog.close()


def test_generated_mcp_preparation_tools_use_reflected_connection_and_handle():
    from openhcs.agent.dto.execution_connection import ExecutionConnectionSpec
    from openhcs.mcp.server import build_server

    observed = []
    handle = FunctionCatalogPreparationHandle(
        ExecutionConnectionSpec(port=15993, transport_mode=TransportMode.TCP),
        ProcessIdentity.current(),
    )

    class Catalog:
        def start_catalog_preparation(self, connection):
            observed.append(connection)
            return preparation_state(handle, FunctionCatalogPreparationOutcome.PENDING)

        def catalog_preparation_status(self, current_handle):
            observed.append(current_handle)
            return preparation_state(current_handle)

        def cancel_catalog_preparation(self, current_handle):
            observed.append(current_handle)
            return preparation_state(
                current_handle, FunctionCatalogPreparationOutcome.CANCELLED
            )

    async def invoke():
        built = build_server(SimpleNamespace(endpoint_function_catalog=Catalog()))
        tools = {tool.name: tool for tool in await built.list_tools()}
        assert {"port", "host", "transport_mode"} <= tools[
            "openhcs_start_function_catalog_preparation"
        ].inputSchema["properties"].keys()
        assert {"connection", "server_identity"} == tools[
            "openhcs_get_function_catalog_preparation_status"
        ].inputSchema["properties"].keys()
        started = await built.call_tool(
            "openhcs_start_function_catalog_preparation",
            {"port": 15993, "transport_mode": "tcp"},
        )
        from openhcs.serialization.json import to_jsonable

        args = to_jsonable(handle)
        status = await built.call_tool(
            "openhcs_get_function_catalog_preparation_status", args
        )
        cancelled = await built.call_tool(
            "openhcs_cancel_function_catalog_preparation", args
        )
        for response in (started, status, cancelled):
            content = response[0] if isinstance(response, tuple) else response.content
            assert not json.loads(content[0].text).get("errors")

    asyncio.run(invoke())
    assert observed == [handle.connection, handle, handle]
