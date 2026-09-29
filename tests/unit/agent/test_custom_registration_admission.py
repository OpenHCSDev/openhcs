"""Built-in destination and route admission before custom source side effects."""

from dataclasses import replace
from pathlib import Path

import pytest
from zmqruntime.config import TransportMode

from openhcs.agent.dto.common import SCHEMA_VERSION
from openhcs.agent.dto.functions import (
    CustomFunctionRegistrationDestination,
    CustomFunctionRegistrationDestinationRequest,
    CustomFunctionRegistrationRequest,
    CustomFunctionRegistrationResult,
)
from openhcs.agent.path_policy import AgentPathPolicy, AgentPathPolicyError
from openhcs.agent.services.endpoint_function_catalog_service import (
    CustomFunctionRegistrationUncertainError,
    ZMQFunctionCatalogService,
)
from openhcs.agent.services.function_catalog_service import FunctionCatalogService
from openhcs.processing.custom_functions.manager import CustomFunctionManager
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG


def request(root, **changes):
    return replace(CustomFunctionRegistrationRequest.from_fields(
        source_code="@numpy\ndef boundary_probe(image):\n    return image\n",
        function_name="boundary_probe", storage_dir=str(root), port=15993,
        transport_mode=TransportMode.TCP,
    ), **changes)


def policy(root):
    return AgentPathPolicy.with_roots(readable_roots=(root,), writable_roots=(root,))


def test_missing_explicit_route_rejects_before_client_creation(tmp_path):
    made = []
    catalog = ZMQFunctionCatalogService(lambda: OPENHCS_ZMQ_CONFIG,
        client_factory=lambda endpoint: made.append(endpoint), path_policy=policy(tmp_path))
    with pytest.raises(ValueError, match="explicit port"):
        catalog.register_custom_function(CustomFunctionRegistrationRequest(source_code="not evaluated"))
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
    catalog = ZMQFunctionCatalogService(lambda: OPENHCS_ZMQ_CONFIG,
        client_factory=lambda endpoint: made.append(endpoint), path_policy=policy(owned))
    with pytest.raises(AgentPathPolicyError):
        catalog.register_custom_function(request(root))
    assert not made
    assert sentinel.read_text() == "preserve"


@pytest.mark.parametrize("wrong_store, timeout", ((False, False), (True, False), (False, True)))
def test_exact_owned_route_and_store_precede_mutation(tmp_path, wrong_store, timeout):
    root = tmp_path / "custom"
    mutations = []
    endpoints = []
    class Client:
        def custom_function_registration_destination(self, probe):
            assert probe.function_name == "boundary_probe"
            native = tmp_path / "foreign" if wrong_store else root
            return CustomFunctionRegistrationDestination(str(native), str(native / "boundary_probe.py"))
        def register_custom_function(self, admitted):
            mutations.append(admitted)
            assert admitted.admission_policy == policy(tmp_path)
            if timeout:
                raise TimeoutError("controlled post-dispatch observation")
            return CustomFunctionRegistrationResult(schema_version=SCHEMA_VERSION, connection=admitted.connection)
        def disconnect(self):
            pass
    def factory(endpoint):
        endpoints.append(endpoint)
        return Client()
    catalog = ZMQFunctionCatalogService(lambda: OPENHCS_ZMQ_CONFIG,
        client_factory=factory, path_policy=policy(tmp_path))
    if wrong_store:
        with pytest.raises(ValueError, match="no source was dispatched"):
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
    result = FunctionCatalogService(path_policy=policy(tmp_path)).custom_function_registration_destination(
        CustomFunctionRegistrationDestinationRequest(function_name="boundary_probe"))
    assert Path(result.storage_dir) == CustomFunctionManager.default_storage_directory()
    assert Path(result.source_file_path) == CustomFunctionManager.source_path_for_name(Path(result.storage_dir), "boundary_probe")
    assert not (tmp_path / "absent").exists()


def test_local_denial_precedes_manager_evaluation_and_creation(tmp_path, monkeypatch):
    monkeypatch.setenv("XDG_DATA_HOME", str(tmp_path / "foreign"))
    evaluated = []
    monkeypatch.setattr(CustomFunctionManager, "_prepare_source", lambda *args: evaluated.append(args))
    root = CustomFunctionManager.default_storage_directory()
    with pytest.raises(AgentPathPolicyError):
        FunctionCatalogService(path_policy=policy(tmp_path / "owned")).register_custom_function(request(root))
    assert not evaluated
    assert not (tmp_path / "foreign").exists()


def test_public_factory_cannot_expand_write_authority(tmp_path):
    with pytest.raises(TypeError, match="admission_policy"):
        CustomFunctionRegistrationRequest.from_fields(source_code="", admission_policy=policy(tmp_path))
