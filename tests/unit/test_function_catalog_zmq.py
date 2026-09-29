from __future__ import annotations

import ast
import inspect
import textwrap
import threading
import time
from concurrent.futures import CancelledError, Future
from dataclasses import replace

import pytest
from zmqruntime import OperationCancellation
from zmqruntime.client import EndpointConnectionPolicy
from zmqruntime.execution import ExecutionServer
from zmqruntime.messages import ProcessIdentity
from zmqruntime.startup import EndpointStartupPhase, EndpointStartupStatus

from openhcs.agent.dto.execution_connection import ExecutionConnectionSpec
from openhcs.agent.dto.functions import (
    CustomFunctionRegistrationControlResponse,
    CustomFunctionRegistrationDestinationControlResponse,
    CustomFunctionRegistrationDestinationRequest,
    CustomFunctionRegistrationRequest,
    CustomFunctionRegistrationResult,
    FunctionCatalogControlPayload,
    FunctionCatalogControlRequest,
    FunctionCatalogControlRequestABC,
    FunctionCatalogControlResponse,
    FunctionCatalogEntry,
    FunctionCatalogPreparationCancelRequest,
    FunctionCatalogPreparationControlResponse,
    FunctionCatalogPreparationOutcome,
    FunctionCatalogPreparationStartRequest,
    FunctionCatalogPreparationStateControlResponse,
    FunctionCatalogPreparationStatusRequest,
    FunctionDetail,
    FunctionDetailControlRequest,
    FunctionDetailControlResponse,
    FunctionParameterSource,
    FunctionParameterSpec,
    FunctionReferenceControlRequest,
    FunctionReferenceControlResponse,
    FunctionSearchRequest,
    catalog_page,
)
from openhcs.agent.services.function_catalog_service import FunctionCatalogService
from openhcs.core.callable_contract import CallableImportIdentity
from openhcs.core.function_reference import ImportableFunctionReference
from openhcs.runtime.function_catalog_preparation import FunctionCatalogPreparation
from openhcs.runtime.zmq_control import (
    ZMQControlMessageRouter,
    ZMQControlRequestContext,
)
from openhcs.runtime.zmq_execution_client import ZMQExecutionClient
from openhcs.runtime.zmq_execution_server import ZMQExecutionServer


def test_function_parameter_source_owns_runtime_presentation() -> None:
    assert FunctionParameterSource.AGENT.runtime_description is None
    assert "FunctionStep input image payload" in (
        FunctionParameterSource.PRIMARY_INPUT.runtime_description or ""
    )


def test_function_parameter_spec_requires_nominal_source() -> None:
    with pytest.raises(TypeError, match="FunctionParameterSource"):
        FunctionParameterSpec(
            name="image",
            annotation="ndarray",
            default_repr=None,
            required=False,
            supplied_by="runtime_primary_input",  # type: ignore[arg-type]
        )


def test_function_catalog_control_request_requires_declared_message_type() -> None:
    with pytest.raises(TypeError, match="message_type"):

        class MissingMessageType(FunctionCatalogControlRequestABC):
            pass


def test_local_mcp_context_uses_persisted_desktop_execution_endpoint(
    monkeypatch,
) -> None:
    from zmqruntime.config import TransportMode

    from openhcs.agent.services.endpoint_function_catalog_service import (
        ZMQFunctionCatalogService,
    )
    from openhcs.mcp.context import create_agent_context
    from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG

    endpoint_config = replace(
        OPENHCS_ZMQ_CONFIG,
        default_port=18888,
        transport_mode=TransportMode.TCP,
    )
    monkeypatch.setattr(
        "openhcs.pyqt_gui.config.load_cached_ui_execution_endpoint_sync",
        lambda: endpoint_config,
    )

    context = create_agent_context()

    assert isinstance(context.function_catalog, ZMQFunctionCatalogService)
    assert context.function_catalog is context.endpoint_function_catalog
    assert context.function_catalog._config_provider() == endpoint_config
    context.function_catalog.close()


def test_hosted_mcp_context_keeps_self_contained_catalog() -> None:
    from openhcs.mcp.context import create_hosted_agent_context

    context = create_hosted_agent_context()

    assert isinstance(context.function_catalog, FunctionCatalogService)


@pytest.mark.parametrize("construction", ("default_factory", "raw", "injected"))
def test_real_mcp_context_composes_typed_preparation_and_catalog_authority(
    monkeypatch, construction
) -> None:
    import asyncio
    import json

    from openhcs.agent.services.endpoint_function_catalog_service import (
        EndpointFunctionCatalogServiceABC,
        ZMQFunctionCatalogService,
    )
    from openhcs.mcp.context import OpenHCSAgentContext, create_agent_context
    from openhcs.mcp.server import build_server
    from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG
    from openhcs.serialization.json import to_jsonable

    connection = ExecutionConnectionSpec(port=22319)
    endpoint = replace(OPENHCS_ZMQ_CONFIG, default_port=connection.port)
    monkeypatch.setattr(
        "openhcs.pyqt_gui.config.load_cached_ui_execution_endpoint_sync",
        lambda: endpoint,
    )
    preparation = FunctionCatalogPreparation(FunctionCatalogService())
    preparation._future = Future()
    native = ZMQControlRequestContext(
        compiled_artifacts={},
        function_catalog_preparation=preparation,
    )
    observed = []

    class Client:
        def function_catalog_preparation(self, request, *, operation_deadline=None):
            observed.append(request)
            response = ZMQControlMessageRouter.handle(
                FunctionCatalogControlPayload.from_request(request).to_dict(),
                native,
            )
            return FunctionCatalogPreparationStateControlResponse.from_control_response(
                response
            ).value

        def disconnect(self):
            pass

    monkeypatch.setattr(
        ZMQFunctionCatalogService, "_new_client", lambda self, config: Client()
    )
    factories = {
        "default_factory": create_agent_context,
        "raw": OpenHCSAgentContext,
        "injected": lambda: OpenHCSAgentContext(
            endpoint_function_catalog=ZMQFunctionCatalogService(lambda: endpoint),
        ),
    }
    context = factories[construction]()
    assert isinstance(
        context.endpoint_function_catalog, EndpointFunctionCatalogServiceABC
    )
    assert context.function_catalog is context.endpoint_function_catalog

    async def invoke():
        built = build_server(context)
        started = await built.call_tool(
            "openhcs_start_function_catalog_preparation",
            {"port": connection.port},
        )
        content = started[0] if isinstance(started, tuple) else started.content
        payload = json.loads(content[0].text)
        assert not payload["errors"]
        assert payload["outcome"] == "pending"
        arguments = to_jsonable(preparation.start(connection).handle)
        for tool in (
            "openhcs_get_function_catalog_preparation_status",
            "openhcs_cancel_function_catalog_preparation",
        ):
            response = await built.call_tool(tool, arguments)
            content = response[0] if isinstance(response, tuple) else response.content
            assert not json.loads(content[0].text)["errors"]

    try:
        asyncio.run(invoke())
        assert len(observed) == 3
        assert preparation._thread is None
        assert preparation._cancellation.requested()
    finally:
        context.endpoint_function_catalog.close()


def test_gui_application_setup_does_not_initialize_execution_catalog() -> None:
    from openhcs.pyqt_gui.app import OpenHCSPyQtApp

    tree = ast.parse(
        textwrap.dedent(inspect.getsource(OpenHCSPyQtApp.setup_application))
    )
    called_names = {
        node.func.id
        for node in ast.walk(tree)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
    }

    assert "initialize_registry" not in called_names


def _entry(*, function_id: str = "cpu:sample") -> FunctionCatalogEntry:
    return FunctionCatalogEntry(
        function_id=function_id,
        import_path="example.sample",
        name="sample",
        module="example",
        library="cpu",
        signature="sample(image, sigma=1.0)",
        summary="Sample function.",
        backend_tags=("numpy",),
    )


def _catalog(entry: FunctionCatalogEntry | None = None):
    items = (_entry() if entry is None else entry,)
    return catalog_page(
        items=items,
        catalog_items=items,
        total=len(items),
        limit=len(items),
        query=None,
        library=None,
    )


def _detail(entry: FunctionCatalogEntry | None = None) -> FunctionDetail:
    return FunctionDetail(
        schema_version="openhcs.agent.v1",
        entry=_entry() if entry is None else entry,
        parameters=(),
        doc="Sample function.",
    )


def _context(
    preparation_future: Future[None] | None = None,
) -> ZMQControlRequestContext:
    ready = preparation_future or Future()
    if preparation_future is None:
        ready.set_result(None)
    catalog = FunctionCatalogService()
    preparation = FunctionCatalogPreparation(catalog)
    preparation._future = ready
    return ZMQControlRequestContext(
        compiled_artifacts={},
        function_catalog=catalog,
        function_catalog_preparation=preparation,
    )


def test_catalog_revision_is_derived_from_entry_owned_membership_identity() -> None:
    catalog = _catalog()
    presentation_change = _catalog(
        replace(
            _entry(),
            signature="sample(image, sigma: float = 1.0)",
            summary="A longer presentation summary.",
        )
    )
    membership_change = _catalog(replace(_entry(), backend_tags=("cupy",)))

    assert presentation_change.revision == catalog.revision
    assert membership_change.revision != catalog.revision


def test_filtered_catalog_page_retains_complete_endpoint_revision() -> None:
    first = _entry(function_id="cpu:first")
    second = _entry(function_id="cpu:second")
    complete_items = (first, second)
    complete = catalog_page(
        items=complete_items,
        catalog_items=complete_items,
        total=2,
        limit=2,
        query=None,
        library=None,
    )
    filtered = catalog_page(
        items=(first,),
        catalog_items=complete_items,
        total=1,
        limit=1,
        query="first",
        library=None,
    )

    assert filtered.revision == complete.revision


def test_function_catalog_control_payload_roundtrip() -> None:
    request = FunctionCatalogControlRequest(compact_signatures=False)
    payload = FunctionCatalogControlPayload.from_request(request)

    assert (
        FunctionCatalogControlRequest.from_control_payload(payload.to_dict()) is request
    )


def test_function_detail_control_payload_roundtrip() -> None:
    request = FunctionDetailControlRequest(
        function_id="cpu:sample",
        catalog_revision="revision",
        max_doc_chars=123,
        compact_signature=False,
    )
    payload = FunctionCatalogControlPayload.from_request(request)

    assert (
        FunctionDetailControlRequest.from_control_payload(payload.to_dict()) is request
    )


def test_function_search_control_payload_reuses_typed_request() -> None:
    request = FunctionSearchRequest(
        query="segment nuclei",
        library="cpu",
        limit=17,
        compact_signatures=False,
    )
    payload = FunctionCatalogControlPayload.from_request(request)

    assert FunctionSearchRequest.from_control_payload(payload.to_dict()) is request


def test_function_reference_control_payload_roundtrip() -> None:
    request = FunctionReferenceControlRequest(
        function_id="cpu:sample",
        catalog_revision="revision",
    )
    payload = FunctionCatalogControlPayload.from_request(request)

    assert (
        FunctionReferenceControlRequest.from_control_payload(payload.to_dict())
        is request
    )


def test_custom_function_registration_control_payload_roundtrip() -> None:
    request = CustomFunctionRegistrationRequest(
        source_code="@numpy\ndef sample(image):\n    return image\n",
        persist=False,
    )
    payload = FunctionCatalogControlPayload.from_request(request)

    assert (
        CustomFunctionRegistrationRequest.from_control_payload(payload.to_dict())
        is request
    )


def test_zmq_router_reports_catalog_preparation_without_blocking() -> None:
    preparing: Future[None] = Future()

    response = ZMQControlMessageRouter.handle(
        FunctionCatalogControlPayload.from_request(
            FunctionCatalogControlRequest()
        ).to_dict(),
        _context(preparing),
    )

    pending = FunctionCatalogPreparationControlResponse.from_control_response(response)
    assert pending is not None
    assert pending.retry_after_seconds > 0


def test_catalog_client_polls_typed_preparation_response(monkeypatch) -> None:
    pending = FunctionCatalogPreparationControlResponse(
        status=EndpointStartupStatus(
            phase=EndpointStartupPhase.PREPARING_CAPABILITIES,
            message="Discovering functions",
            sequence=1,
            timestamp=1.0,
        ),
        retry_after_seconds=0.25,
    ).to_control_response()
    ready = {"status": "ok", "catalog": _catalog()}
    responses = iter((pending, ready))
    waits: list[float] = []

    class _Cancellation:
        @staticmethod
        def requested() -> bool:
            return False

        @staticmethod
        def wait(timeout: float) -> bool:
            waits.append(timeout)
            return False

    client = ZMQExecutionClient(port=22319, persistent=True)
    monkeypatch.setattr(
        client, "_send_control_request", lambda request: next(responses)
    )
    response = client._send_function_catalog_control_request(
        FunctionCatalogControlPayload.from_request(
            FunctionCatalogControlRequest()
        ).to_dict(),
        cancellation=_Cancellation(),
    )

    assert response is ready
    assert waits == [0.25]


def test_catalog_client_cancellation_prevents_another_poll(monkeypatch) -> None:
    cancellation = OperationCancellation()
    cancellation.cancel()
    client = ZMQExecutionClient(port=22319, persistent=True)
    monkeypatch.setattr(
        client,
        "_send_control_request",
        lambda _request: (_ for _ in ()).throw(
            AssertionError("Cancelled catalog preparation must not poll")
        ),
    )

    with pytest.raises(CancelledError, match="catalog preparation"):
        client._send_function_catalog_control_request(
            FunctionCatalogControlPayload.from_request(
                FunctionCatalogControlRequest()
            ).to_dict(),
            cancellation=cancellation,
        )


@pytest.mark.parametrize("response_kind", ("ready", "pending", "timeout"))
def test_registration_client_sends_mutation_once_even_if_pending_or_uncertain(
    monkeypatch,
    response_kind,
) -> None:
    client = ZMQExecutionClient(port=22319, persistent=True)
    monkeypatch.setattr(client, "is_connected", lambda: True)
    observed = []
    result = CustomFunctionRegistrationResult(schema_version="openhcs.agent.v1")

    def send(payload):
        observed.append(payload)
        if response_kind == "timeout":
            raise TimeoutError("postdispatch observation")
        if response_kind == "pending":
            return FunctionCatalogPreparationControlResponse(
                status=EndpointStartupStatus(
                    phase=EndpointStartupPhase.PREPARING_CAPABILITIES,
                    message="Preparing",
                    sequence=1,
                    timestamp=1.0,
                ),
            ).to_control_response()
        return CustomFunctionRegistrationControlResponse(
            value=result
        ).to_control_response()

    monkeypatch.setattr(client, "_send_control_request", send)
    monkeypatch.setattr(
        client,
        "_send_function_catalog_control_request",
        lambda _payload: pytest.fail("Mutation cannot use the preparation poll loop"),
    )
    request = CustomFunctionRegistrationRequest(
        source_code="not evaluated", persist=False
    )
    if response_kind == "ready":
        assert client.register_custom_function(request) is result
    else:
        with pytest.raises(
            TimeoutError if response_kind == "timeout" else RuntimeError
        ):
            client.register_custom_function(request)
    assert observed == [FunctionCatalogControlPayload.from_request(request).to_dict()]


def test_catalog_client_applies_request_cancellation_to_endpoint_startup(
    monkeypatch,
) -> None:
    cancellation = OperationCancellation()
    page = _catalog()
    observed: dict[str, object] = {}

    class _ConnectionAttempt:
        @staticmethod
        def connect(policy, timeout):
            observed["policy"] = policy
            observed["timeout"] = timeout
            return True

    client = ZMQExecutionClient(port=22319, persistent=True)
    monkeypatch.setattr(client, "is_connected", lambda: False)

    def new_connection_attempt(*, cancellation=None):
        observed["cancellation"] = cancellation
        return _ConnectionAttempt()

    monkeypatch.setattr(client, "new_connection_attempt", new_connection_attempt)
    monkeypatch.setattr(
        client,
        "_send_function_catalog_control_request",
        lambda _request, *, cancellation=None: FunctionCatalogControlResponse(
            page
        ).to_control_response(),
    )

    result = client.get_function_catalog(
        FunctionCatalogControlRequest(),
        cancellation=cancellation,
    )

    assert result is page
    assert observed == {
        "cancellation": cancellation,
        "policy": EndpointConnectionPolicy.ATTACH_OR_START,
        "timeout": client.config.client_connect_timeout_seconds,
    }


def test_zmq_router_projects_catalog_and_revision_checked_detail(monkeypatch) -> None:
    catalog = _catalog()
    detail = _detail()
    monkeypatch.setattr(
        FunctionCatalogService,
        "catalog",
        lambda self, *, compact_signatures=False: catalog,
    )
    monkeypatch.setattr(
        FunctionCatalogService,
        "get",
        lambda self, function_id, **kwargs: detail,
    )

    catalog_response = ZMQControlMessageRouter.handle(
        FunctionCatalogControlPayload.from_request(
            FunctionCatalogControlRequest()
        ).to_dict(),
        _context(),
    )
    projected_catalog = FunctionCatalogControlResponse.from_control_response(
        catalog_response
    ).catalog

    detail_response = ZMQControlMessageRouter.handle(
        FunctionCatalogControlPayload.from_request(
            FunctionDetailControlRequest(
                function_id=detail.entry.function_id,
                catalog_revision=projected_catalog.revision,
            )
        ).to_dict(),
        _context(),
    )

    assert projected_catalog is catalog
    assert (
        FunctionDetailControlResponse.from_control_response(detail_response).detail
        is detail
    )


def test_zmq_router_rejects_detail_from_stale_catalog_revision(monkeypatch) -> None:
    monkeypatch.setattr(
        FunctionCatalogService,
        "catalog",
        lambda self, *, compact_signatures=False: _catalog(),
    )

    response = ZMQControlMessageRouter.handle(
        FunctionCatalogControlPayload.from_request(
            FunctionDetailControlRequest(
                function_id="cpu:sample",
                catalog_revision="stale",
            )
        ).to_dict(),
        _context(),
    )

    assert response["status"] == "error"
    assert "changed after it was read" in response["error"]


def test_zmq_router_transports_revision_checked_function_reference(
    monkeypatch,
) -> None:
    reference = ImportableFunctionReference(
        import_identity=CallableImportIdentity(__name__, "_entry"),
        composite_key=f"python:{__name__}:_entry",
    )
    observed_revisions: list[str] = []
    monkeypatch.setattr(
        FunctionCatalogService,
        "require_revision",
        lambda self, revision: observed_revisions.append(revision),
    )
    monkeypatch.setattr(
        FunctionCatalogService,
        "reference",
        lambda self, function_id: reference,
    )

    response = ZMQControlMessageRouter.handle(
        FunctionCatalogControlPayload.from_request(
            FunctionReferenceControlRequest(
                function_id="cpu:sample",
                catalog_revision="revision",
            )
        ).to_dict(),
        _context(),
    )

    assert (
        FunctionReferenceControlResponse.from_control_response(response).reference
        is reference
    )
    assert observed_revisions == ["revision"]


def test_zmq_router_registers_custom_source_through_catalog_owner(
    monkeypatch,
) -> None:
    request = CustomFunctionRegistrationRequest(
        source_code="@numpy\ndef sample(image):\n    return image\n",
        connection=ExecutionConnectionSpec(port=22319),
        server_identity=ProcessIdentity.current(),
    )
    result = CustomFunctionRegistrationResult(
        schema_version="openhcs.agent.v1",
        registered_count=1,
    )
    observed_requests: list[CustomFunctionRegistrationRequest] = []
    monkeypatch.setattr(
        FunctionCatalogService,
        "register_custom_function",
        lambda self, current_request: (
            observed_requests.append(current_request) or result
        ),
    )

    response = ZMQControlMessageRouter.handle(
        FunctionCatalogControlPayload.from_request(request).to_dict(),
        _context(),
    )

    assert (
        CustomFunctionRegistrationControlResponse.from_control_response(response).result
        is result
    )
    assert observed_requests == [request]


def test_native_registration_destination_bypasses_catalog_preparation(
    tmp_path,
    monkeypatch,
) -> None:
    from zmqruntime.messages import ProcessIdentity

    monkeypatch.setenv("XDG_DATA_HOME", str(tmp_path / "absent"))
    context = _context(Future())

    def reject_preparation():
        raise AssertionError(
            "Destination admission cannot prepare the function catalog"
        )

    monkeypatch.setattr(
        context.function_catalog_preparation, "ensure_started", reject_preparation
    )
    response = ZMQControlMessageRouter.handle(
        FunctionCatalogControlPayload.from_request(
            CustomFunctionRegistrationDestinationRequest(function_name="boundary_probe")
        ).to_dict(),
        context,
    )
    destination = (
        CustomFunctionRegistrationDestinationControlResponse.from_control_response(
            response
        ).destination
    )
    assert destination.server_identity == ProcessIdentity.current()
    assert destination.source_file_path == str(
        tmp_path / "absent" / "openhcs" / "custom_functions" / "boundary_probe.py"
    )
    assert not (tmp_path / "absent").exists()


def test_native_preparation_start_status_cancel_are_responsive_and_incarnation_owned():
    entered = threading.Event()

    class ControlledCatalog:
        def prepare(self, *, status_callback, cancellation):
            status_callback("Controlled preparation remains pending")
            entered.set()
            assert cancellation.wait(2)
            raise CancelledError()

    preparation = FunctionCatalogPreparation(ControlledCatalog())
    context = ZMQControlRequestContext(
        compiled_artifacts={}, function_catalog_preparation=preparation
    )

    def dispatch(request):
        started = time.monotonic()
        response = ZMQControlMessageRouter.handle(
            FunctionCatalogControlPayload.from_request(request).to_dict(), context
        )
        assert time.monotonic() - started < 0.5
        return FunctionCatalogPreparationStateControlResponse.from_control_response(
            response
        ).value

    try:
        connection = ExecutionConnectionSpec(port=22319)
        state = dispatch(FunctionCatalogPreparationStartRequest(connection))
        assert state.outcome is FunctionCatalogPreparationOutcome.PENDING
        assert entered.wait(1)
        future, thread = preparation._future, preparation._thread
        assert (
            dispatch(FunctionCatalogPreparationStartRequest(connection)).handle
            == state.handle
        )
        assert preparation._future is future and preparation._thread is thread
        assert (
            dispatch(FunctionCatalogPreparationStatusRequest(state.handle)).outcome
            is FunctionCatalogPreparationOutcome.PENDING
        )
        stale = replace(
            state.handle,
            server_identity=replace(state.handle.server_identity, create_time=0),
        )
        with pytest.raises(RuntimeError, match="owner changed"):
            preparation.cancel_preparation(stale)
        assert not preparation._cancellation.requested()
        cancelled = dispatch(FunctionCatalogPreparationCancelRequest(state.handle))
        assert cancelled.outcome in (
            FunctionCatalogPreparationOutcome.CANCELLING,
            FunctionCatalogPreparationOutcome.CANCELLED,
        )
        preparation.cancel_and_join()
        assert (
            dispatch(FunctionCatalogPreparationStatusRequest(state.handle)).outcome
            is FunctionCatalogPreparationOutcome.CANCELLED
        )
        assert preparation._future is future and not thread.is_alive()
    finally:
        preparation.cancel_and_join()


def test_native_registration_does_not_start_or_wait_for_cold_preparation(monkeypatch):
    context = ZMQControlRequestContext(
        compiled_artifacts={},
        function_catalog=FunctionCatalogService(),
        function_catalog_preparation=FunctionCatalogPreparation(
            FunctionCatalogService()
        ),
    )
    monkeypatch.setattr(
        context.function_catalog_preparation,
        "ensure_started",
        lambda: pytest.fail("Mutation cannot initiate warmup"),
    )
    monkeypatch.setattr(
        context.function_catalog,
        "register_custom_function",
        lambda _request: pytest.fail("Cold mutation must reject before evaluation"),
    )
    request = CustomFunctionRegistrationRequest(
        source_code="never evaluated",
        persist=False,
        connection=ExecutionConnectionSpec(port=22319),
        server_identity=ProcessIdentity.current(),
    )
    response = ZMQControlMessageRouter.handle(
        FunctionCatalogControlPayload.from_request(request).to_dict(), context
    )
    assert (
        response["status"] == "error"
        and "No source was dispatched" in response["error"]
    )
    assert context.function_catalog_preparation._future is None


def test_zmq_router_delegates_search_to_catalog_owner(monkeypatch) -> None:
    catalog = _catalog()
    observed = []

    def _search(self, **kwargs):
        observed.append(kwargs)
        return catalog

    monkeypatch.setattr(FunctionCatalogService, "search", _search)
    request = FunctionSearchRequest(
        query="sample",
        library="cpu",
        limit=9,
        compact_signatures=True,
    )

    response = ZMQControlMessageRouter.handle(
        FunctionCatalogControlPayload.from_request(request).to_dict(),
        _context(),
    )

    assert (
        FunctionCatalogControlResponse.from_control_response(response).catalog
        is catalog
    )
    assert observed == [
        {
            "query": "sample",
            "library": "cpu",
            "limit": 9,
            "compact_signatures": True,
        }
    ]


def test_execution_server_start_only_binds_endpoint(
    monkeypatch,
) -> None:
    events: list[str] = []
    monkeypatch.setattr(
        FunctionCatalogService,
        "catalog",
        lambda self, *, compact_signatures=False: events.append("catalog"),
    )
    monkeypatch.setattr(
        ExecutionServer,
        "start",
        lambda self: events.append("bind"),
    )

    ZMQExecutionServer().start()

    assert events == ["bind"]


def test_execution_server_runtime_capability_preparation_uses_single_owner(
    monkeypatch,
) -> None:
    events = []
    server = ZMQExecutionServer()
    monkeypatch.setattr(
        server._function_catalog_preparation,
        "wait_until_ready",
        lambda callback=None: events.append(callback),
    )
    callback = object()

    server.prepare_runtime_capabilities(callback)

    assert events == [callback]


def test_execution_server_stop_cancels_catalog_preparation_before_backend_cleanup(
    monkeypatch,
) -> None:
    from openhcs.runtime import zmq_execution_server

    events: list[str] = []
    server = ZMQExecutionServer()
    monkeypatch.setattr(
        ExecutionServer,
        "stop",
        lambda self: events.append("transport"),
    )
    monkeypatch.setattr(
        server._function_catalog_preparation,
        "cancel_and_join",
        lambda: events.append("catalog"),
    )
    monkeypatch.setattr(
        zmq_execution_server,
        "cleanup_backend_connections",
        lambda *, include_process_resources: events.append(
            f"backends:{include_process_resources}"
        ),
    )

    server.stop()

    assert events == ["transport", "catalog", "backends:True"]


def test_function_catalog_preparation_cancellation_reaches_catalog_owner() -> None:
    from openhcs.runtime.function_catalog_preparation import (
        FunctionCatalogPreparation,
    )

    started = threading.Event()

    class CancellableCatalog:
        def prepare(
            self,
            *,
            status_callback,
            cancellation,
        ) -> None:
            del status_callback
            started.set()
            cancellation.wait()
            raise CancelledError

    preparation = FunctionCatalogPreparation(CancellableCatalog())
    future = preparation.ensure_started()
    assert started.wait(timeout=1.0)

    preparation.cancel_and_join()

    assert future.cancelled()


def test_persistent_capability_preparation_uses_registry_owner(
    monkeypatch,
) -> None:
    from openhcs.processing.backends.lib_registry.registry_service import (
        RegistryService,
    )
    from openhcs.runtime.function_catalog_preparation import (
        FunctionCatalogPreparation,
    )

    events: list[str] = []
    monkeypatch.setattr(
        RegistryService,
        "prepare_in_current_process",
        lambda: events.append("prepare"),
    )
    FunctionCatalogPreparation.prepare_persistent_catalog()

    assert events == ["prepare"]


def test_catalog_readiness_waits_for_kernel_preparation_with_cached_metadata(
    monkeypatch,
) -> None:
    """Metadata availability cannot publish readiness ahead of kernel warmup."""

    from openhcs.processing.backends.lib_registry.registry_service import (
        RegistryService,
    )
    from openhcs.runtime.function_catalog_preparation import FunctionCatalogPreparation

    started = threading.Event()
    release = threading.Event()
    events = []
    monkeypatch.setattr(RegistryService, "_metadata_cache", {})

    def prepare(*, status_callback, cancellation):
        assert cancellation is not None
        status_callback("Preparing declared kernels")
        events.append("kernels")
        started.set()
        assert release.wait(timeout=5)

    def catalog(self, *, compact_signatures, status_callback, cancellation):
        assert compact_signatures is True
        events.append("catalog")
        return _catalog()

    monkeypatch.setattr(RegistryService, "prepare_persistent_catalog", prepare)
    monkeypatch.setattr(FunctionCatalogService, "catalog", catalog)
    preparation = FunctionCatalogPreparation(FunctionCatalogService())
    future = preparation.ensure_started()
    try:
        assert started.wait(timeout=1)
        assert preparation.ensure_started() is future
        assert not future.done()
        assert preparation.snapshot().message == "Preparing declared kernels"
    finally:
        release.set()
        preparation.cancel_and_join()
    assert future.result() is None
    assert events == ["kernels", "catalog"]


def test_kernel_preparation_failure_reaches_catalog_future(monkeypatch) -> None:
    from openhcs.processing.backends.lib_registry.registry_service import (
        RegistryService,
    )
    from openhcs.runtime.function_catalog_preparation import FunctionCatalogPreparation

    def fail(**kwargs):
        raise RuntimeError("kernel preparation failed")

    monkeypatch.setattr(RegistryService, "prepare_persistent_catalog", fail)
    preparation = FunctionCatalogPreparation(FunctionCatalogService())
    try:
        with pytest.raises(RuntimeError, match="kernel preparation failed"):
            preparation.wait_until_ready(observation_interval_seconds=0.01)
    finally:
        preparation.cancel_and_join()


def test_endpoint_catalog_reconciles_persisted_custom_function_sources(
    tmp_path,
    monkeypatch,
) -> None:
    """One running catalog reflects external add/delete source mutations."""

    import openhcs.processing.func_registry as func_registry
    from openhcs.processing.backends.lib_registry.registry_service import (
        RegistryService,
    )
    from openhcs.processing.custom_functions.manager import CustomFunctionManager
    from openhcs.processing.custom_functions.runtime_registry import (
        CustomFunctionRuntimeRegistry,
    )

    def registered_custom_metadata(
        cls,
        *,
        status_callback=None,
        cancellation=None,
    ):
        """Project only metadata attached by the real custom-function owner."""

        del cls, status_callback, cancellation
        metadata = CustomFunctionRuntimeRegistry.metadata_by_name().values()
        return {
            function_metadata.composite_key: function_metadata
            for function_metadata in metadata
        }

    with monkeypatch.context() as isolated_catalog:
        isolated_catalog.setenv("OPENHCS_CPU_ONLY", "true")
        isolated_catalog.setenv("XDG_DATA_HOME", str(tmp_path / "data"))
        isolated_catalog.setattr(func_registry, "_registry_initialized", False)
        isolated_catalog.setattr(
            CustomFunctionRuntimeRegistry,
            "_declarations_by_name",
            {},
        )
        isolated_catalog.setattr(
            CustomFunctionRuntimeRegistry,
            "_source_revision",
            None,
        )
        isolated_catalog.setattr(
            RegistryService,
            "get_all_functions_with_metadata",
            classmethod(registered_custom_metadata),
        )

        service = FunctionCatalogService()
        manager = CustomFunctionManager()
        before = {item.name for item in service.catalog().items}
        manager.register_from_code(
            "@numpy\ndef live_catalog_refresh_probe(image):\n    return image\n",
            persist=True,
            emit_signal=False,
        )
        after_add = {item.name for item in service.catalog().items}
        assert "live_catalog_refresh_probe" not in before
        assert "live_catalog_refresh_probe" in after_add
        assert manager.delete_custom_function("live_catalog_refresh_probe")
        after_delete = {item.name for item in service.catalog().items}
        assert "live_catalog_refresh_probe" not in after_delete
