"""Endpoint-owned function catalog service for OpenHCS authoring consumers."""

from __future__ import annotations

import logging
import threading
from abc import abstractmethod
from collections.abc import Callable, Mapping
from concurrent.futures import CancelledError, Future
from dataclasses import dataclass, replace
from types import MappingProxyType
from typing import TYPE_CHECKING

from zmqruntime import OperationCancellation, OperationDeadline

from openhcs.agent.dto.execution_connection import ExecutionConnectionSpec
from openhcs.agent.dto.functions import (
    DEFAULT_FUNCTION_DETAIL_DOC_CHARS,
    CustomFunctionRegistrationDestinationRequest,
    CustomFunctionRegistrationRequest,
    CustomFunctionRegistrationResult,
    FunctionCatalogControlRequest,
    FunctionCatalogEntry,
    FunctionCatalogPage,
    FunctionCatalogPreparationCancelRequest,
    FunctionCatalogPreparationHandle,
    FunctionCatalogPreparationStartRequest,
    FunctionCatalogPreparationState,
    FunctionCatalogPreparationStatusRequest,
    FunctionDetail,
    FunctionDetailControlRequest,
    FunctionReferenceControlRequest,
    FunctionSearchRequest,
)
from openhcs.agent.exceptions import AgentFacingErrorMixin
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.function_catalog_service import FunctionCatalogServiceABC
from openhcs.runtime.zmq_config import OpenHCSZMQConfig

if TYPE_CHECKING:
    from openhcs.core.function_reference import FunctionReference
    from openhcs.runtime.zmq_execution_client import ZMQExecutionClient

logger = logging.getLogger(__name__)


class CustomFunctionRegistrationUncertainError(AgentFacingErrorMixin, RuntimeError):
    agent_error_code = "custom_function_registration_uncertain"
    agent_error_hint = "Preserve this request and endpoint receipt. Do not replay or fall back; persistence may have completed."

    def __init__(self, request: CustomFunctionRegistrationRequest):
        super().__init__(
            f"Registration observation failed after invoking {request.connection.transport_endpoint()}; "
            f"destination={request.storage_dir}, function={request.function_name!r}. "
            f"Selected server={request.server_identity!r}. "
            "Outcome is uncertain; source or registry mutation may have completed."
        )


FunctionCatalogClientFactory = Callable[
    [OpenHCSZMQConfig],
    "ZMQExecutionClient",
]


class EndpointFunctionUnavailableError(RuntimeError):
    """A server function cannot yet be represented by the local editor."""

    def __init__(
        self,
        entry: FunctionCatalogEntry,
        endpoint: OpenHCSZMQConfig,
    ) -> None:
        self.entry = entry
        self.endpoint = endpoint
        super().__init__(
            f"{entry.name!r} is available on the connected execution server "
            f"({endpoint.client_host}:{endpoint.default_port}) but its callable "
            "cannot be materialized by this authoring process."
        )


@dataclass(frozen=True, slots=True)
class FunctionCatalogEndpointRevision:
    """One execution endpoint paired with its catalog membership revision."""

    endpoint: OpenHCSZMQConfig
    revision: str


@dataclass(frozen=True, slots=True)
class FunctionCatalogProjection:
    """One exact catalog snapshot derived from one execution endpoint."""

    endpoint: OpenHCSZMQConfig
    page: FunctionCatalogPage
    compact_signatures: bool
    entries_by_id: Mapping[str, FunctionCatalogEntry]

    @classmethod
    def from_page(
        cls,
        endpoint: OpenHCSZMQConfig,
        page: FunctionCatalogPage,
        *,
        compact_signatures: bool,
    ) -> FunctionCatalogProjection:
        entries_by_id = MappingProxyType(
            {entry.function_id: entry for entry in page.items}
        )
        if len(entries_by_id) != len(page.items):
            raise ValueError(
                "Execution endpoint returned duplicate function identities in one "
                "catalog revision."
            )
        return cls(
            endpoint=endpoint,
            page=page,
            compact_signatures=compact_signatures,
            entries_by_id=entries_by_id,
        )

    @property
    def namespace(self) -> FunctionCatalogEndpointRevision:
        """Complete endpoint configuration plus server-owned catalog revision."""

        return FunctionCatalogEndpointRevision(self.endpoint, self.page.revision)


FunctionCatalogEndpointState = (
    FunctionCatalogEndpointRevision | FunctionCatalogProjection
)


@dataclass(frozen=True, slots=True)
class FunctionCatalogClientSession:
    """One client paired with the exact endpoint used to construct it."""

    endpoint: OpenHCSZMQConfig
    client: ZMQExecutionClient

    def disconnect(self) -> None:
        self.client.disconnect()


class FunctionCatalogPreparation:
    """One cancellable endpoint-catalog read and all of its lifecycle handles."""

    def __init__(
        self,
        endpoint: OpenHCSZMQConfig,
        compact_signatures: bool,
        worker: Callable[[FunctionCatalogPreparation], None],
    ) -> None:
        self.endpoint = endpoint
        self.compact_signatures = compact_signatures
        self.future: Future[FunctionCatalogPage] = Future()
        self.cancellation = OperationCancellation()
        self.thread = threading.Thread(
            target=worker,
            args=(self,),
            name="openhcs-function-catalog-projection",
        )

    def matches(
        self,
        endpoint: OpenHCSZMQConfig,
        compact_signatures: bool,
    ) -> bool:
        """Return whether this operation already owns the requested read."""

        return (
            self.endpoint == endpoint and self.compact_signatures == compact_signatures
        )

    def cancel_and_join(self) -> None:
        """Stop this operation and wait for its client-owning worker."""

        self.cancellation.cancel()
        if self.thread is not threading.current_thread():
            self.thread.join()


class EndpointFunctionCatalogServiceABC(FunctionCatalogServiceABC):
    """Endpoint catalog with responsive access to its native preparation owner."""

    @abstractmethod
    def start_catalog_preparation(
        self, connection: ExecutionConnectionSpec
    ) -> FunctionCatalogPreparationState:
        """Start/coalesce the selected endpoint's existing preparation future."""

    @abstractmethod
    def catalog_preparation_status(
        self, handle: FunctionCatalogPreparationHandle
    ) -> FunctionCatalogPreparationState:
        """Observe the exact native incarnation without starting or waiting."""

    @abstractmethod
    def cancel_catalog_preparation(
        self, handle: FunctionCatalogPreparationHandle
    ) -> FunctionCatalogPreparationState:
        """Signal the exact native preparation owner without joining its child."""


class ZMQFunctionCatalogService(EndpointFunctionCatalogServiceABC):
    """Use one execution endpoint as the authoring callable-catalog authority."""

    def __init__(
        self,
        config_provider: Callable[[], OpenHCSZMQConfig],
        *,
        client_factory: FunctionCatalogClientFactory | None = None,
        path_policy: AgentPathPolicy | None = None,
    ) -> None:
        self._config_provider = config_provider
        self._path_policy = path_policy or AgentPathPolicy.from_environment()
        self._client_factory = client_factory or self._new_client
        self._client_session: FunctionCatalogClientSession | None = None
        self._endpoint_state: FunctionCatalogEndpointState | None = None
        self._preparation: FunctionCatalogPreparation | None = None
        self._closed = False
        self._state_lock = threading.RLock()

    def _new_client(self, config: OpenHCSZMQConfig) -> ZMQExecutionClient:
        from openhcs.runtime.zmq_execution_client import ZMQExecutionClient

        return ZMQExecutionClient(config=config)

    @property
    def projection(self) -> FunctionCatalogProjection | None:
        with self._state_lock:
            state = self._endpoint_state
        return state if isinstance(state, FunctionCatalogProjection) else None

    def prepare(
        self,
        *,
        compact_signatures: bool = True,
    ) -> Future[FunctionCatalogPage]:
        """Read the endpoint's current catalog, coalescing concurrent callers.

        A completed projection proves its contents, not that the endpoint still
        has the same revision. Other authoring processes can register functions
        without emitting an event in this process. Registry discovery remains
        cached by the endpoint; consumers request a fresh projection here.
        """

        endpoint = self._config_provider()
        self._cancel_mismatched_preparation(endpoint, compact_signatures)
        with self._state_lock:
            if self._closed:
                raise RuntimeError("Function catalog projection is closed")
            if self._preparation is not None and self._preparation.matches(
                endpoint,
                compact_signatures,
            ):
                return self._preparation.future

            preparation = FunctionCatalogPreparation(
                endpoint,
                compact_signatures,
                self._prepare_catalog,
            )
            self._preparation = preparation
            preparation.thread.start()
        return preparation.future

    def catalog(
        self,
        *,
        compact_signatures: bool = True,
        status_callback: Callable[[str], None] | None = None,
        cancellation: OperationCancellation | None = None,
    ) -> FunctionCatalogPage:
        self._cancel_preparation()
        endpoint = self._config_provider()
        if status_callback is not None:
            status_callback("Requesting the execution endpoint function catalog")
        page = self._client_for(endpoint).get_function_catalog(
            FunctionCatalogControlRequest(
                compact_signatures=compact_signatures,
            ),
            cancellation=cancellation,
        )
        with self._state_lock:
            self._endpoint_state = FunctionCatalogProjection.from_page(
                endpoint,
                page,
                compact_signatures=compact_signatures,
            )
        if status_callback is not None:
            status_callback(f"Function catalog ready ({page.total} functions)")
        return page

    def search(
        self,
        *,
        query: str | None = None,
        library: str | None = None,
        limit: int = 50,
        compact_signatures: bool = True,
    ) -> FunctionCatalogPage:
        endpoint = self._config_provider()
        page = self._client_for(endpoint).search_function_catalog(
            FunctionSearchRequest(
                query=query,
                library=library,
                limit=limit,
                compact_signatures=compact_signatures,
            )
        )
        with self._state_lock:
            state = self._endpoint_state
            if (
                state is None
                or state.endpoint != endpoint
                or self._state_revision(state) != page.revision
            ):
                self._endpoint_state = FunctionCatalogEndpointRevision(
                    endpoint,
                    page.revision,
                )
        return page

    def get(
        self,
        function_id: str,
        *,
        max_doc_chars: int | None = DEFAULT_FUNCTION_DETAIL_DOC_CHARS,
        compact_signature: bool = True,
    ) -> FunctionDetail:
        endpoint_revision = self._require_endpoint_revision()
        return self._client_for(endpoint_revision.endpoint).get_function_detail(
            FunctionDetailControlRequest(
                function_id=function_id,
                catalog_revision=endpoint_revision.revision,
                max_doc_chars=max_doc_chars,
                compact_signature=compact_signature,
            )
        )

    def get_by_import_path(
        self,
        import_path: str,
        *,
        max_doc_chars: int | None = DEFAULT_FUNCTION_DETAIL_DOC_CHARS,
        compact_signature: bool = True,
    ) -> FunctionDetail | None:
        requested_import_path = import_path.strip()
        if not requested_import_path:
            return None
        page = self.search(
            query=requested_import_path,
            limit=50,
            compact_signatures=True,
        )
        entry = next(
            (item for item in page.items if item.import_path == requested_import_path),
            None,
        )
        if entry is None:
            return None
        return self.get(
            entry.function_id,
            max_doc_chars=max_doc_chars,
            compact_signature=compact_signature,
        )

    def resolve(self, function_id: str) -> Callable:
        """Resolve only the selected endpoint reference in this process."""

        endpoint_revision = self._require_endpoint_revision()
        entry = self._entry(function_id)
        try:
            return self.reference(function_id).resolve()
        except (ImportError, RuntimeError, TypeError) as exc:
            raise EndpointFunctionUnavailableError(
                entry,
                endpoint_revision.endpoint,
            ) from exc

    def reference(self, function_id: str) -> FunctionReference:
        """Transport the endpoint-owned contract without loading its library here."""

        endpoint_revision = self._require_endpoint_revision()
        return self._client_for(endpoint_revision.endpoint).get_function_reference(
            FunctionReferenceControlRequest(
                function_id=function_id,
                catalog_revision=endpoint_revision.revision,
            )
        )

    def register_custom_function(
        self,
        request: CustomFunctionRegistrationRequest,
    ) -> CustomFunctionRegistrationResult:
        """Register source at the endpoint and project ephemeral source locally."""

        request = request.admitted(self._path_policy)
        endpoint = self._endpoint_for_connection(request.connection)
        deadline = OperationDeadline.after_milliseconds(
            endpoint.control_timeout_ms,
            operation="custom function registration",
        )
        client = self._client_for(endpoint)
        destination = client.custom_function_registration_destination(
            CustomFunctionRegistrationDestinationRequest(
                function_name=request.function_name
            ),
            operation_deadline=deadline,
        )
        destination.require_request(request)
        if request.persist:
            self._path_policy.assert_writable(destination.storage_dir)
            self._path_policy.assert_writable(destination.source_file_path)
        request = replace(request, server_identity=destination.server_identity)
        self.invalidate()
        self._config_provider = lambda: endpoint
        # Observe the existing future once, never inline-poll a cold warmup.
        handle = FunctionCatalogPreparationHandle(
            request.connection, destination.server_identity
        )
        state = client.function_catalog_preparation(
            FunctionCatalogPreparationStatusRequest(handle),
            operation_deadline=deadline,
        )
        state.require_handle(handle)
        state.require_ready()
        deadline.remaining_seconds()
        try:
            result = client.register_custom_function(
                request, operation_deadline=deadline
            )
            destination.require_result(request, result)
            if not request.persist:
                from openhcs.processing.custom_functions.manager import (
                    CustomFunctionManager,
                )

                CustomFunctionManager(create_storage=False).register_from_code(
                    request.source_code,
                    persist=False,
                    clear_caches=False,
                    emit_signal=False,
                )
            self.invalidate()
        except Exception as error:
            raise CustomFunctionRegistrationUncertainError(request) from error
        return result

    def _endpoint_for_connection(
        self, connection: ExecutionConnectionSpec
    ) -> OpenHCSZMQConfig:
        """Use the explicit typed route, never a companion endpoint registry."""
        return replace(
            self._config_provider(),
            default_port=connection.require_port("Function catalog operation"),
            client_host=connection.host,
            transport_mode=connection.transport_endpoint().transport_mode,
            persistent=connection.persistent,
        )

    def start_catalog_preparation(
        self, connection: ExecutionConnectionSpec
    ) -> FunctionCatalogPreparationState:
        endpoint = self._endpoint_for_connection(connection)
        state = self._client_for(endpoint).function_catalog_preparation(
            FunctionCatalogPreparationStartRequest(connection),
        )
        if state.handle.connection != connection:
            raise RuntimeError(
                "Catalog preparation response changed the explicit connection."
            )
        self.invalidate()
        self._config_provider = lambda: endpoint
        return state

    def catalog_preparation_status(
        self, handle: FunctionCatalogPreparationHandle
    ) -> FunctionCatalogPreparationState:
        state = self._client_for(
            self._endpoint_for_connection(handle.connection)
        ).function_catalog_preparation(
            FunctionCatalogPreparationStatusRequest(handle),
        )
        state.require_handle(handle)
        return state

    def cancel_catalog_preparation(
        self, handle: FunctionCatalogPreparationHandle
    ) -> FunctionCatalogPreparationState:
        state = self._client_for(
            self._endpoint_for_connection(handle.connection)
        ).function_catalog_preparation(
            FunctionCatalogPreparationCancelRequest(handle),
        )
        state.require_handle(handle)
        return state

    def invalidate(self) -> None:
        """Discard the derived page; the next read requests the endpoint again."""

        self._cancel_preparation()
        with self._state_lock:
            self._endpoint_state = None

    def close(self) -> None:
        with self._state_lock:
            if self._closed:
                return
            self._closed = True
        self._cancel_preparation()
        if self._client_session is not None:
            try:
                self._client_session.disconnect()
            finally:
                self._client_session = None
        with self._state_lock:
            self._endpoint_state = None

    def _require_endpoint_revision(self) -> FunctionCatalogEndpointRevision:
        endpoint = self._config_provider()
        with self._state_lock:
            state = self._endpoint_state
        if state is None or state.endpoint != endpoint:
            self.catalog()
            with self._state_lock:
                state = self._endpoint_state
        if state is None:
            raise RuntimeError("Function catalog endpoint returned no revision.")
        if isinstance(state, FunctionCatalogProjection):
            return state.namespace
        return state

    @staticmethod
    def _state_revision(state: FunctionCatalogEndpointState) -> str:
        if isinstance(state, FunctionCatalogProjection):
            return state.page.revision
        return state.revision

    def _entry(self, function_id: str) -> FunctionCatalogEntry:
        projection = self.projection
        if projection is not None:
            entry = projection.entries_by_id.get(function_id)
            if entry is not None:
                return entry
        return self.get(
            function_id,
            max_doc_chars=0,
            compact_signature=True,
        ).entry

    def _prepare_catalog(
        self,
        preparation: FunctionCatalogPreparation,
    ) -> None:
        """Read one catalog on its client-owning worker thread."""

        if not preparation.future.set_running_or_notify_cancel():
            return
        client: ZMQExecutionClient | None = None
        try:
            client = self._client_factory(preparation.endpoint)
            page = client.get_function_catalog(
                FunctionCatalogControlRequest(
                    compact_signatures=preparation.compact_signatures,
                ),
                cancellation=preparation.cancellation,
            )
            projection = FunctionCatalogProjection.from_page(
                preparation.endpoint,
                page,
                compact_signatures=preparation.compact_signatures,
            )
            with self._state_lock:
                if self._preparation is preparation:
                    self._endpoint_state = projection
                    self._preparation = None
            preparation.future.set_result(page)
        except CancelledError as error:
            preparation.future.set_exception(error)
        except Exception as error:
            with self._state_lock:
                if self._preparation is preparation:
                    self._preparation = None
            preparation.future.set_exception(error)
        finally:
            if client is not None:
                try:
                    client.disconnect()
                except Exception:
                    logger.exception("Failed to disconnect function catalog client")
            with self._state_lock:
                if self._preparation is preparation:
                    self._preparation = None

    def _cancel_preparation(self) -> None:
        """Cancel and join the exact endpoint-catalog worker owned by this service."""

        with self._state_lock:
            preparation = self._preparation
            self._preparation = None
        if preparation is None:
            return
        preparation.cancel_and_join()

    def _cancel_mismatched_preparation(
        self,
        endpoint: OpenHCSZMQConfig,
        compact_signatures: bool,
    ) -> None:
        """Cancel an active read only when it cannot satisfy this request."""

        with self._state_lock:
            preparation = self._preparation
            if preparation is None or preparation.matches(
                endpoint,
                compact_signatures,
            ):
                return
            self._preparation = None
        preparation.cancel_and_join()

    def _client_for(self, endpoint: OpenHCSZMQConfig) -> ZMQExecutionClient:
        if self._client_session is not None:
            if self._client_session.endpoint == endpoint:
                return self._client_session.client
            self._client_session.disconnect()
        self._client_session = FunctionCatalogClientSession(
            endpoint,
            self._client_factory(endpoint),
        )
        with self._state_lock:
            if (
                self._endpoint_state is not None
                and self._endpoint_state.endpoint != endpoint
            ):
                self._endpoint_state = None
        return self._client_session.client
