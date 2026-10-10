"""The OpenHCS session: every client's datasets, pipelines and executions.

Durable authoring state (the dataset list, each dataset's PipelineConfig and
pipeline steps) lives in ObjectState. Runtime state (pending work, compiled
artifacts, the execution batch, debug sessions, the runtime projection) lives
here and is reset with the session. Clients call :meth:`Session.invoke`,
read :meth:`Session.view` and follow :meth:`Session.events_after` or
:meth:`Session.subscribe`; none of them keeps a copy.
"""

from __future__ import annotations

import asyncio
import inspect
import logging
import time
from abc import ABC, abstractmethod
from dataclasses import dataclass
from collections.abc import Callable, Iterable
from pathlib import Path
from typing import TYPE_CHECKING, TypeVar

from objectstate.lazy_factory import ensure_global_config_context
from objectstate.object_state import ObjectState, ObjectStateRegistry
from polystore.base import _create_storage_registry
from pyqt_reactive.services.async_operation_executor import AsyncOperationExecutor
from pyqt_reactive.services.scope_token_service import ScopeTokenService
from pyqt_reactive.services.zmq_server_scan_service import EndpointObservationSnapshot
from zmqruntime.messages import ExecutionRecord
from zmqruntime.startup import EndpointStartupPhase, EndpointStartupStatus

from openhcs.authoring.session.compile_batch import CompileBatch
from openhcs.authoring.session.compilation import CompiledDataset
from openhcs.authoring.session.datasets import (
    DatasetRow,
    dataset_list_state,
    dataset_scope_ids,
    write_dataset_scope_ids,
)
from openhcs.authoring.session.debug_runs import DebugRunRequest, DebugRuns
from openhcs.authoring.session.events import (
    AvailabilityChanged,
    BatchFinished,
    CompiledStateChanged,
    DatasetConfigChanged,
    DatasetExecutionFinished,
    DatasetRunning,
    DatasetsChanged,
    DatasetStateChanged,
    DebugSnapshotAvailable,
    ErrorReported,
    ExecutionStateChanged,
    GlobalConfigChanged,
    InitializationFailed,
    LogsCleared,
    PipelineChanged,
    PipelineImported,
    ProgressAdvanced,
    ProgressFinished,
    ProgressStarted,
    RuntimeProjectionChanged,
    SelectionChanged,
    ServerCompatibilityObserved,
    ServerConnectionChanged,
    SessionEvent,
    SessionEventLog,
    SessionEventRecord,
    StatusReported,
)
from openhcs.authoring.session.execution_batch import ExecutionBatchRuntime
from openhcs.authoring.session.execution_client import ZMQClientService
from openhcs.authoring.session.execution_control import ExecutionControl
from openhcs.authoring.session.live_measurements import LiveMeasurementTable
from openhcs.authoring.session.pipelines import PipelineObjectStateBinding
from openhcs.authoring.session.progress import ExecutionProgress
from openhcs.authoring.session.result_summaries import consolidate_batch_results
from openhcs.authoring.session.progress_notifications import (
    DebugSnapshotAvailableNotification,
)
from openhcs.authoring.session.run_requests import dataset_pipeline_request
from openhcs.authoring.session.submission import (
    ExecutionSubmission,
    SubmittedExecution,
)
from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
from openhcs.core.dataset_sources.dataset_roots import (
    DatasetRootRule,
    LocalDirectoryRoot,
)
from openhcs.core.dataset_sources.dataset_scopes import (
    DatasetScope,
    DatasetScopeKind,
)
from openhcs.core.dataset_sources.source import (
    PreparedWorkspaceSource,
    SourceSelectionRole,
)
from openhcs.core.debug import (
    DebugCommandType,
    DebugReplayMode,
    DebugSession,
    DebugSnapshot,
    DebugTerminalSummary,
)
from openhcs.core.debug_session_projection import (
    DebugPauseBoundaryState,
    DebugSessionProjectionContext,
    DebugSessionTargetState,
)
from openhcs.core.execution_state import (
    ExecutionCompletionPayload,
    ManagerExecutionState,
)
from openhcs.core.input_workspace import InputWorkspacePreparationResult
from openhcs.core.pipeline_document import PipelineDocument, PipelineDocumentCodec
from openhcs.core.pipeline_import import PipelineImporter
from openhcs.core.orchestrator.orchestrator import (
    OrchestratorState,
    PipelineOrchestrator,
)
from openhcs.core.progress import registry
from openhcs.core.progress.debug_projection import (
    DebugRuntimeProjection,
    RuntimeProjectionBundle,
)
from openhcs.core.progress.projection import ExecutionRuntimeProjection
from openhcs.core.steps.function_step import FunctionStep
from openhcs.runtime.zmq_config import OpenHCSZMQConfig
from openhcs.runtime.zmq_execution_signature import (
    ZMQAuxiliaryExecutionParams,
    ZMQRuntimeObservationExportScope,
)
from openhcs.ui.shared.plate_scope_identity import PipelineScopeIdentity

if TYPE_CHECKING:
    from openhcs.agent.dto.common import AgentError
    from openhcs.authoring.session.operations import SessionOperation
    from openhcs.authoring.session.views import SessionView
    from zmqruntime.messages import PongResponse

    from openhcs.runtime.zmq_execution_client import (
        ZMQExecutionClient,
        ZMQExecutionRequestBuilder,
    )

logger = logging.getLogger(__name__)
ResultT = TypeVar("ResultT")


# ---------------------------------------------------------------------------
# Ports a client supplies
# ---------------------------------------------------------------------------


class MainThread(ABC):
    """Where session work that touches ObjectState runs."""

    @abstractmethod
    def post(self, callback: Callable[[], None]) -> None: ...

    @abstractmethod
    def call(self, callback: Callable[[], ResultT]) -> ResultT: ...


class CallerThread(MainThread):
    """Run session work on the calling thread (a process with one owner thread)."""

    def post(self, callback: Callable[[], None]) -> None:
        callback()

    def call(self, callback: Callable[[], ResultT]) -> ResultT:
        return callback()


class DispatcherThread(MainThread):
    """Run session work through a UI-thread dispatcher (``post``/``call``)."""

    def __init__(self, dispatcher) -> None:
        self._dispatcher = dispatcher

    def post(self, callback: Callable[[], None]) -> None:
        self._dispatcher.post(callback)

    def call(self, callback: Callable[[], ResultT]) -> ResultT:
        return self._dispatcher.call(callback)


class DatasetAccess(ABC):
    """Which dataset roots this session may read and initialize."""

    @abstractmethod
    def require_readable(self, root: Path) -> Path: ...

    @abstractmethod
    def require_initializable(self, root: Path) -> Path:
        """Initialization writes dataset metadata next to the data."""

    @abstractmethod
    def require_writable(self, path: Path) -> Path: ...


class UnrestrictedDatasetAccess(DatasetAccess):
    """A desktop session reads and writes wherever its user can."""

    def require_readable(self, root: Path) -> Path:
        return root

    def require_initializable(self, root: Path) -> Path:
        return root

    def require_writable(self, path: Path) -> Path:
        return path


class Renderer(ABC):
    """What presents renderer operations (windows, dialogs, editors)."""

    @abstractmethod
    def presents(self, operation: type["SessionOperation"]) -> bool: ...

    @abstractmethod
    def present(self, operation: type["SessionOperation"], request: object) -> None: ...

    def unavailable_reason(
        self,
        operation: type["SessionOperation"],
        request: object,
    ) -> "AgentError | None":
        """Why the renderer cannot present ``operation`` now (default: it can)."""

        del operation, request
        return None

    @abstractmethod
    def prompt(self, operation: type["SessionOperation"]) -> object | None:
        """Ask the user for a prompted operation's request (``None``: cancelled)."""


class NoRenderer(Renderer):
    """A headless session presents nothing."""

    def presents(self, operation: type["SessionOperation"]) -> bool:
        del operation
        return False

    def present(self, operation: type["SessionOperation"], request: object) -> None:
        raise RuntimeError(f"{operation.__name__} needs a renderer; none is attached.")

    def prompt(self, operation: type["SessionOperation"]) -> object | None:
        raise RuntimeError(f"{operation.__name__} needs a renderer to prompt for it.")


# ---------------------------------------------------------------------------
# The session
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class FinishedExecution:
    """One ordinary execution: what was submitted and the server's record of it."""

    scope_id: str
    request: "ZMQExecutionRequestBuilder"
    record: ExecutionRecord
    endpoint: "PongResponse | None"


class Session:
    """Datasets, their pipelines and executions, and the events they emit."""

    def __init__(
        self,
        *,
        transport_config: OpenHCSZMQConfig,
        global_config: GlobalPipelineConfig,
        main_thread: MainThread,
        progress_interval_seconds: float = 1 / 30,
        dataset_access: DatasetAccess = UnrestrictedDatasetAccess(),
    ) -> None:
        self.main_thread = main_thread
        self.dataset_access = dataset_access
        self.renderer: Renderer = NoRenderer()
        self.event_log = SessionEventLog()
        self.global_config = global_config
        self.client = ZMQClientService(
            config=transport_config,
            status_callback=lambda status: self.publish(ServerConnectionChanged(status)),
            compatibility_callback=lambda compatibility: self.publish(
                ServerCompatibilityObserved(compatibility)
            ),
        )
        self._endpoint_status: Callable[[], EndpointStartupStatus] = (
            self._client_endpoint_status
        )

        self.selected_scope_ids: tuple[str, ...] = ()
        self.current_scope_id = ""
        self.compiled: dict[str, CompiledDataset] = {}
        self.init_pending: set[str] = set()
        self.compile_pending: set[str] = set()
        self._execution_state = ManagerExecutionState.IDLE
        self.batch = ExecutionBatchRuntime()
        self.progress_tracker = registry()
        self.debug_sessions: dict[str, DebugSession] = {}
        self.debug_snapshots: dict[str, tuple[DebugSnapshot, ...]] = {}
        self.debug_terminal_summaries: dict[str, DebugTerminalSummary] = {}
        self.inspected_debug_sessions: dict[str, DebugSession] = {}
        """Debug sessions a client loaded from snapshots without running them."""
        self.runtime_projection = ExecutionRuntimeProjection()
        self.debug_runtime_projection = DebugRuntimeProjection.empty(
            self.runtime_projection
        )
        self.live_measurements = LiveMeasurementTable()
        self.submitted_executions: dict[str, SubmittedExecution] = {}
        self.finished_executions: dict[str, FinishedExecution] = {}

        self.compile_batch = CompileBatch(self)
        self.submission = ExecutionSubmission(self)
        self.execution_control = ExecutionControl(self)
        self.debug_runs = DebugRuns(self)
        self.progress = ExecutionProgress(self, interval_seconds=progress_interval_seconds)
        self._work = AsyncOperationExecutor()
        self._closed = False

        dataset_list_state()
        self._split_dataset_scopes()

    # -- events ---------------------------------------------------------------

    def publish(self, event: SessionEvent) -> SessionEventRecord:
        return self.event_log.publish(event)

    def subscribe(self, listener: Callable[[SessionEventRecord], None]) -> Callable[[], None]:
        return self.event_log.subscribe(listener)

    def events_after(
        self, sequence: int, *, timeout_seconds: float = 0.0
    ) -> tuple[SessionEventRecord, ...]:
        return self.event_log.after(sequence, timeout_seconds=timeout_seconds)

    def refresh(self) -> None:
        self.publish(DatasetsChanged())
        self.publish(AvailabilityChanged())

    # -- operations and views -------------------------------------------------

    def invoke(self, operation: type["SessionOperation"], request: object):
        """Run one operation (after its availability check) and return its result."""

        return operation.invoke(self, request)

    def view(self, view: type["SessionView"], *args, **kwargs):
        return view.state_of(self, *args, **kwargs)

    def attach_renderer(self, renderer: Renderer) -> None:
        self.renderer = renderer

    def start(self, work: Callable[..., object], *args, **kwargs):
        """Run one coroutine function on the session's worker pool."""

        future = self._work.submit(work, *args, **kwargs)

        def report_failure(completed) -> None:
            if completed.cancelled():
                return
            error = completed.exception()
            if error is not None:
                logger.error("Session work failed: %s", error, exc_info=error)
                self.publish(ErrorReported(str(error)))

        future.add_done_callback(report_failure)
        return future

    def close(self) -> None:
        if self._closed:
            return
        self._closed = True
        self.progress.close()
        self._work.close()
        self.execution_control.disconnect()

    # -- configuration --------------------------------------------------------

    def set_transport_config(self, config: OpenHCSZMQConfig) -> None:
        self.client.set_config(config)

    def bind_endpoint_observations(
        self, provider: Callable[[], EndpointObservationSnapshot]
    ) -> None:
        """Read endpoint readiness from a shared observer (the server browser)."""

        self._endpoint_status = lambda: provider().status_for_port(
            self.client.config.default_port
        )
        self.publish(AvailabilityChanged())

    def endpoint_status(self) -> EndpointStartupStatus:
        return self._endpoint_status()

    def _client_endpoint_status(self) -> EndpointStartupStatus:
        if self.client.has_client():
            return EndpointStartupStatus(
                phase=EndpointStartupPhase.CONNECTED, message="Connected"
            )
        return EndpointStartupStatus(
            phase=EndpointStartupPhase.DISCONNECTED, message="Not connected"
        )

    def adopt_global_config(self, config: GlobalPipelineConfig) -> None:
        """A saved global config: every dataset now resolves against it."""

        self.global_config = config
        ensure_global_config_context(GlobalPipelineConfig, config)
        for scope_id in dataset_scope_ids():
            orchestrator = ObjectStateRegistry.get_object(scope_id)
            if orchestrator is not None:
                self.publish(
                    DatasetConfigChanged(scope_id, orchestrator.get_effective_config())
                )

    def apply_global_config(self, config: GlobalPipelineConfig) -> None:
        """Write ``config`` into the global ObjectState and adopt it."""

        self.require_definition_mutation_allowed()
        global_state = ObjectStateRegistry.get_by_scope("")
        if global_state is not None:
            global_state.update_object_instance(config)
        self.adopt_global_config(config)
        self.publish(GlobalConfigChanged(config))

    def apply_dataset_configs(self, configs: dict[str, PipelineConfig]) -> None:
        for scope_id in configs:
            self.require_definition_mutation_allowed(scope_id)
        for scope_id, config in configs.items():
            orchestrator = self.orchestrator(scope_id)
            orchestrator.apply_pipeline_config(config)
            state = ObjectStateRegistry.get_by_scope(scope_id)
            if state is None or not isinstance(state.saved_object, PipelineConfig):
                raise RuntimeError(
                    "A dataset PipelineConfig update needs the dataset's ObjectState "
                    f"delegated to a PipelineConfig; scope {scope_id!r} has none."
                )
            state.update_object_instance(config)
            self.publish(
                DatasetConfigChanged(scope_id, orchestrator.get_effective_config())
            )

    # -- datasets -------------------------------------------------------------

    def dataset_scope_ids(self) -> list[str]:
        return dataset_scope_ids()

    def dataset_rows(self) -> list[DatasetRow]:
        return [DatasetRow.of(scope_id) for scope_id in dataset_scope_ids()]

    def dataset_name(self, scope_id: str) -> str:
        return DatasetScope.parse(scope_id).display_name

    def orchestrator(self, scope_id: str) -> PipelineOrchestrator:
        orchestrator = ObjectStateRegistry.get_object(scope_id)
        if not isinstance(orchestrator, PipelineOrchestrator):
            raise RuntimeError(f"Dataset {scope_id!r} has no orchestrator.")
        return orchestrator

    def is_initialized(self, scope_id: str) -> bool:
        orchestrator = ObjectStateRegistry.get_object(scope_id)
        return (
            isinstance(orchestrator, PipelineOrchestrator)
            and orchestrator.state.has_completed_initialization
        )

    def add_dataset_roots(self, roots: Iterable[Path | str]) -> tuple[str, ...]:
        """Add one row per scope each root offers; return the added scope ids."""

        offers = tuple(
            offer
            for root in roots
            for offer in DatasetScopeKind.offers_for_root(
                self.dataset_access.require_readable(Path(root))
            )
        )
        added = self._add_scopes(
            tuple(offer.scope for offer in offers),
            label="add datasets",
        )
        if not added:
            self.publish(StatusReported("No new datasets added (duplicates skipped)"))
            return ()
        preferred = next(
            (
                offer.scope.scope_id
                for offer in offers
                if offer.select_by_default and offer.scope.scope_id in added
            ),
            added[-1],
        )
        self.select((preferred,))
        self.publish(
            StatusReported(
                f"Added {len(added)} dataset(s): "
                + ", ".join(self.dataset_name(scope_id) for scope_id in added)
            )
        )
        return added

    def ensure_datasets(self, scope_ids: Iterable[str]) -> tuple[str, ...]:
        """Register every scope id not yet in the list; return those added."""

        added = self._add_scopes(
            tuple(DatasetScope.parse(str(scope_id)) for scope_id in scope_ids),
            label="register orchestrators",
        )
        if added:
            self.publish(StatusReported(f"Added {len(added)} dataset(s) from code"))
        return added

    def _add_scopes(
        self,
        scopes: tuple[DatasetScope, ...],
        *,
        label: str,
        source_role: type[SourceSelectionRole] | None = None,
    ) -> tuple[str, ...]:
        current = dataset_scope_ids()
        added: list[str] = []
        for scope in scopes:
            if scope.scope_id in current or scope.scope_id in added:
                continue
            self._create_orchestrator(scope, source_role=source_role)
            added.append(scope.scope_id)
        if added:
            with ObjectStateRegistry.atomic(label):
                write_dataset_scope_ids([*current, *added])
            self.refresh()
        return tuple(added)

    def _create_orchestrator(
        self,
        scope: DatasetScope,
        *,
        source_role: type[SourceSelectionRole] | None = None,
    ) -> ObjectState:
        existing = ObjectStateRegistry.get_by_scope(scope.scope_id)
        if existing is not None:
            return existing
        orchestrator = PipelineOrchestrator(
            plate_path=scope.root,
            storage_registry=_create_storage_registry(),
            selected_pipeline_path=scope.pipeline_path,
            transport_config=self.client.config,
        )
        if source_role is not None:
            orchestrator.apply_pipeline_config(
                source_role.pipeline_config_for_source(orchestrator.pipeline_config)
            )
        state = ObjectState(
            object_instance=orchestrator,
            scope_id=scope.scope_id,
            parent_state=ObjectStateRegistry.get_by_scope(""),
        )
        ObjectStateRegistry.register(state)
        self.publish(DatasetStateChanged(scope.scope_id, OrchestratorState.CREATED))
        return state

    def _split_dataset_scopes(self) -> None:
        """Expand persisted plain roots that a registered kind now splits into rows."""

        scope_ids = tuple(dataset_scope_ids())
        expanded: list[str] = []
        created: list[DatasetScope] = []
        for scope_id in scope_ids:
            scope = DatasetScope.parse(scope_id)
            offers = (
                DatasetScopeKind.offers_for_root(scope.root)
                if scope.scope_id == str(scope.root)
                else ()
            )
            targets = tuple(offer.scope for offer in offers) or (scope,)
            if any(target.scope_id != scope_id for target in targets):
                created.extend(targets)
            for target in targets:
                if target.scope_id not in expanded:
                    expanded.append(target.scope_id)
        if tuple(expanded) == scope_ids:
            return
        with ObjectStateRegistry.atomic("split dataset scopes"):
            for scope in created:
                self._create_orchestrator(scope)
            write_dataset_scope_ids(expanded)
        logger.info("Split dataset scopes: %s -> %s", list(scope_ids), expanded)

    def delete_datasets(self, scope_ids: Iterable[str]) -> None:
        doomed = {str(scope_id) for scope_id in scope_ids}
        active = sorted(scope_id for scope_id in doomed if self.has_active_work(scope_id))
        if active:
            raise RuntimeError(
                "Cannot delete a dataset with active initialization, compilation, "
                f"or execution: {', '.join(active)}. Other datasets remain available."
            )
        names = ", ".join(self.dataset_name(scope_id) for scope_id in sorted(doomed))
        with ObjectStateRegistry.atomic(f"delete datasets {names}"):
            remaining = [
                scope_id for scope_id in dataset_scope_ids() if scope_id not in doomed
            ]
            write_dataset_scope_ids(remaining)
            for scope_id in doomed:
                ObjectStateRegistry.unregister_scope_and_descendants(scope_id)
                self.compiled.pop(scope_id, None)
        selection = tuple(s for s in self.selected_scope_ids if s not in doomed)
        if not selection and remaining:
            selection = (remaining[0],)
        self.select(selection)
        self.refresh()

    def sync_datasets(self, scope_ids: tuple[str, ...]) -> None:
        """Make the dataset list exactly ``scope_ids``."""

        requested = tuple(dict.fromkeys(str(scope_id) for scope_id in scope_ids))
        removed = [s for s in dataset_scope_ids() if s not in set(requested)]
        if removed:
            self.delete_datasets(removed)
        self.ensure_datasets(requested)
        if self.current_scope_id not in requested:
            self.select(requested[:1])

    def reorder_dataset(self, from_index: int, to_index: int) -> None:
        scope_ids = dataset_scope_ids()
        scope_ids.insert(to_index, scope_ids.pop(from_index))
        write_dataset_scope_ids(scope_ids)
        self.publish(DatasetsChanged())

    def select(self, scope_ids: Iterable[str]) -> None:
        selection = tuple(scope_ids)
        current = selection[0] if selection else ""
        if selection == self.selected_scope_ids and current == self.current_scope_id:
            return
        self.selected_scope_ids = selection
        self.current_scope_id = current
        self.publish(SelectionChanged(selection, current))
        self.publish(AvailabilityChanged())

    # -- pipelines ------------------------------------------------------------

    def pipeline_steps(self, scope_id: str) -> list[FunctionStep]:
        return PipelineObjectStateBinding.steps_for_plate(scope_id)

    @staticmethod
    def step_scope_id(scope_id: str, step: FunctionStep) -> str:
        return ScopeTokenService.build_scope_id(scope_id, step)

    def set_pipeline_document(self, scope_id: str, document: PipelineDocument) -> None:
        """Replace one dataset's steps and PipelineConfig with a document's."""

        self.require_definition_mutation_allowed(scope_id)
        self.apply_dataset_configs({scope_id: document.pipeline_config})
        PipelineObjectStateBinding.update_plate_steps(
            scope_id, list(document.pipeline_steps)
        )
        PipelineObjectStateBinding.commit_plate_state(scope_id)
        self.pipeline_changed(scope_id)
        self.publish(
            StatusReported(f"Pipeline updated with {len(document.pipeline_steps)} steps")
        )

    def set_pipeline_source(self, scope_id: str, source: str) -> None:
        self.set_pipeline_document(scope_id, PipelineDocumentCodec.from_source(source))

    def load_pipeline_file(self, scope_id: str, path: Path | str) -> None:
        file_path = self.dataset_access.require_readable(Path(path))
        self.set_pipeline_document(
            scope_id, PipelineImporter.for_path(file_path).read(file_path)
        )

    def load_example_pipeline(self, scope_id: str) -> None:
        import openhcs.demo.basic_pipeline as example

        self.set_pipeline_source(scope_id, inspect.getsource(example))

    def add_step(
        self,
        scope_id: str,
        staged_step: FunctionStep,
        edited_step: FunctionStep,
        staged_scope_id: str,
    ) -> None:
        """Append a step staged for editing, under the staged step's scope."""

        self.require_definition_mutation_allowed(scope_id)
        label = f"add step {edited_step.name}"
        with ObjectStateRegistry.atomic(label):
            ScopeTokenService.transfer_token(scope_id, staged_step, edited_step)
            PipelineObjectStateBinding.update_plate_steps(
                scope_id, [*self.pipeline_steps(scope_id), edited_step]
            )
            ObjectStateRegistry.record_snapshot(label, staged_scope_id)
        self.pipeline_changed(scope_id)
        self.publish(StatusReported(f"Added new step: {edited_step.name}"))

    def replace_step(
        self,
        scope_id: str,
        current_step: FunctionStep,
        edited_step: FunctionStep,
    ) -> None:
        self.require_definition_mutation_allowed(scope_id)
        PipelineObjectStateBinding.replace_plate_step(scope_id, current_step, edited_step)
        self.pipeline_changed(scope_id)
        self.publish(StatusReported(f"Updated step: {edited_step.name}"))

    def move_step(self, scope_id: str, from_index: int, to_index: int) -> None:
        self.require_definition_mutation_allowed(scope_id)
        steps = self.pipeline_steps(scope_id)
        steps.insert(to_index, steps.pop(from_index))
        PipelineObjectStateBinding.update_plate_steps(scope_id, steps)
        ObjectStateRegistry.record_snapshot("reorder steps", scope_id=scope_id)
        self.pipeline_changed(scope_id)

    def insert_steps(
        self,
        scope_id: str,
        index: int,
        new_steps: list[FunctionStep],
    ) -> None:
        self.require_definition_mutation_allowed(scope_id)
        steps = self.pipeline_steps(scope_id)
        names = ", ".join(step.name for step in new_steps)
        with ObjectStateRegistry.atomic(f"paste {len(new_steps)} step(s): {names}"):
            for step in new_steps:
                ScopeTokenService.ensure_token(scope_id, step)
            steps[index:index] = new_steps
            PipelineObjectStateBinding.update_plate_steps(scope_id, steps)
        self.pipeline_changed(scope_id)

    def delete_steps(self, scope_id: str, step_scope_ids: Iterable[str]) -> None:
        doomed = set(step_scope_ids)
        self.require_definition_mutation_allowed(scope_id)
        steps = self.pipeline_steps(scope_id)
        kept = [step for step in steps if self.step_scope_id(scope_id, step) not in doomed]
        names = [step.name for step in steps if step not in kept]
        with ObjectStateRegistry.atomic(f"delete steps {', '.join(names)}"):
            for step_scope_id in doomed:
                ObjectStateRegistry.unregister_scope_and_descendants(step_scope_id)
            PipelineObjectStateBinding.update_plate_steps(scope_id, kept)
        self.pipeline_changed(scope_id)

    def set_pipeline(self, scope_id: str, steps: list[FunctionStep]) -> None:
        """Replace one dataset's pipeline steps."""

        self.require_definition_mutation_allowed(scope_id)
        PipelineObjectStateBinding.update_plate_steps(scope_id, list(steps))
        self.pipeline_changed(scope_id)

    def pipeline_changed(self, scope_id: str) -> None:
        """A dataset's steps changed: its compilation no longer applies."""

        self.require_definition_mutation_allowed(scope_id)
        self.invalidate_compilation(scope_id)
        for sessions in (self.debug_sessions, self.inspected_debug_sessions):
            debug_session = sessions.get(scope_id)
            if debug_session is not None:
                sessions[scope_id] = debug_session.mark_dirty_from_cursor()
                if sessions[scope_id].dirty_from_cursor is not None:
                    self.publish(
                        StatusReported(
                            "Debug snapshots downstream of the current cursor are dirty."
                        )
                    )
        self.publish(PipelineChanged(scope_id))
        self.publish(DatasetsChanged())

    def invalidate_compilation(self, scope_id: str) -> None:
        if scope_id in self.compiled:
            self.set_compiled(scope_id, None)
        if self.batch.is_active(scope_id):
            return
        self.clear_execution_tracking(scope_id)
        orchestrator = ObjectStateRegistry.get_object(scope_id)
        if (
            orchestrator is not None
            and orchestrator.state.has_completed_initialization
            and orchestrator.state is not OrchestratorState.READY
        ):
            self.set_dataset_state(scope_id, OrchestratorState.READY)

    def import_workspace_pipeline(
        self,
        scope_id: str,
        workspace: InputWorkspacePreparationResult | None,
    ) -> None:
        """Adopt the pipeline and config a prepared input workspace carries."""

        if workspace is None:
            return
        if workspace.pipeline_config is not None:
            self.apply_dataset_configs({scope_id: workspace.pipeline_config})
        if workspace.pipeline_import_error is not None:
            self.publish(
                StatusReported(
                    "Source workspace initialized; pipeline import failed: "
                    f"{workspace.pipeline_import_error.message}"
                )
            )
        steps = workspace.pipeline_steps
        if steps is not None:
            if not steps:
                raise RuntimeError(f"Pipeline import produced no steps for {scope_id}.")
            PipelineObjectStateBinding.update_plate_steps(scope_id, list(steps))
            self.publish(
                StatusReported(
                    f"Imported {len(steps)} step(s) for {self.dataset_name(scope_id)}"
                )
            )
        self.publish(PipelineImported(scope_id))

    def import_initialized_pipelines(self) -> None:
        for scope_id in dataset_scope_ids():
            orchestrator = ObjectStateRegistry.get_object(scope_id)
            if isinstance(orchestrator, PipelineOrchestrator):
                self.import_workspace_pipeline(
                    scope_id, orchestrator.input_workspace_preparation_result
                )

    # -- admission ------------------------------------------------------------

    def has_pending_definition_work(self, scope_id: str | None = None) -> bool:
        pending = self.init_pending | self.compile_pending
        return bool(pending) if scope_id is None else scope_id in pending

    def has_active_work(self, scope_id: str) -> bool:
        return self.batch.is_active(scope_id) or self.has_pending_definition_work(
            scope_id
        )

    def require_definition_mutation_allowed(self, scope_id: str | None = None) -> None:
        if self.has_pending_definition_work(scope_id):
            raise RuntimeError(
                "Pipeline definitions cannot change while the affected dataset has "
                "active initialization or compilation. Other datasets remain editable."
            )

    def require_definition_mutation_allowed_for_object_scope(self, scope_id: str) -> None:
        """Authorize an ObjectState mutation that may belong to a dataset."""

        if scope_id == "":
            self.require_definition_mutation_allowed()
            return
        for row in self.dataset_rows():
            if row.scope.owns_object_state_scope(scope_id):
                self.require_definition_mutation_allowed(row.scope_id)
                return

    def require_work_allowed(self, scope_id: str) -> None:
        if self.has_active_work(scope_id):
            raise RuntimeError(
                "The affected dataset has active initialization, compilation, or "
                "execution."
            )

    # -- runtime state --------------------------------------------------------

    @property
    def execution_state(self) -> ManagerExecutionState:
        return self._execution_state

    @execution_state.setter
    def execution_state(self, state: ManagerExecutionState) -> None:
        if not isinstance(state, ManagerExecutionState):
            raise TypeError(
                f"execution_state must be ManagerExecutionState, got {state!r}."
            )
        if state is self._execution_state:
            return
        self._execution_state = state
        self.publish(ExecutionStateChanged(state))
        self.publish(AvailabilityChanged())

    def set_dataset_state(self, scope_id: str, state: OrchestratorState) -> None:
        orchestrator = ObjectStateRegistry.get_object(scope_id)
        if orchestrator is not None:
            orchestrator._state = state
        self.publish(DatasetStateChanged(scope_id, state))
        self.publish(DatasetsChanged())

    def compiled_inspection(self, scope_id: str):
        """The compiler's artifact inspection of a compiled dataset, if any."""

        compiled = self.compiled.get(scope_id)
        return None if compiled is None else compiled.inspection

    def set_compiled(self, scope_id: str, compiled: CompiledDataset | None) -> None:
        if compiled is None:
            self.compiled.pop(scope_id, None)
        else:
            self.compiled[scope_id] = compiled
        self.publish(CompiledStateChanged(scope_id, compiled))
        self.publish(AvailabilityChanged())

    def mark_compile_pending(self, scope_ids: Iterable[str]) -> None:
        self.compile_pending.update(scope_ids)
        self.refresh()

    def clear_compile_pending(self, scope_ids: Iterable[str]) -> None:
        self.compile_pending.difference_update(scope_ids)
        self.refresh()

    def install_runtime_projection(self, bundle: RuntimeProjectionBundle) -> None:
        self.runtime_projection = bundle.execution
        self.debug_runtime_projection = bundle.debug
        self.publish(RuntimeProjectionChanged(bundle.execution))
        self.publish(DatasetsChanged())

    def clear_execution_tracking(self, scope_id: str) -> None:
        execution_id = self.batch.remove_plate(scope_id)
        if execution_id:
            self.progress.clear_execution(execution_id)

    def retire_execution_tracking(self, scope_id: str) -> None:
        execution_id = self.batch.retire_execution(scope_id)
        if execution_id:
            self.progress.clear_execution(execution_id)

    # -- execution server -----------------------------------------------------

    async def connect_client(self) -> "ZMQExecutionClient":
        return await self.client.connect(
            progress_callback=self.progress.on_progress,
            persistent=self.client.config.persistent,
        )

    async def ensure_server(self) -> bool:
        await self.connect_client()
        return True

    async def attach_existing_server(self) -> bool:
        client = await self.client.connect_existing(
            progress_callback=self.progress.on_progress,
            persistent=self.client.config.persistent,
            timeout=self.client.config.server_info_timeout_ms / 1000,
        )
        return client is not None

    # -- initialize -----------------------------------------------------------

    async def initialize_datasets(self, scope_ids: tuple[str, ...]) -> None:
        ensure_global_config_context(GlobalPipelineConfig, self.global_config)
        for scope_id in scope_ids:
            self.require_work_allowed(scope_id)
            self.dataset_access.require_initializable(DatasetScope.parse(scope_id).root)
        self.init_pending.update(scope_ids)
        self.refresh()
        self.publish(ProgressStarted(len(scope_ids)))
        done = 0

        async def initialize(scope_id: str) -> None:
            nonlocal done
            scope = DatasetScope.parse(scope_id)
            if ObjectStateRegistry.get_object(scope_id) is None:
                self.main_thread.call(lambda: self._create_orchestrator(scope))
            orchestrator = self.orchestrator(scope_id)
            if orchestrator.state.skips_initialization:
                self.init_pending.discard(scope_id)
                self.main_thread.call(
                    lambda: self.import_workspace_pipeline(
                        scope_id, orchestrator.input_workspace_preparation_result
                    )
                )
            else:
                self.publish(DatasetsChanged())

                def run() -> InputWorkspacePreparationResult | None:
                    ensure_global_config_context(GlobalPipelineConfig, self.global_config)
                    workspace = scope.prepare_input_workspace()
                    if workspace is not None:
                        orchestrator.bind_input_workspace(workspace)
                    orchestrator.initialize()
                    return workspace

                try:
                    workspace = await asyncio.get_running_loop().run_in_executor(
                        None, run
                    )
                except Exception as error:
                    logger.error(
                        "Failed to initialize %s: %s", scope_id, error, exc_info=True
                    )
                    self.init_pending.discard(scope_id)
                    self.set_dataset_state(scope_id, OrchestratorState.INIT_FAILED)
                    self.publish(
                        InitializationFailed(scope_id, scope.display_name, str(error))
                    )
                else:
                    self.init_pending.discard(scope_id)
                    self.main_thread.call(
                        lambda: self.import_workspace_pipeline(scope_id, workspace)
                    )
                    self.set_dataset_state(scope_id, OrchestratorState.READY)
                    if scope_id == self.current_scope_id or not self.current_scope_id:
                        self.main_thread.call(
                            lambda: self._reselect(scope_id)
                        )
            done += 1
            self.publish(ProgressAdvanced(done))

        try:
            await asyncio.gather(*(initialize(scope_id) for scope_id in scope_ids))
        finally:
            self.init_pending.difference_update(scope_ids)
            self.refresh()
            self.publish(ProgressFinished())

        states = [
            ObjectStateRegistry.get_object(scope_id).state
            for scope_id in scope_ids
            if ObjectStateRegistry.get_object(scope_id) is not None
        ]
        succeeded = sum(state is OrchestratorState.READY for state in states)
        failed = sum(state is OrchestratorState.INIT_FAILED for state in states)
        self.publish(
            StatusReported(
                f"Successfully initialized {succeeded} dataset(s)"
                if failed == 0
                else f"Initialized {succeeded} dataset(s), {failed} error(s)"
            )
        )

    def _reselect(self, scope_id: str) -> None:
        """Re-announce the current dataset once its initialization changes it."""

        if self.current_scope_id == scope_id:
            self.publish(SelectionChanged(self.selected_scope_ids, scope_id))
        else:
            self.select((scope_id,))

    # -- compile --------------------------------------------------------------

    async def compile_datasets(self, scope_ids: tuple[str, ...]) -> None:
        await self.compile_batch.compile_datasets(scope_ids)

    # -- run ------------------------------------------------------------------

    def require_execution_allowed(self, scope_ids: Iterable[str]) -> None:
        if self.execution_state.busy or self.batch.active_plates:
            raise RuntimeError("An execution batch is already active.")
        for scope_id in scope_ids:
            self.require_definition_mutation_allowed(scope_id)

    def _begin_batch(self, scope_ids: tuple[str, ...]) -> None:
        self.require_execution_allowed(scope_ids)
        self.batch.begin_batch(scope_ids)
        self.execution_state = ManagerExecutionState.RUNNING

    async def run_datasets(
        self,
        scope_ids: tuple[str, ...],
        *,
        auxiliary_params: ZMQAuxiliaryExecutionParams | None = None,
    ) -> None:
        """Compile then submit every dataset in one execution batch."""

        self._begin_batch(scope_ids)
        try:
            self.progress.reset_for_new_batch()
            self.live_measurements.clear()
            self.publish(LogsCleared())
            await self.connect_client()
            for scope_id in scope_ids:
                self.debug_terminal_summaries.pop(scope_id, None)
                self.set_dataset_state(scope_id, OrchestratorState.EXECUTING)
            self.publish(
                StatusReported(
                    f"Compiling {len(scope_ids)} dataset(s) before execution..."
                )
            )
            requests = [
                dataset_pipeline_request(scope_id, self.global_config)
                for scope_id in scope_ids
            ]
            artifacts = await self.compile_batch.compile_before_execution(requests)
            self.publish(
                StatusReported(
                    f"Compilation complete. Submitting {len(requests)} dataset(s) "
                    "for execution..."
                )
            )
            for request in requests:
                await self.submission.submit_execution(
                    request,
                    compile_artifact_id=artifacts[request.scope_id],
                    auxiliary_params=auxiliary_params,
                )
        except Exception as error:
            logger.error("Failed to execute datasets: %s", error, exc_info=True)
            self.publish(ErrorReported(f"Failed to execute: {error}"))
            await self.execution_control.handle_execution_failure()

    def observation_export_params(
        self,
        export_path: str | None,
        export_scope: ZMQRuntimeObservationExportScope | str,
    ) -> ZMQAuxiliaryExecutionParams | None:
        """Runtime observation export options for a run, under the access policy."""

        scope = ZMQRuntimeObservationExportScope(export_scope)
        if export_path is None:
            if scope is not ZMQRuntimeObservationExportScope.VALUES:
                raise ValueError("Outcome observation requires an export path.")
            return None
        path = self.dataset_access.require_writable(Path(export_path))
        if path.exists():
            raise FileExistsError(f"Runtime observation export path already exists: {path}")
        return ZMQAuxiliaryExecutionParams(
            runtime_observation_export_path=path,
            runtime_observation_export_scope=scope,
        )

    def stop_execution(self, force: bool | None = None) -> None:
        self.execution_state, force_kill = self.execution_state.stop_request(force)
        self.execution_control.stop(force=force_kill)

    def dataset_running(self, scope_id: str) -> None:
        self.publish(DatasetRunning(scope_id))
        self.publish(DatasetsChanged())

    def record_finished_execution(self, execution_id: str, payload: dict) -> None:
        """Keep an ordinary execution's submission and server record together."""

        submitted = self.submitted_executions.pop(execution_id, None)
        if submitted is None:
            return
        self.finished_executions[execution_id] = FinishedExecution(
            scope_id=submitted.scope_id,
            request=submitted.request,
            record=ExecutionRecord.from_dict(payload),
            endpoint=submitted.endpoint,
        )

    def finish_dataset_execution(
        self,
        completion: ExecutionCompletionPayload,
        scope_id: str,
    ) -> None:
        """Record one dataset's terminal status (from any thread)."""

        self.main_thread.post(lambda: self._finish_dataset_execution(completion, scope_id))

    def _finish_dataset_execution(
        self,
        completion: ExecutionCompletionPayload,
        scope_id: str,
    ) -> None:
        status = completion.status
        logger.info("Dataset %s finished with status %s", scope_id, status.value)
        self.batch.mark_terminal(scope_id, status)
        try:
            self.set_dataset_state(scope_id, status.orchestrator_state)
            self.publish(StatusReported(f"{status.status_prefix} {scope_id}"))
            if status.auto_add_output_plate:
                if self.execution_state.allows_auto_add_output:
                    self._add_output_dataset(scope_id, completion)
                else:
                    logger.info(
                        "Skipping output dataset (execution_state=%s)",
                        self.execution_state,
                    )
            self._close_debug_session(scope_id)
        finally:
            self.retire_execution_tracking(scope_id)
            if self.execution_state.stop_pending and self.batch.all_batch_terminal():
                self.execution_state = ManagerExecutionState.IDLE
            self.execution_control.check_all_completed()
            self.refresh()
        self.publish(DatasetExecutionFinished(scope_id, completion))
        if status.emit_failure:
            detail = completion.traceback_text or completion.message
            separator = ":\n\n" if completion.traceback_text else ": "
            self.publish(ErrorReported(f"Execution failed for {scope_id}{separator}{detail}"))

    def _add_output_dataset(
        self,
        source_scope_id: str,
        completion: ExecutionCompletionPayload,
    ) -> None:
        """Add the computed output root as a dataset when the run asks for it."""

        if completion.auto_add_output_plate_to_plate_manager is None:
            raise RuntimeError(
                "Missing auto-add flag in completion result; expected from compile context."
            )
        if not completion.auto_add_output_plate_to_plate_manager:
            return
        output_root = completion.output_plate_root
        if not output_root:
            return
        output_root = str(output_root)
        if output_root in dataset_scope_ids():
            return
        if DatasetRootRule.for_dataset(output_root) is LocalDirectoryRoot:
            path = Path(output_root)
            path.mkdir(parents=True, exist_ok=True)
            if not path.is_dir():
                raise RuntimeError(f"Output dataset is not a directory: {output_root}")
        self._add_scopes(
            (DatasetScope.of_root(output_root),),
            label="add output dataset",
            source_role=PreparedWorkspaceSource,
        )
        logger.info("Added output dataset %s (from %s)", output_root, source_scope_id)

    def finish_batch(self, completed_count: int, failed_count: int) -> None:
        self.execution_state = ManagerExecutionState.IDLE
        summary = f"All done: {completed_count} completed, {failed_count} failed"
        if completed_count > 1 and self.global_config.analysis_consolidation_config.enabled:
            try:
                consolidate_batch_results(self)
                summary += ". Global summary created."
            except Exception as error:
                logger.error("Failed to create global summary: %s", error, exc_info=True)
                summary += ". Global summary failed."
        self.publish(StatusReported(summary))
        self.publish(BatchFinished(completed_count, failed_count))
        self.refresh()

    # -- debug ----------------------------------------------------------------

    async def run_debug(
        self,
        scope_id: str,
        *,
        command_type: DebugCommandType = DebugCommandType.RUN,
        snapshot_store_backend: str | None = None,
        selected_source_group: str | None = None,
        pause_step_indices: tuple[int, ...] = (),
        start_step_index: int = 0,
        start_after_invocation_key: str | None = None,
    ) -> None:
        """Start a debug run, or send a command to the dataset's debug worker."""

        active = self.debug_sessions.get(scope_id)
        if active is not None:
            self.debug_sessions[scope_id] = active.with_command(command_type)
            await self.debug_runs.send_worker_command(
                debug_session_id=active.debug_session_id,
                command_type=command_type,
            )
            if command_type is DebugCommandType.STOP:
                self.debug_sessions.pop(scope_id, None)
            return

        self.require_execution_allowed((scope_id,))
        debug_session = DebugSession.create(plate_id=scope_id, command_type=command_type)
        self.debug_sessions[scope_id] = debug_session
        root = DatasetScope.parse(scope_id).root
        snapshot_root = (root if root.is_dir() else root.parent) / ".openhcs_debug"
        self._begin_batch((scope_id,))
        try:
            await self.connect_client()
            self.progress.reset_for_new_batch()
            self.publish(StatusReported(f"Compiling debug run for {scope_id}..."))
            debug_request = DebugRunRequest(
                debug_session_id=debug_session.debug_session_id,
                snapshot_store_ref=str(snapshot_root),
                snapshot_store_backend=snapshot_store_backend,
                command_type=DebugCommandType(command_type),
                selected_source_group=selected_source_group,
                pause_step_indices=tuple(pause_step_indices),
                start_step_index=start_step_index,
                start_after_invocation_key=start_after_invocation_key,
                replay_mode=DebugReplayMode.PERSISTENT_PAUSED_WORKER,
            )
            request = dataset_pipeline_request(scope_id, self.global_config)
            artifact_id = await self.debug_runs.compile_artifact_id(request, debug_request)
            self.publish(StatusReported(f"Submitting debug run for {scope_id}..."))
            await self.debug_runs.submit(
                request,
                compile_artifact_id=artifact_id,
                debug_request=debug_request,
            )
        except Exception as error:
            logger.error("Failed to execute debug run: %s", error, exc_info=True)
            self.publish(ErrorReported(f"Failed to execute debug run: {error}"))
            await self.execution_control.handle_execution_failure()

    def record_debug_snapshot(
        self,
        notification: DebugSnapshotAvailableNotification,
    ) -> None:
        scope_id = notification.progress_event.plate_id
        if notification.snapshot is not None:
            retained = tuple(
                snapshot
                for snapshot in self.debug_snapshots.get(scope_id, ())
                if snapshot.snapshot_id != notification.snapshot.snapshot_id
            )
            self.debug_snapshots[scope_id] = (*retained, notification.snapshot)
        active = self.debug_sessions.get(scope_id)
        if active is not None:
            context = notification.debug_context
            self.debug_sessions[scope_id] = active.with_snapshot_store(
                snapshot_store_ref=context.snapshot_store_ref,
                snapshot_store_backend=context.snapshot_store_backend,
                axis_id=notification.progress_event.axis_id,
            ).with_cursor(context.cursor)
        self.publish(DebugSnapshotAvailable(notification))

    def displayed_debug_session(self, scope_id: str) -> DebugSession | None:
        """The running debug session, else the one loaded from a snapshot."""

        active = self.debug_sessions.get(scope_id)
        if active is not None:
            return active
        if scope_id in self.debug_terminal_summaries:
            return None
        return self.inspected_debug_sessions.get(scope_id)

    def inspect_debug_snapshot(
        self,
        notification: DebugSnapshotAvailableNotification,
        snapshot: DebugSnapshot | None,
    ) -> None:
        """Move the displayed debug cursor to a snapshot a client opened."""

        event = notification.progress_event
        context = notification.debug_context
        scope_id = event.plate_id
        active = self.debug_sessions.get(scope_id)
        summary = self.debug_terminal_summaries.get(scope_id)
        if active is not None:
            self.debug_sessions[scope_id] = active.with_snapshot_store(
                snapshot_store_ref=context.snapshot_store_ref,
                snapshot_store_backend=context.snapshot_store_backend,
                axis_id=event.axis_id,
            ).with_cursor(context.cursor)
        elif summary is not None and summary.debug_session_id == context.debug_session_id:
            self.inspected_debug_sessions.pop(scope_id, None)
            if snapshot is not None:
                self.debug_terminal_summaries[scope_id] = summary.with_snapshot(
                    snapshot=snapshot,
                    snapshot_id=context.snapshot_id,
                    snapshot_store_ref=context.snapshot_store_ref,
                    snapshot_store_backend=context.snapshot_store_backend,
                )
        else:
            self.inspected_debug_sessions[scope_id] = DebugSession(
                debug_session_id=context.debug_session_id,
                plate_id=scope_id,
                axis_id=event.axis_id,
                snapshot_store_ref=context.snapshot_store_ref,
                snapshot_store_backend=context.snapshot_store_backend,
            ).with_cursor(context.cursor)
        self.refresh()

    def _close_debug_session(self, scope_id: str) -> None:
        active = self.debug_sessions.pop(scope_id, None)
        if active is None or active.plate_id != scope_id:
            return
        terminal_status = self.batch.terminal_status(scope_id)
        if terminal_status is None:
            self.debug_terminal_summaries.pop(scope_id, None)
        else:
            summary = DebugTerminalSummary.from_session(
                active,
                terminal_status=terminal_status.value,
                completed_at_unix=time.time(),
            )
            snapshots = self.debug_snapshots.get(scope_id, ())
            latest = snapshots[-1] if snapshots else None
            self.debug_terminal_summaries[scope_id] = (
                summary
                if latest is None
                else summary.with_snapshot(
                    snapshot=latest,
                    snapshot_id=latest.snapshot_id,
                    snapshot_store_ref=active.snapshot_store_ref,
                    snapshot_store_backend=active.snapshot_store_backend,
                )
            )
        self.publish(ExecutionStateChanged(self.execution_state))

    def debug_context(self, scope_id: str) -> DebugSessionProjectionContext:
        return DebugSessionProjectionContext(
            target=DebugSessionTargetState(
                current_plate_scope_id=scope_id,
                pipeline_scope_id=PipelineScopeIdentity.from_plate_scope(scope_id).scope_id,
                initialized=self.is_initialized(scope_id),
                compiled=scope_id in self.compiled,
                terminal_status=(
                    None
                    if (status := self.batch.terminal_status(scope_id)) is None
                    else status.value
                ),
            ),
            session=self.displayed_debug_session(scope_id),
            terminal_summary=self.debug_terminal_summaries.get(scope_id),
            pause_boundaries=DebugPauseBoundaryState(
                pause_step_indices=tuple(
                    index
                    for index, step in enumerate(self.pipeline_steps(scope_id))
                    if step.debug_pause
                )
            ),
            snapshots=self.debug_snapshots.get(scope_id, ()),
            manager_execution_state=self.execution_state,
        )

    def current_debug_context(self) -> DebugSessionProjectionContext | None:
        if not self.current_scope_id:
            return None
        return self.debug_context(self.current_scope_id)

