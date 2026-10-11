"""Session views: frozen states every client renders, and the operations they bind.

A view's state is derived on demand from ObjectState and the session's runtime
state; no client caches it. A renderer binds one button per entry of the
view's ``operations`` and asks the operation whether it is available.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, ClassVar

from metaclass_registry import AutoRegisterMeta
from objectstate.object_state import ObjectStateRegistry

from openhcs.agent.dto.session import (
    DatasetListState,
    DatasetRowState,
    PipelineStepState,
    PipelineStepsState,
)
from openhcs.agent.ui_bridge_identities import (
    PipelineEditorWidgetIdentity,
    PlateManagerWidgetIdentity,
    UiSessionViewWidgetIdentityDeclaration,
)
from openhcs.authoring.session.dataset_status import PlateStatusPresenter
from openhcs.authoring.session.datasets import DatasetRow
from openhcs.authoring.session.operations import SessionOperation
from openhcs.authoring.session.operations.datasets import (
    AddDatasets,
    CompileDatasets,
    DeleteDatasets,
    EditDatasetConfig,
    InitializeDatasets,
    RunDatasets,
    ShowDatasetCode,
    ShowDatasetImages,
    ShowLiveResults,
)
from openhcs.authoring.session.operations.pipelines import (
    AddPipelineStep,
    DeletePipelineSteps,
    EditPipelineStep,
    LoadExamplePipeline,
    ShowPipelineCode,
)
from openhcs.core.config import PathPlanningConfig
from openhcs.core.function_reference import FunctionReferenceTransportAuthority
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.pipeline.path_planner import PipelinePathPlanner
from openhcs.ui.shared.plate_scope_identity import PipelineScopeIdentity

if TYPE_CHECKING:
    from openhcs.authoring.session.session import Session


class SessionView(ABC, metaclass=AutoRegisterMeta):
    """One frozen state a client renders, and the operations it offers."""

    __registry_key__ = "view_id"
    __skip_if_no_key__ = True

    view_id: ClassVar[str | None] = None
    title: ClassVar[str]
    window: ClassVar[type[UiSessionViewWidgetIdentityDeclaration]]
    """The stable UI window that renders this view."""
    state: ClassVar[type]
    operations: ClassVar[tuple[type[SessionOperation], ...]]

    @classmethod
    def rendered_in(
        cls, window: type[UiSessionViewWidgetIdentityDeclaration]
    ) -> type["SessionView"]:
        (view,) = (view for view in cls.__registry__.values() if view.window is window)
        return view

    @classmethod
    @abstractmethod
    def state_of(cls, session: "Session") -> object: ...

    @classmethod
    def available_operations(
        cls,
        session: "Session",
        selection: tuple[str, ...],
    ) -> tuple[type[SessionOperation], ...]:
        """Operations (as each slot resolves now) available for ``selection``."""

        return tuple(
            operation
            for slot in cls.operations
            if (operation := slot.resolved(session)).available(
                session, operation.request_for_selection(session, selection)
            )
            is None
        )


# ---------------------------------------------------------------------------
# Dataset list
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class OutputRelation:
    """Source/output relation of one row, from its path planning."""

    output_scope_id: str | None = None
    output_root: str | None = None
    source_scope_id: str | None = None
    source_root: str | None = None


def output_relations(
    rows: tuple[DatasetRow, ...],
    default_path_config: PathPlanningConfig,
) -> dict[str, OutputRelation]:
    """Which rows are outputs of which, from each row's path planning config."""

    row_by_root = {row.root: row for row in rows}
    output_root_by_source: dict[str, str] = {}
    source_by_output_root: dict[str, DatasetRow] = {}
    for row in rows:
        orchestrator = ObjectStateRegistry.get_object(row.scope_id)
        path_config = (
            orchestrator.get_effective_config().path_planning_config
            if isinstance(orchestrator, PipelineOrchestrator)
            else default_path_config
        )
        output_root = str(
            PipelinePathPlanner.build_output_plate_root(Path(row.root), path_config)
        )
        if output_root == row.root:
            continue
        output_root_by_source[row.scope_id] = output_root
        if output_root in row_by_root:
            source_by_output_root[output_root] = row

    relations: dict[str, OutputRelation] = {}
    for row in rows:
        source = source_by_output_root.get(row.root)
        output_root = output_root_by_source.get(row.scope_id)
        output_row = None if output_root is None else row_by_root.get(output_root)
        relations[row.scope_id] = OutputRelation(
            output_scope_id=output_root if output_row is None else output_row.scope_id,
            output_root=output_root,
            source_scope_id=None if source is None else source.scope_id,
            source_root=None if source is None else source.root,
        )
    return relations


@dataclass(frozen=True, slots=True)
class DatasetActivity:
    """One row's work, read from the session's runtime state."""

    session: "Session"
    scope_id: str

    @property
    def initialized(self) -> bool:
        return self.session.is_initialized(self.scope_id)

    @property
    def terminal_status(self):
        return self.session.batch.terminal_status(self.scope_id)

    @property
    def orchestrator_state(self):
        terminal = self.terminal_status
        if terminal is not None:
            return terminal.orchestrator_state
        orchestrator = ObjectStateRegistry.get_object(self.scope_id)
        return orchestrator.state if isinstance(orchestrator, PipelineOrchestrator) else None

    @property
    def execution_id(self) -> str | None:
        return self.session.batch.execution_id(self.scope_id)

    @property
    def runtime(self):
        execution_id = self.execution_id
        if self.terminal_status is not None or execution_id is None:
            return None
        return self.session.runtime_projection.get_plate(
            plate_id=self.scope_id, execution_id=execution_id
        )

    @property
    def execution_active(self) -> bool:
        runtime = self.runtime
        return self.terminal_status is None and (
            self.session.batch.is_active(self.scope_id)
            or (runtime is not None and not runtime.is_terminal)
        )

    @property
    def debug_phase(self):
        if (
            self.session.debug_sessions.get(self.scope_id) is None
            and self.session.debug_terminal_summaries.get(self.scope_id) is None
        ):
            return None
        return self.session.debug_context(self.scope_id).phase

    @property
    def debug_session_id(self) -> str | None:
        active = self.session.debug_sessions.get(self.scope_id)
        if active is not None:
            return active.debug_session_id
        summary = self.session.debug_terminal_summaries.get(self.scope_id)
        return None if summary is None else summary.debug_session_id

    @property
    def status_prefix(self) -> str:
        phase = self.debug_phase
        if phase is not None:
            prefix = PlateStatusPresenter.build_debug_status_prefix(debug_phase=phase)
            if prefix:
                return prefix
        return PlateStatusPresenter.build_status_prefix(
            orchestrator_state=self.orchestrator_state,
            is_init_pending=self.scope_id in self.session.init_pending,
            is_compile_pending=self.scope_id in self.session.compile_pending,
            is_execution_active=self.execution_active,
            terminal_status=self.terminal_status,
            runtime_projection=self.runtime,
        )


class DatasetListView(SessionView):
    view_id = "dataset_list"
    title = "Datasets"
    window = PlateManagerWidgetIdentity
    state = DatasetListState
    operations = (
        AddDatasets,
        DeleteDatasets,
        EditDatasetConfig,
        InitializeDatasets,
        CompileDatasets,
        RunDatasets,
        ShowDatasetCode,
        ShowLiveResults,
        ShowDatasetImages,
    )

    @classmethod
    def state_of(cls, session: "Session") -> DatasetListState:
        rows = tuple(session.dataset_rows())
        relations = output_relations(rows, session.global_config.path_planning_config)
        selected = set(session.selected_scope_ids)
        return DatasetListState(
            rows=tuple(
                cls.row_state(session, row, relations[row.scope_id], row.scope_id in selected)
                for row in rows
            ),
            selected_scope_ids=session.selected_scope_ids,
            execution_state=session.execution_state.value,
            available_operation_ids=tuple(
                operation.operation_id
                for operation in cls.available_operations(
                    session, session.selected_scope_ids
                )
            ),
            event_sequence=session.event_log.last_sequence,
        )

    @staticmethod
    def row_state(
        session: "Session",
        row: DatasetRow,
        relation: OutputRelation,
        selected: bool,
    ) -> DatasetRowState:
        activity = DatasetActivity(session, row.scope_id)
        orchestrator_state = activity.orchestrator_state
        terminal = activity.terminal_status
        runtime = activity.runtime
        debug_phase = activity.debug_phase
        return DatasetRowState(
            scope_id=row.scope_id,
            name=row.name,
            root=row.root,
            pipeline_path=row.pipeline_path,
            selected=selected,
            initialized=activity.initialized,
            compiled=row.scope_id in session.compiled,
            init_pending=row.scope_id in session.init_pending,
            compile_pending=row.scope_id in session.compile_pending,
            execution_active=activity.execution_active,
            status_prefix=activity.status_prefix,
            orchestrator_state=(
                None if orchestrator_state is None else orchestrator_state.value
            ),
            execution_id=activity.execution_id,
            terminal_status=None if terminal is None else terminal.value,
            runtime_state=None if runtime is None else runtime.state.value,
            runtime_percent=None if runtime is None else runtime.percent,
            queue_position=None if runtime is None else runtime.queue_position,
            output_scope_id=relation.output_scope_id,
            output_root=relation.output_root,
            source_scope_id=relation.source_scope_id,
            source_root=relation.source_root,
            debug_phase=None if debug_phase is None else debug_phase.value,
            debug_session_id=activity.debug_session_id,
            finished_execution_id=next(
                (
                    execution_id
                    for execution_id, finished in reversed(
                        session.finished_executions.items()
                    )
                    if finished.scope_id == row.scope_id
                ),
                None,
            ),
        )


# ---------------------------------------------------------------------------
# Pipeline steps
# ---------------------------------------------------------------------------


def _function_entries(function_spec) -> tuple:
    if function_spec is None:
        return ()
    entries = tuple(function_spec) if isinstance(function_spec, list) else (function_spec,)
    functions = []
    for entry in entries:
        function = entry[0] if isinstance(entry, tuple) else entry
        if callable(function):
            functions.append(function)
    return tuple(functions)


def _function_name(function) -> str:
    return getattr(function, "__name__", type(function).__name__)


def _function_id(function) -> str | None:
    try:
        return FunctionReferenceTransportAuthority.function_reference(
            function
        ).composite_key
    except Exception:
        return None


class PipelineStepsView(SessionView):
    view_id = "pipeline_steps"
    title = "Pipeline Editor"
    window = PipelineEditorWidgetIdentity
    state = PipelineStepsState
    operations = (
        AddPipelineStep,
        DeletePipelineSteps,
        EditPipelineStep,
        LoadExamplePipeline,
        ShowPipelineCode,
    )

    @classmethod
    def state_of(
        cls,
        session: "Session",
        scope_id: str,
        selected_step_scope_ids: tuple[str, ...] = (),
    ) -> PipelineStepsState:
        """One dataset's steps ("" for no dataset)."""

        if not scope_id:
            return PipelineStepsState(
                scope_id=None,
                pipeline_scope_id=None,
                event_sequence=session.event_log.last_sequence,
            )
        selected = set(selected_step_scope_ids)
        steps = []
        for index, step in enumerate(session.pipeline_steps(scope_id)):
            step_scope_id = session.step_scope_id(scope_id, step)
            state = ObjectStateRegistry.get_by_scope(step_scope_id)
            functions = _function_entries(step.function_spec())
            steps.append(
                PipelineStepState(
                    step_scope_id=step_scope_id,
                    index=index,
                    name=step.name,
                    enabled=step.enabled,
                    selected=step_scope_id in selected,
                    dirty=bool(state.dirty_fields) if state is not None else False,
                    default_diff=(
                        bool(state.signature_diff_fields) if state is not None else False
                    ),
                    description=step.description,
                    debug_pause=step.debug_pause,
                    function_names=tuple(_function_name(f) for f in functions),
                    function_ids=tuple(
                        function_id
                        for f in functions
                        if (function_id := _function_id(f)) is not None
                    ),
                )
            )
        return PipelineStepsState(
            scope_id=scope_id,
            pipeline_scope_id=PipelineScopeIdentity.from_plate_scope(scope_id).scope_id,
            steps=tuple(steps),
            event_sequence=session.event_log.last_sequence,
        )
