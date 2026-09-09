"""Shared PlateManager state projection for UI rendering and agent bridge polling."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING

from objectstate.object_state import ObjectStateRegistry
from pyqt_reactive.services.scope_color_service import ScopeColorService

from openhcs.agent.dto.ui_bridge import (
    UiPlateManagerRowState,
    UiPlateManagerState,
    UiStateSurfaceSummary,
)
from openhcs.core.config import PathPlanningConfig
from openhcs.core.debug_session_projection import DebugSessionPhase
from openhcs.core.execution_state import (
    TerminalExecutionStatus,
)
from openhcs.core.orchestrator.orchestrator import (
    OrchestratorState,
    PipelineOrchestrator,
)
from openhcs.core.pipeline.path_planner import PipelinePathPlanner
from openhcs.core.progress.projection import PlateRuntimeProjection
from openhcs.core.selection import SelectedAllSelectionMode
from openhcs.pyqt_gui.services.plate_manager_row import PlateManagerRow
from openhcs.pyqt_gui.widgets.shared.services.debug_session_projection import (
    DebugToolbarActionProjector,
)
from openhcs.pyqt_gui.widgets.shared.services.plate_status_presenter import (
    PlateStatusPresenter,
)

if TYPE_CHECKING:
    from openhcs.pyqt_gui.widgets.plate_manager import PlateManagerWidget


@dataclass(frozen=True, slots=True)
class PlateManagerStateSelectionAuthority:
    """Closed selection-mode table for PlateManager state projection."""

    all_rows: tuple[PlateManagerRow, ...]
    selected_rows: tuple[PlateManagerRow, ...]

    def rows_for_mode(self, selection_mode: str) -> tuple[PlateManagerRow, ...]:
        mode = SelectedAllSelectionMode(selection_mode)
        rows_by_mode = {
            SelectedAllSelectionMode.ALL: self.all_rows,
            SelectedAllSelectionMode.SELECTED: self.selected_rows,
        }
        return rows_by_mode[mode]


@dataclass(frozen=True, slots=True)
class PlateManagerOutputPlateRelation:
    """Input/output plate relationship projected from path-planning config."""

    output_plate_scope_id: str | None = None
    output_plate_root: str | None = None
    source_plate_scope_id: str | None = None
    source_plate_root: str | None = None


@dataclass(frozen=True, slots=True)
class PlateManagerOutputPlateRelationAuthority:
    """Build source/output plate relationships from visible PlateManager rows."""

    relations: dict[str, PlateManagerOutputPlateRelation]

    @classmethod
    def from_rows(
        cls,
        rows: tuple[PlateManagerRow, ...],
        default_path_config: PathPlanningConfig,
    ) -> "PlateManagerOutputPlateRelationAuthority":
        row_by_root = {row.plate_root: row for row in rows}
        output_root_by_source: dict[str, str] = {}
        source_by_output_root: dict[str, PlateManagerRow] = {}
        for row in rows:
            output_root = cls._output_plate_root(
                row,
                cls._path_config_for_row(row, default_path_config),
            )
            if output_root is None or output_root == row.plate_root:
                continue
            output_root_by_source[row.scope_id] = output_root
            if output_root in row_by_root:
                source_by_output_root[output_root] = row

        relations: dict[str, PlateManagerOutputPlateRelation] = {}
        for row in rows:
            source_row = source_by_output_root.get(row.plate_root)
            output_root = output_root_by_source.get(row.scope_id)
            output_row = None if output_root is None else row_by_root.get(output_root)
            relations[row.scope_id] = PlateManagerOutputPlateRelation(
                source_plate_scope_id=(
                    None if source_row is None else source_row.scope_id
                ),
                source_plate_root=(
                    None if source_row is None else source_row.plate_root
                ),
                output_plate_scope_id=(
                    output_root if output_row is None else output_row.scope_id
                ),
                output_plate_root=output_root,
            )
        return cls(relations=relations)

    def relation_for(self, row: PlateManagerRow) -> PlateManagerOutputPlateRelation:
        return self.relations.get(row.scope_id, PlateManagerOutputPlateRelation())

    @staticmethod
    def _output_plate_root(
        row: PlateManagerRow,
        path_config: PathPlanningConfig,
    ) -> str | None:
        return str(
            PipelinePathPlanner.build_output_plate_root(
                Path(row.plate_root),
                path_config,
            )
        )

    @staticmethod
    def _path_config_for_row(
        row: PlateManagerRow,
        default_path_config: PathPlanningConfig,
    ) -> PathPlanningConfig:
        orchestrator = ObjectStateRegistry.get_object(row.scope_id)
        if isinstance(orchestrator, PipelineOrchestrator):
            return orchestrator.get_effective_config().path_planning_config
        return default_path_config


@dataclass(frozen=True, slots=True)
class PlateRowActivityProjection:
    """Ephemeral view of existing work owners, independent of path planning."""

    manager: "PlateManagerWidget"
    row: PlateManagerRow

    @property
    def initialized(self) -> bool:
        orchestrator = ObjectStateRegistry.get_object(self.row.scope_id)
        return (
            isinstance(orchestrator, PipelineOrchestrator)
            and orchestrator.state.has_completed_initialization
        )

    @property
    def orchestrator_state(self) -> OrchestratorState | None:
        terminal = self.terminal_status
        if terminal is not None:
            return terminal.orchestrator_state
        orchestrator = ObjectStateRegistry.get_object(self.row.scope_id)
        return (
            orchestrator.state
            if isinstance(orchestrator, PipelineOrchestrator)
            else None
        )

    @property
    def execution_id(self) -> str | None:
        return self.manager.plate_terminal_activity_status.execution_id(
            self.row.scope_id
        )

    @property
    def terminal_status(self) -> TerminalExecutionStatus | None:
        return self.manager.plate_terminal_activity_status.terminal_status(
            self.row.scope_id
        )

    @property
    def runtime_projection(self) -> PlateRuntimeProjection | None:
        execution_id = self.execution_id
        if self.terminal_status is not None or execution_id is None:
            return None
        return self.manager.runtime_progress_projection.get_plate(
            plate_id=self.row.scope_id, execution_id=execution_id
        )

    @property
    def execution_active(self) -> bool:
        runtime = self.runtime_projection
        return self.terminal_status is None and (
            self.manager.plate_terminal_activity_status.is_active(self.row.scope_id)
            or (runtime is not None and not runtime.is_terminal)
        )

    @property
    def debug_phase(self) -> DebugSessionPhase | None:
        scope = self.row.scope_id
        if (
            self.manager.debug_session_for_plate(scope) is None
            and self.manager.debug_terminal_summary_for_plate(scope) is None
        ):
            return None
        return DebugToolbarActionProjector.phase(
            self.manager.debug_session_context_for_plate(scope)
        )

    @property
    def debug_session_id(self) -> str | None:
        scope = self.row.scope_id
        session = self.manager.debug_session_for_plate(scope)
        if session is not None:
            return session.debug_session_id
        summary = self.manager.debug_terminal_summary_for_plate(scope)
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
            is_init_pending=self.row.scope_id in self.manager.plate_init_pending,
            is_compile_pending=self.row.scope_id in self.manager.plate_compile_pending,
            is_execution_active=self.execution_active,
            terminal_status=self.terminal_status,
            runtime_projection=self.runtime_projection,
        )


class PlateManagerStateProjectionService:
    """Build the single PlateManager state projection used by UI and bridge code."""

    def output_relation_for(
        self,
        manager: "PlateManagerWidget",
        row: PlateManagerRow,
    ) -> PlateManagerOutputPlateRelation:
        """Return the source/output relation for one visible PlateManager row."""
        return PlateManagerOutputPlateRelationAuthority.from_rows(
            tuple(manager.plates),
            manager.global_config.path_planning_config,
        ).relation_for(row)

    @staticmethod
    def scope_accent_color(plate_scope_id: str) -> str:
        """Project the current UI-owned scope accent as an exact Qt color name."""

        return (
            ScopeColorService.instance().get_accent_color(plate_scope_id).name().lower()
        )

    def project(
        self,
        manager: "PlateManagerWidget",
        *,
        schema_version: str,
        summary: UiStateSurfaceSummary,
        selection_mode: str,
    ) -> UiPlateManagerState:
        all_rows = tuple(manager.plates)
        selected_rows = tuple(manager.get_selected_items())
        selected_scope_ids = tuple(row.scope_id for row in selected_rows)
        selected_scope_set = set(selected_scope_ids)
        output_relations = PlateManagerOutputPlateRelationAuthority.from_rows(
            all_rows,
            manager.global_config.path_planning_config,
        )
        rows = PlateManagerStateSelectionAuthority(
            all_rows=all_rows,
            selected_rows=selected_rows,
        ).rows_for_mode(selection_mode)
        return UiPlateManagerState(
            schema_version=schema_version,
            summary=summary,
            selection_mode=selection_mode,
            rows=tuple(
                self.project_row(
                    manager,
                    row,
                    selected_scope_ids=selected_scope_set,
                    output_relation=output_relations.relation_for(row),
                )
                for row in rows
            ),
            selected_scope_ids=selected_scope_ids,
            manager_execution_state=manager.execution_state.value,
            object_state_token=ObjectStateRegistry.get_token(),
        )

    def project_row(
        self,
        manager: "PlateManagerWidget",
        row: PlateManagerRow,
        *,
        selected_scope_ids: set[str],
        output_relation: PlateManagerOutputPlateRelation,
    ) -> UiPlateManagerRowState:
        activity = self.activity_for(manager, row)
        orchestrator_state = activity.orchestrator_state
        terminal_status = activity.terminal_status
        runtime = activity.runtime_projection
        debug_phase = activity.debug_phase
        return UiPlateManagerRowState(
            plate_scope_id=row.scope_id,
            name=row.name,
            plate_root=row.plate_root,
            cppipe_path=row.cppipe_path,
            selected=row.scope_id in selected_scope_ids,
            initialized=activity.initialized,
            compiled=row.scope_id in manager.plate_compiled_data,
            init_pending=row.scope_id in manager.plate_init_pending,
            compile_pending=row.scope_id in manager.plate_compile_pending,
            execution_active=activity.execution_active,
            status_prefix=activity.status_prefix,
            orchestrator_state=(
                None if orchestrator_state is None else orchestrator_state.value
            ),
            execution_id=activity.execution_id,
            terminal_status=None if terminal_status is None else terminal_status.value,
            runtime_state=None if runtime is None else runtime.state.value,
            runtime_percent=None if runtime is None else runtime.percent,
            queue_position=None if runtime is None else runtime.queue_position,
            output_plate_scope_id=output_relation.output_plate_scope_id,
            output_plate_root=output_relation.output_plate_root,
            source_plate_scope_id=output_relation.source_plate_scope_id,
            source_plate_root=output_relation.source_plate_root,
            debug_phase=None if debug_phase is None else debug_phase.value,
            debug_session_id=activity.debug_session_id,
            scope_accent_color=self.scope_accent_color(row.scope_id),
        )

    @staticmethod
    def activity_for(
        manager: "PlateManagerWidget", row: PlateManagerRow
    ) -> PlateRowActivityProjection:
        return PlateRowActivityProjection(manager, row)
