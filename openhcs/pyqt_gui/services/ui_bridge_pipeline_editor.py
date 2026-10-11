"""PipelineEditor provider set for the PyQt UI bridge."""

from __future__ import annotations

import hashlib
from dataclasses import replace

from openhcs.agent.dto.common import AgentError, SCHEMA_VERSION
from openhcs.agent.dto.ui_bridge import (
    UiActionIdentity,
    UiActionInvokeRequest,
    UiActionSummary,
    UiCodeDocumentSelectionMode,
    UiDebugActionState,
    UiDebugCursorState,
    UiDebugRuntimeFrameState,
    UiDebugTerminalSummaryState,
    UiLiveOverviewItem,
    UiLiveOverviewMetric,
    UiLiveOverviewSection,
    UiLiveOverviewSeverity,
    UiPipelineDebugSessionState,
    UiPipelineEditorState,
    UiProgressIdentityState,
    UiStateSurfaceDocument,
    UiStateSurfaceRequest,
    UiStateSurfaceSummary,
)
from openhcs.agent.ui_bridge_identities import (
    PipelineDebugSessionStateSurfaceIdentityDeclaration,
    PipelineDebugToolbarWidgetIdentity,
    PipelineEditorStateSurfaceIdentityDeclaration,
    PipelineEditorWidgetIdentity,
    PlateManagerStateSurfaceIdentityDeclaration,
)
from python_introspect import to_jsonable
from objectstate.object_state import ObjectStateRegistry
from openhcs.core.progress.debug_projection import DebugRuntimeFrame
from openhcs.pyqt_gui.services.ui_bridge_contracts import (
    UiActionDispatch,
    UiActionProviderABC,
    UiActionProviderIdentity,
    UiBridgeSnapshotProviderABC,
    UiStateSurfaceProviderABC,
    UiStateSurfaceProviderIdentity,
    state_surface_declaration_for_identity,
    state_surface_ids_for_action,
)
from openhcs.pyqt_gui.services.ui_bridge_registry import (
    UiBridgeProviderSetABC,
    UiBridgeRegistrationContext,
)
from openhcs.authoring.session.views import PipelineStepsView
from openhcs.pyqt_gui.services.ui_bridge_session_actions import (
    SessionOperationActionProvider,
)
from openhcs.pyqt_gui.widgets.pipeline_editor import PipelineEditorWidget
from openhcs.pyqt_gui.widgets.debug_toolbar import DebugToolbarWidget
from openhcs.pyqt_gui.widgets.shared.services.debug_session_projection import (
    DebugActionRenderModel,
    DebugToolbarActionProjector,
)

PIPELINE_EDITOR_ACTIONS_TITLE = "Pipeline editor actions"
PIPELINE_DEBUG_TOOLBAR_ACTIONS_TITLE = "Pipeline debug toolbar actions"
PLATE_MANAGER_STATE_SURFACE_ID = (
    PlateManagerStateSurfaceIdentityDeclaration.require_value()
)
PIPELINE_EDITOR_WIDGET_ID = PipelineEditorWidgetIdentity.require_value()
PIPELINE_DEBUG_TOOLBAR_WIDGET_ID = PipelineDebugToolbarWidgetIdentity.require_value()
PIPELINE_EDITOR_STATE_DECLARATION = state_surface_declaration_for_identity(
    PipelineEditorWidget.UI_STATE_SURFACE_DECLARATIONS,
    PipelineEditorStateSurfaceIdentityDeclaration,
)
PIPELINE_EDITOR_STATE_IDENTITY = UiStateSurfaceProviderIdentity.from_owner(
    PIPELINE_EDITOR_STATE_DECLARATION,
    widget_declaration=PipelineEditorWidget.UI_BRIDGE_WIDGET_IDENTITY,
)
PIPELINE_DEBUG_SESSION_STATE_DECLARATION = state_surface_declaration_for_identity(
    DebugToolbarWidget.UI_STATE_SURFACE_DECLARATIONS,
    PipelineDebugSessionStateSurfaceIdentityDeclaration,
)
PIPELINE_DEBUG_SESSION_STATE_IDENTITY = UiStateSurfaceProviderIdentity.from_owner(
    PIPELINE_DEBUG_SESSION_STATE_DECLARATION,
    widget_declaration=DebugToolbarWidget.UI_BRIDGE_WIDGET_IDENTITY,
)


class PipelineDebugToolbarActionProvider(UiActionProviderABC):
    """Expose declared debug-toolbar controls through the UI bridge."""

    identity = UiActionProviderIdentity.from_widget_declaration(
        PipelineDebugToolbarWidgetIdentity,
        title=PIPELINE_DEBUG_TOOLBAR_ACTIONS_TITLE,
    )

    def __init__(self, manager) -> None:
        self._manager = manager

    def action_ids(self) -> tuple[str, ...]:
        return tuple(
            declaration.action_id()
            for declaration in DebugToolbarActionProjector.declarations()
        )

    def summary(self, action_id: str) -> UiActionSummary:
        model = self._model(action_id)
        return UiActionSummary(
            schema_version=SCHEMA_VERSION,
            identity=UiActionIdentity(
                widget_id=self.identity.widget_id,
                action_id=action_id,
            ),
            title=model.label,
            enabled=model.disabled_reason is None,
            disabled_error=(
                None
                if model.disabled_reason is None
                else model.disabled_reason.as_agent_error()
            ),
            invocation_mode="sync",
            side_effects=model.side_effects,
            confirmation_required=model.confirmation_required,
            selection_mode="current_pipeline",
            current_selection_count=len(model.target_scope_ids),
            target_scope_ids=model.target_scope_ids,
            selection_revision_token=self._selection_revision_token(),
            related_state_surface_ids=self._related_state_surface_ids(action_id),
        )

    def dispatch(self, request: UiActionInvokeRequest) -> UiActionDispatch:
        event_sequence = self._manager.session.event_log.last_sequence
        self._model(request.action_id).declaration.invoke(self._manager.debug_workflow)
        return UiActionDispatch(event_sequence=event_sequence)

    def workflow_status_surface_ids(self) -> tuple[str, ...]:
        return tuple(
            dict.fromkeys(
                (
                    PLATE_MANAGER_STATE_SURFACE_ID,
                    *(
                        declaration.surface_id
                        for declaration in self._owner_surface_declarations()
                    ),
                )
            )
        )

    @staticmethod
    def _owner_surface_declarations():
        return (
            *PipelineEditorWidget.UI_STATE_SURFACE_DECLARATIONS,
            *DebugToolbarWidget.UI_STATE_SURFACE_DECLARATIONS,
        )

    @classmethod
    def _related_state_surface_ids(cls, action_id: str) -> tuple[str, ...]:
        owner_surface_ids = state_surface_ids_for_action(
            cls._owner_surface_declarations(),
            action_id,
        )
        return tuple(
            dict.fromkeys((PLATE_MANAGER_STATE_SURFACE_ID, *owner_surface_ids))
        )

    def _models(self) -> tuple[DebugActionRenderModel, ...]:
        return DebugToolbarActionProjector.render_models(
            self._manager.debug_session_context()
        )

    def _model(self, action_id: str) -> DebugActionRenderModel:
        for model in self._models():
            if model.action_id == action_id:
                return model
        raise ValueError(f"Debug toolbar action is not declared: {action_id!r}")

    def _selection_revision_token(self) -> str:
        models = self._models()
        parts = (
            self.identity.widget_id,
            tuple(
                (
                    model.action_id,
                    model.enabled,
                    (
                        None
                        if model.disabled_reason is None
                        else model.disabled_reason.code
                    ),
                    model.target_scope_ids,
                )
                for model in models
            ),
            ObjectStateRegistry.get_token(),
        )
        return hashlib.sha256(repr(parts).encode("utf-8")).hexdigest()


class PipelineDebugSessionStateSurfaceProvider(UiStateSurfaceProviderABC):
    """Pollable PipelineEditor debug-session state backed by shared projection."""

    identity = PIPELINE_DEBUG_SESSION_STATE_IDENTITY

    def __init__(
        self,
        manager,
        *,
        snapshot_provider: UiBridgeSnapshotProviderABC,
    ) -> None:
        self._manager = manager
        self._snapshot_provider = snapshot_provider

    def summary(self) -> UiStateSurfaceSummary:
        target_scope_ids = self._target_scope_ids()
        return UiStateSurfaceSummary(
            schema_version=SCHEMA_VERSION,
            identity=self.identity.as_surface_identity(),
            title=self.identity.title,
            widget_id=self.identity.widget_id,
            readable=True,
            supported_selection_modes=("all",),
            current_selection_count=len(target_scope_ids),
            total_scope_count=1 if target_scope_ids else 0,
        )

    def read(self, request: UiStateSurfaceRequest) -> UiStateSurfaceDocument:
        selection_mode = request.resolved_selection_mode(
            UiCodeDocumentSelectionMode.ALL
        )
        try:
            state = self._state()
        except Exception as exc:
            return self._state_error(
                request,
                (AgentError.from_exception("ui_state_surface_read_failed", exc),),
            )

        revision_token = self._revision_token(state, selection_mode=selection_mode)
        state = replace(
            state,
            current_revision_token=revision_token,
            current_snapshot=self._snapshot_provider.current_snapshot(),
            unchanged=request.base_revision_token == revision_token,
        )
        return self._document_from_state(state, selection_mode=selection_mode)

    def overview_sections(self) -> tuple[UiLiveOverviewSection, ...]:
        state = self._state()
        disabled_actions = tuple(
            action for action in state.actions if action.disabled_error is not None
        )
        items = []
        if state.terminal_summary is not None:
            items.append(
                UiLiveOverviewItem(
                    label="terminal debug session",
                    status=state.terminal_summary.terminal_status,
                    detail=self._terminal_summary_detail(state),
                    severity=UiLiveOverviewSeverity.WARNING.value,
                    source_surface_id=self.identity.surface_id,
                    source_widget_id=PipelineDebugToolbarWidgetIdentity.require_value(),
                )
            )
        items.extend(self._disabled_action_item(action) for action in disabled_actions)
        return (
            UiLiveOverviewSection(
                section_id=self.identity.surface_id,
                title=self.identity.title,
                summary=state.phase,
                metrics=(
                    UiLiveOverviewMetric(
                        key="phase",
                        label="phase",
                        value=state.phase,
                    ),
                    UiLiveOverviewMetric(
                        key="compiled",
                        label="compiled",
                        value=str(state.compiled),
                    ),
                    UiLiveOverviewMetric(
                        key="actions",
                        label="actions",
                        value=str(len(state.actions)),
                    ),
                    UiLiveOverviewMetric(
                        key="disabled",
                        label="disabled",
                        value=str(len(disabled_actions)),
                    ),
                ),
                items=tuple(items),
            ),
        )

    def _state(self) -> UiPipelineDebugSessionState:
        context = self._manager.debug_session_context()
        target = context.target
        session = context.active_session
        actions = tuple(self._action_state(model) for model in self._models())
        debug_projection = self._manager.debug_runtime_projection()
        return UiPipelineDebugSessionState(
            schema_version=SCHEMA_VERSION,
            summary=self.summary(),
            object_state_token=ObjectStateRegistry.get_token(),
            current_plate_scope_id=(
                None if target is None else target.current_plate_scope_id
            ),
            pipeline_scope_id=None if target is None else target.pipeline_scope_id,
            manager_execution_state=context.manager_execution_state.value,
            initialized=False if target is None else target.initialized,
            compiled=False if target is None else target.compiled,
            phase=DebugToolbarActionProjector.phase(context).value,
            active_session_id=None if session is None else session.debug_session_id,
            execution_id=None if session is None else session.execution_id,
            axis_id=None if session is None else session.axis_id,
            selected_source_group=(
                None if session is None else session.selected_source_group
            ),
            snapshot_store_ref=None if session is None else session.snapshot_store_ref,
            snapshot_store_backend=(
                None if session is None else session.snapshot_store_backend
            ),
            terminal_status=None if target is None else target.terminal_status,
            cursor=(
                None
                if session is None
                else self._cursor_state(session.cursor, session.dirty_from_cursor)
            ),
            terminal_summary=self._terminal_summary_state(context),
            actions=actions,
            current_frame=self._runtime_frame_state(debug_projection.current_frame),
            last_frame=self._runtime_frame_state(debug_projection.last_frame),
            selected_scope_ids=self._target_scope_ids(),
            current_revision_token=self._snapshot_provider.revision_token(
                self.identity.revision_key
            ),
            current_snapshot=self._snapshot_provider.current_snapshot(),
        )

    def _models(self) -> tuple[DebugActionRenderModel, ...]:
        return DebugToolbarActionProjector.render_models(
            self._manager.debug_session_context()
        )

    @staticmethod
    def _terminal_summary_detail(state: UiPipelineDebugSessionState) -> str | None:
        summary = state.terminal_summary
        if summary is None:
            return None
        parts = [
            f"plate={summary.plate_scope_id}",
            f"command={summary.command_type}",
        ]
        if summary.step_name is not None:
            parts.append(f"step={summary.step_name}")
        if summary.callable_name is not None:
            parts.append(f"callable={summary.callable_name}")
        return " ".join(parts)

    @staticmethod
    def _disabled_action_item(action: UiDebugActionState) -> UiLiveOverviewItem:
        disabled = action.disabled_error
        return UiLiveOverviewItem(
            label=action.label,
            status=None if disabled is None else disabled.code,
            detail=None if disabled is None else disabled.message,
            severity=UiLiveOverviewSeverity.INFO.value,
            source_surface_id=PIPELINE_DEBUG_SESSION_STATE_IDENTITY.surface_id,
            source_widget_id=PipelineDebugToolbarWidgetIdentity.require_value(),
        )

    @classmethod
    def _action_state(cls, model: DebugActionRenderModel) -> UiDebugActionState:
        return UiDebugActionState(
            action_id=model.action_id,
            label=model.label,
            placement=model.placement.value,
            enabled=model.enabled,
            side_effects=model.side_effects,
            confirmation_required=model.confirmation_required,
            requires_active_debug_session=model.requires_active_debug_session,
            disabled_error=(
                None
                if model.disabled_reason is None
                else model.disabled_reason.as_agent_error()
            ),
            selected_scope_ids=model.target_scope_ids,
        )

    @staticmethod
    def _cursor_state(cursor, dirty_from_cursor) -> UiDebugCursorState | None:
        if cursor is None:
            return None
        return UiDebugCursorState(
            step_index=cursor.step_index,
            step_scope_id=cursor.step_scope_id,
            group_key=cursor.group_key,
            invocation_key=cursor.invocation_key,
            pattern_group_identity=cursor.pattern_group_identity,
            dirty=dirty_from_cursor == cursor,
        )

    def _terminal_summary_state(
        self,
        context,
    ) -> UiDebugTerminalSummaryState | None:
        summary = context.terminal_summary
        if summary is None:
            return None
        return UiDebugTerminalSummaryState(
            debug_session_id=summary.debug_session_id,
            plate_scope_id=summary.plate_id,
            terminal_status=summary.terminal_status,
            command_type=(
                None if summary.command_type is None else summary.command_type.value
            ),
            axis_id=summary.axis_id,
            snapshot_id=summary.snapshot_id,
            snapshot_store_ref=summary.snapshot_store_ref,
            snapshot_store_backend=summary.snapshot_store_backend,
            step_name=summary.step_name,
            callable_name=summary.callable_name,
            cursor=self._cursor_state(summary.cursor, None),
            completed_at_unix=summary.completed_at_unix,
        )

    @classmethod
    def _runtime_frame_state(
        cls,
        frame: DebugRuntimeFrame | None,
    ) -> UiDebugRuntimeFrameState | None:
        if frame is None:
            return None
        identity = frame.progress_identity
        context = frame.record.context
        cursor_state = cls._cursor_state(frame.cursor, None)
        if cursor_state is None:
            raise ValueError("Debug runtime frame cursor projection is required.")
        return UiDebugRuntimeFrameState(
            debug_session_id=frame.record.session_id,
            snapshot_store_ref=context.snapshot_store_ref,
            snapshot_store_backend=context.snapshot_store_backend,
            progress_identity=UiProgressIdentityState(
                execution_id=identity.execution_id,
                plate_id=identity.plate_id,
                axis_id=identity.axis_id,
                step_name=identity.step_name,
            ),
            cursor=cursor_state,
            event_type=frame.event_type.value,
            step_name=frame.step_name,
            callable_name=frame.callable_name,
            snapshot_id=frame.snapshot_id,
            timestamp=frame.record.event.timestamp,
        )

    def _target_scope_ids(self) -> tuple[str, ...]:
        return DebugToolbarActionProjector.target_scope_ids(
            self._manager.debug_session_context()
        )

    def _revision_token(
        self,
        state: UiPipelineDebugSessionState,
        *,
        selection_mode: str,
    ) -> str:
        action_parts = tuple(
            (
                action.action_id,
                action.enabled,
                None if action.disabled_error is None else action.disabled_error.code,
                action.selected_scope_ids,
            )
            for action in state.actions
        )
        cursor_parts = None
        if state.cursor is not None:
            cursor_parts = (
                state.cursor.step_index,
                state.cursor.step_scope_id,
                state.cursor.group_key,
                state.cursor.invocation_key,
                state.cursor.pattern_group_identity,
                state.cursor.dirty,
            )
        parts = (
            self.identity.revision_key,
            str(state.object_state_token),
            self._snapshot_provider.current_branch_head_snapshot_id(),
            str(ObjectStateRegistry.get_current_snapshot_index()),
            selection_mode,
            state.current_plate_scope_id,
            state.pipeline_scope_id,
            state.manager_execution_state,
            state.initialized,
            state.compiled,
            state.phase,
            state.active_session_id,
            state.execution_id,
            state.axis_id,
            state.selected_source_group,
            state.snapshot_store_ref,
            state.snapshot_store_backend,
            state.terminal_status,
            cursor_parts,
            (
                None
                if state.terminal_summary is None
                else (
                    state.terminal_summary.debug_session_id,
                    state.terminal_summary.terminal_status,
                    state.terminal_summary.command_type,
                    state.terminal_summary.axis_id,
                    state.terminal_summary.snapshot_id,
                    state.terminal_summary.snapshot_store_ref,
                    state.terminal_summary.snapshot_store_backend,
                    state.terminal_summary.step_name,
                    state.terminal_summary.callable_name,
                    state.terminal_summary.completed_at_unix,
                )
            ),
            self._frame_revision_parts(state.current_frame),
            self._frame_revision_parts(state.last_frame),
            action_parts,
        )
        return hashlib.sha256(repr(parts).encode("utf-8")).hexdigest()

    @staticmethod
    def _frame_revision_parts(
        frame: UiDebugRuntimeFrameState | None,
    ) -> tuple | None:
        if frame is None:
            return None
        return (
            frame.debug_session_id,
            frame.progress_identity.execution_id,
            frame.progress_identity.plate_id,
            frame.progress_identity.axis_id,
            frame.progress_identity.step_name,
            frame.cursor.step_index,
            frame.cursor.step_scope_id,
            frame.cursor.group_key,
            frame.cursor.invocation_key,
            frame.cursor.pattern_group_identity,
            frame.event_type,
            frame.step_name,
            frame.callable_name,
            frame.snapshot_id,
            frame.snapshot_store_ref,
            frame.snapshot_store_backend,
            frame.timestamp,
        )

    def _state_error(
        self,
        request: UiStateSurfaceRequest,
        errors: tuple[AgentError, ...],
    ) -> UiStateSurfaceDocument:
        selection_mode = request.resolved_selection_mode(
            UiCodeDocumentSelectionMode.ALL
        )
        state = UiPipelineDebugSessionState(
            schema_version=SCHEMA_VERSION,
            summary=self.summary(),
            object_state_token=ObjectStateRegistry.get_token(),
            current_plate_scope_id=None,
            pipeline_scope_id=None,
            manager_execution_state="unknown",
            initialized=False,
            compiled=False,
            phase="unavailable",
            active_session_id=None,
            execution_id=None,
            axis_id=None,
            selected_source_group=None,
            snapshot_store_ref=None,
            snapshot_store_backend=None,
            terminal_status=None,
            cursor=None,
            terminal_summary=None,
            actions=(),
            selected_scope_ids=(),
            current_revision_token=self._snapshot_provider.revision_token(
                self.identity.revision_key
            ),
            current_snapshot=self._snapshot_provider.current_snapshot(),
            errors=errors,
        )
        return self._document_from_state(state, selection_mode=selection_mode)

    @staticmethod
    def _document_from_state(
        state: UiPipelineDebugSessionState,
        *,
        selection_mode: str,
    ) -> UiStateSurfaceDocument:
        payload = to_jsonable(state)
        if not isinstance(payload, dict):
            raise TypeError(
                "Debug session state payload did not serialize to an object."
            )
        return UiStateSurfaceDocument(
            schema_version=state.schema_version,
            summary=state.summary,
            payload_schema=PIPELINE_DEBUG_SESSION_STATE_DECLARATION.payload_schema,
            payload=payload,
            current_revision_token=state.current_revision_token,
            current_snapshot=state.current_snapshot,
            selection_mode=selection_mode,
            selected_scope_ids=state.selected_scope_ids,
            unchanged=state.unchanged,
            warnings=state.warnings,
            errors=state.errors,
        )


class PipelineEditorStateSurfaceProvider(UiStateSurfaceProviderABC):
    """Pollable PipelineEditor state backed by shared manager widget hooks."""

    identity = PIPELINE_EDITOR_STATE_IDENTITY

    def __init__(
        self,
        manager,
        *,
        snapshot_provider: UiBridgeSnapshotProviderABC,
    ) -> None:
        self._manager = manager
        self._snapshot_provider = snapshot_provider

    def summary(self) -> UiStateSurfaceSummary:
        return UiStateSurfaceSummary(
            schema_version=SCHEMA_VERSION,
            identity=self.identity.as_surface_identity(),
            title=self.identity.title,
            widget_id=self.identity.widget_id,
            readable=True,
            supported_selection_modes=("selected", "all"),
            current_selection_count=len(self._manager.get_selected_items()),
            total_scope_count=len(self._manager.STATE_BINDING.items(self._manager)),
        )

    def read(self, request: UiStateSurfaceRequest) -> UiStateSurfaceDocument:
        selection_mode = request.resolved_selection_mode(
            UiCodeDocumentSelectionMode.ALL
        )
        try:
            state = self._state(selection_mode=selection_mode)
        except Exception as exc:
            return self._state_error(
                request,
                (AgentError.from_exception("ui_state_surface_read_failed", exc),),
            )

        revision_token = self._revision_token(state, selection_mode=selection_mode)
        state = UiPipelineEditorState(
            schema_version=state.schema_version,
            summary=state.summary,
            object_state_token=state.object_state_token,
            current_plate_scope_id=state.current_plate_scope_id,
            pipeline_scope_id=state.pipeline_scope_id,
            steps=state.steps,
            selected_scope_ids=state.selected_scope_ids,
            current_revision_token=revision_token,
            current_snapshot=self._snapshot_provider.current_snapshot(),
            unchanged=request.base_revision_token == revision_token,
            errors=state.errors,
            warnings=state.warnings,
        )
        return self._document_from_state(state, selection_mode=selection_mode)

    def _state(self, *, selection_mode: str) -> UiPipelineEditorState:
        selected = self._manager.selected_step_scope_ids()
        view = PipelineStepsView.state_of(
            self._manager.session, self._manager.current_plate, selected
        )
        steps = view.steps
        if selection_mode == UiCodeDocumentSelectionMode.SELECTED.value:
            steps = tuple(step for step in steps if step.selected)
        return UiPipelineEditorState(
            schema_version=SCHEMA_VERSION,
            summary=self.summary(),
            object_state_token=ObjectStateRegistry.get_token(),
            current_plate_scope_id=view.scope_id,
            pipeline_scope_id=view.pipeline_scope_id,
            steps=steps,
            selected_scope_ids=selected,
            current_revision_token=self._snapshot_provider.revision_token(
                self.identity.revision_key
            ),
            current_snapshot=self._snapshot_provider.current_snapshot(),
        )

    def _revision_token(
        self,
        state: UiPipelineEditorState,
        *,
        selection_mode: str,
    ) -> str:
        step_parts = tuple(
            (
                step.step_scope_id,
                step.index,
                step.name,
                step.enabled,
                step.selected,
                step.dirty,
                step.default_diff,
                step.debug_pause,
                step.function_names,
                step.function_ids,
            )
            for step in state.steps
        )
        parts = (
            self.identity.revision_key,
            str(state.object_state_token),
            self._snapshot_provider.current_branch_head_snapshot_id(),
            str(ObjectStateRegistry.get_current_snapshot_index()),
            selection_mode,
            state.current_plate_scope_id,
            state.pipeline_scope_id,
            state.selected_scope_ids,
            step_parts,
        )
        return hashlib.sha256(repr(parts).encode("utf-8")).hexdigest()

    def _state_error(
        self,
        request: UiStateSurfaceRequest,
        errors: tuple[AgentError, ...],
    ) -> UiStateSurfaceDocument:
        selection_mode = request.resolved_selection_mode(
            UiCodeDocumentSelectionMode.ALL
        )
        state = UiPipelineEditorState(
            schema_version=SCHEMA_VERSION,
            summary=self.summary(),
            object_state_token=ObjectStateRegistry.get_token(),
            current_plate_scope_id=None,
            pipeline_scope_id=None,
            steps=(),
            selected_scope_ids=(),
            current_revision_token=self._snapshot_provider.revision_token(
                self.identity.revision_key
            ),
            current_snapshot=self._snapshot_provider.current_snapshot(),
            errors=errors,
        )
        return self._document_from_state(state, selection_mode=selection_mode)

    @staticmethod
    def _document_from_state(
        state: UiPipelineEditorState,
        *,
        selection_mode: str,
    ) -> UiStateSurfaceDocument:
        payload = to_jsonable(state)
        if not isinstance(payload, dict):
            raise TypeError(
                "PipelineEditor state payload did not serialize to an object."
            )
        return UiStateSurfaceDocument(
            schema_version=state.schema_version,
            summary=state.summary,
            payload_schema=PIPELINE_EDITOR_STATE_DECLARATION.payload_schema,
            payload=payload,
            current_revision_token=state.current_revision_token,
            current_snapshot=state.current_snapshot,
            selection_mode=selection_mode,
            selected_scope_ids=state.selected_scope_ids,
            unchanged=state.unchanged,
            warnings=state.warnings,
            errors=state.errors,
        )


class PipelineEditorBridgeProviderSet(UiBridgeProviderSetABC):
    """Register PipelineEditor surfaces with a UI bridge registry."""

    registry_key = PIPELINE_EDITOR_WIDGET_ID

    def __init__(self, manager) -> None:
        self._manager = manager

    @classmethod
    def for_main_window(cls, main_window) -> "PipelineEditorBridgeProviderSet":
        return cls(main_window.pipeline_editor_widget)

    def register(self, context: UiBridgeRegistrationContext) -> None:
        context.registry.register_state_surface_provider(
            PipelineEditorStateSurfaceProvider(
                self._manager,
                snapshot_provider=context.snapshot_provider,
            )
        )
        context.registry.register_state_surface_provider(
            PipelineDebugSessionStateSurfaceProvider(
                self._manager,
                snapshot_provider=context.snapshot_provider,
            )
        )
        context.registry.register_action_provider(
            SessionOperationActionProvider(
                identity=UiActionProviderIdentity.from_widget_declaration(
                    PipelineEditorWidgetIdentity,
                    title=PIPELINE_EDITOR_ACTIONS_TITLE,
                ),
                session=self._manager.session,
                operations=PipelineStepsView.operations,
                selection=self._manager.selected_step_scope_ids,
                related_state_surface_ids=lambda action_id: state_surface_ids_for_action(
                    PipelineEditorWidget.UI_STATE_SURFACE_DECLARATIONS, action_id
                ),
            )
        )
        context.registry.register_action_provider(
            PipelineDebugToolbarActionProvider(self._manager)
        )
