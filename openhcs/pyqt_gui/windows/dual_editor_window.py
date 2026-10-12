"""The step editor window.

pyqt-reactive's ``TabbedEditorWindow`` does the work. This module declares what
OpenHCS edits in it (a pipeline step, see ``dual_editor_session.StepEdit``; its
tabs, see ``dual_editor_tabs``) and keeps the one thing that is about pipelines:
following the step when the pipeline around it changes.
"""

import logging
from collections.abc import Callable
from functools import singledispatchmethod

from formbridge.services.scope_token_service import ScopeTokenService
from objectstate import ScopeKey
from objectstate.object_state import ObjectStateRegistry
from PyQt6.QtCore import QTimer
from pyqt_reactive.services.time_travel_navigation import FunctionScopeRef, NavigationTarget
from pyqt_reactive.services.window_manager import WindowManager
from pyqt_reactive.services.window_navigation import RegisteredWindowNavigationRequest
from pyqt_reactive.theming import ColorScheme
from pyqt_reactive.windows.tabbed_editor_window import TabbedEditorWindow

from openhcs.authoring.session.events import (
    GlobalConfigChanged,
    PipelineChanged,
    PipelineImported,
    SessionEvent,
)
from openhcs.authoring.session.session import Session
from openhcs.authoring.session.step_scopes import StepEditorScope
from openhcs.core.artifact_inspection import CompiledArtifactInspection
from openhcs.core.config import SourceBindingsConfig
from openhcs.core.source_binding_context import SourceBindingContext
from openhcs.core.steps.function_step import FunctionStep
from openhcs.pyqt_gui.session_rendering import QtSessionEventRelay
from openhcs.pyqt_gui.windows import dual_editor_tabs  # noqa: F401 - declares the tabs
from openhcs.pyqt_gui.windows.dual_editor_session import (
    StepEdit,
    StepEditorTab,
    _nothing_to_do,
)
from openhcs.ui.shared.plate_scope_identity import PipelineScopeIdentity

logger = logging.getLogger(__name__)


def _main_window_of(service_adapter, parent_widget):
    """The main window, from the given service adapter or the nearest manager widget's."""
    from pyqt_reactive.widgets.shared.abstract_manager_widget import (
        AbstractManagerWidget,
    )

    current = parent_widget
    while service_adapter is None and current is not None:
        if isinstance(current, AbstractManagerWidget):
            service_adapter = current.service_adapter
        current = current.parent()
    return None if service_adapter is None else service_adapter.main_window


class DualEditorWindow(TabbedEditorWindow):
    """Edit one pipeline step; follow it while the pipeline around it changes."""

    edited: StepEdit
    tabs: tuple[StepEditorTab, ...]

    def __init__(
        self,
        step_data: FunctionStep,
        is_new: bool = False,
        on_save_callback: Callable[[FunctionStep], None] = _nothing_to_do,
        color_scheme: ColorScheme | None = None,
        orchestrator=None,
        parent=None,
        service_adapter=None,
        step_index: int | None = None,
        *,
        plate_scope: str,
        source_bindings: SourceBindingsConfig | None = None,
        source_binding_context: SourceBindingContext | None = None,
        function_invocation_badge_provider: (
            Callable[[str, int, Callable], str | None] | None
        ) = None,
        compiled_artifact_inspection_provider: Callable[
            [str], CompiledArtifactInspection | None
        ] = _nothing_to_do,
        before_mutation: Callable[[], None] = _nothing_to_do,
    ):
        if orchestrator is None:
            raise RuntimeError("DualEditorWindow requires the plate's orchestrator")
        super().__init__(
            StepEdit(
                pipeline_step=step_data,
                plate_scope=str(plate_scope),
                orchestrator=orchestrator,
                is_new=is_new,
                list_position=step_index,
                on_save=on_save_callback,
                before_mutation=before_mutation,
                source_bindings=source_bindings,
                source_binding_context=source_binding_context,
                function_invocation_badge_provider=function_invocation_badge_provider,
                compiled_artifact_inspection_provider=compiled_artifact_inspection_provider,
                main_window=_main_window_of(service_adapter, parent),
            ),
            color_scheme=color_scheme,
            parent=parent,
        )
        self._session_subscriptions: list[Callable[[], None]] = []

    # -- following the pipeline -----------------------------------------------

    def connect_session_events(self, session: Session) -> None:
        """Follow pipeline and global-config changes the session publishes."""
        self._authoring_session = session
        relay = QtSessionEventRelay(session, parent=self)
        # A bound method, not a closure over self: PyQt holds bound-method
        # slots weakly, so the connection does not keep this window alive.
        relay.published.connect(self._on_session_record)
        plate_scope = self.edited.plate_scope
        pipeline_scope = PipelineScopeIdentity.from_plate_scope(plate_scope).scope_id

        def follow_restored_pipeline(dirty_states, _triggering_scope) -> None:
            if any(scope_id == pipeline_scope for scope_id, _state in dirty_states):
                QTimer.singleShot(0, lambda: self._follow_pipeline(plate_scope))

        restored = ObjectStateRegistry.add_time_travel_complete_callback(follow_restored_pipeline)
        self.destroyed.connect(restored.release)
        self._session_subscriptions += [relay.close, restored.release]

    def _on_session_record(self, record) -> None:
        self.on_session_event(record.event)

    @singledispatchmethod
    def on_session_event(self, event: SessionEvent) -> None:
        del event

    @on_session_event.register
    def _(self, event: PipelineChanged) -> None:
        self._follow_pipeline(event.scope_id)

    @on_session_event.register
    def _(self, event: PipelineImported) -> None:
        self._follow_pipeline(event.scope_id)

    @on_session_event.register
    def _(self, event: GlobalConfigChanged) -> None:
        del event
        # Inherited placeholders in the step editor re-resolve against the new
        # global config.
        ObjectStateRegistry.increment_token()

    def _follow_pipeline(self, scope_id: str) -> None:
        if scope_id == self.edited.plate_scope:
            self._on_pipeline_changed(self._authoring_session.pipeline_steps(scope_id))

    def _on_pipeline_changed(self, pipeline_steps: list[FunctionStep]) -> None:
        """Follow this editor's step to its new position or its replacement object."""
        edit = self.edited
        step_token = StepEditorScope.parse(edit.scope_id).step_token.raw
        found = next(
            (
                (index, step)
                for index, step in enumerate(pipeline_steps)
                if ScopeTokenService.object_token(step) == step_token
            ),
            None,
        )
        if found is None:
            return
        index, step = found

        if index != edit.list_position:
            edit.list_position = index
            self._step_index = index
            for tab in self.tabs:
                tab.set_step_index(index)
            self._refresh_scope_border()
            self.apply_dirty_window_presentation()

        # The edited clone is never replaced: it holds the unsaved changes. Only the
        # views of what the pipeline holds follow a replaced step object.
        if step is not edit.pipeline_step:
            edit.pipeline_step = step
            for tab in self.tabs:
                tab.pipeline_step_replaced(step)
            self.detect_changes()

    def _cleanup_managed_resources(self) -> None:
        for release in self._session_subscriptions:
            release()
        self._session_subscriptions.clear()
        super()._cleanup_managed_resources()


def step_function_scope(scope_id: str) -> FunctionScopeRef | None:
    """A function child scope of a step editor, owned by the step's scope."""

    try:
        scope = StepEditorScope.parse(scope_id)
    except ValueError:
        return None
    if scope.is_function_scope and ScopeKey(scope.child_scope_id).depth == 1:
        return FunctionScopeRef(
            owner_scope_id=scope.step_scope_id,
            function_token=scope.child_scope_id,
        )
    return None


def select_step_editor_tab_after_time_travel(
    scope_id: str,
    target: NavigationTarget,
) -> None:
    """Show the tab that holds the field or function time travel focused."""

    window = WindowManager.get_window(scope_id)
    if isinstance(window, DualEditorWindow):
        request = RegisteredWindowNavigationRequest(
            window=window,
            requested_scope_id=scope_id,
            field_path=target.to_field_path(),
        )
        for tab in window.window_navigation_driver().owning_tabs(request):
            tab.select()
