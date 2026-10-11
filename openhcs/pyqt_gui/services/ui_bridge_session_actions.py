"""UI-bridge actions that are session operations.

One provider serves any widget whose buttons are session operations: the
catalog, availability, labels and invocation all come from the operation
classes, so a new operation is a bridge action with no provider code.
"""

from __future__ import annotations

import hashlib
from collections.abc import Callable

from objectstate.object_state import ObjectStateRegistry

from openhcs.agent.dto.common import SCHEMA_VERSION, AgentError
from openhcs.agent.dto.ui_bridge import (
    UiActionIdentity,
    UiActionInvokeRequest,
    UiActionSummary,
)
from openhcs.authoring.session.operations import SessionOperation
from openhcs.authoring.session.operations.datasets import PromptedOperation
from openhcs.authoring.session.session import Session
from openhcs.pyqt_gui.services.ui_bridge_contracts import (
    UiActionDispatch,
    UiActionProviderABC,
    UiActionProviderIdentity,
)
from openhcs.pyqt_gui.widgets.shared.services.qt_widget_edit_commit import (
    commit_focused_widget_edits,
)


class SessionOperationActionProvider(UiActionProviderABC):
    """Bridge actions for a fixed tuple of session operation slots."""

    def __init__(
        self,
        *,
        identity: UiActionProviderIdentity,
        session: Session,
        operations: tuple[type[SessionOperation], ...],
        selection: Callable[[], tuple[str, ...]] = tuple,
        related_state_surface_ids: Callable[[str], tuple[str, ...]] = lambda _id: (),
        workflow_status_surface_ids: tuple[str, ...] = (),
    ) -> None:
        self.identity = identity
        self._session = session
        self._operations = operations
        self._selection = selection
        self._related_state_surface_ids = related_state_surface_ids
        self._workflow_status_surface_ids = workflow_status_surface_ids

    def action_ids(self) -> tuple[str, ...]:
        return tuple(slot.operation_id for slot in self._operations)

    def catalog_warnings(self):
        return tuple(warning for slot in self._operations for warning in slot.warnings)

    def workflow_status_surface_ids(self) -> tuple[str, ...]:
        return self._workflow_status_surface_ids

    def summary(self, action_id: str) -> UiActionSummary:
        operation = self._operation(action_id)
        selection = self._selection()
        error = operation.available(
            self._session, operation.request_for_selection(self._session, selection)
        )
        return UiActionSummary(
            schema_version=SCHEMA_VERSION,
            identity=UiActionIdentity(widget_id=self.identity.widget_id, action_id=action_id),
            title=operation.button_label(self._session),
            enabled=error is None,
            disabled_error=error,
            invocation_mode="sync",
            side_effects=operation.side_effects,
            confirmation_required=operation.confirmation_required,
            selection_mode=operation.selection_mode,
            current_selection_count=len(selection),
            target_scope_ids=selection,
            selection_revision_token=self._selection_revision_token(selection),
            related_state_surface_ids=self._related_state_surface_ids(action_id),
        )

    def dispatch(self, request: UiActionInvokeRequest) -> UiActionDispatch:
        operation = self._operation(request.action_id)
        commit_focused_widget_edits()
        session_request = (
            self._session.renderer.prompt(operation)
            if issubclass(operation, PromptedOperation)
            else operation.request_for_selection(self._session, self._selection())
        )
        if session_request is None:
            return UiActionDispatch(
                errors=(AgentError(code="ui_action_cancelled", message="The user cancelled."),)
            )
        result = self._session.invoke(operation, session_request)
        return UiActionDispatch(
            errors=result.errors,
            warnings=result.warnings,
            event_sequence=result.event_sequence,
        )

    def _operation(self, action_id: str) -> type[SessionOperation]:
        slot = SessionOperation.named(action_id)
        if slot not in self._operations:
            raise ValueError(f"{self.identity.widget_id} has no action {action_id!r}.")
        return slot.resolved(self._session)

    def _selection_revision_token(self, selection: tuple[str, ...]) -> str:
        parts = (self.identity.widget_id, selection, ObjectStateRegistry.get_token())
        return hashlib.sha256(repr(parts).encode("utf-8")).hexdigest()
