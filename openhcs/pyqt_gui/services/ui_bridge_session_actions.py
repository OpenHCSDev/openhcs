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
    UiActionCatalog,
    UiActionIdentity,
    UiActionInvocationStatus,
    UiActionInvokeRequest,
    UiActionInvokeResult,
    UiActionSummary,
    UiMutationReceipt,
)
from openhcs.authoring.session.operations import SessionOperation
from openhcs.authoring.session.operations.datasets import PromptedOperation
from openhcs.authoring.session.session import Session
from openhcs.pyqt_gui.services.ui_bridge_contracts import (
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

    def catalog(self) -> UiActionCatalog:
        return UiActionCatalog(
            schema_version=SCHEMA_VERSION,
            actions=tuple(self.summary(slot.operation_id) for slot in self._operations),
            warnings=tuple(
                warning for slot in self._operations for warning in slot.warnings
            ),
        )

    def summary(self, action_id: str) -> UiActionSummary:
        operation = self._operation(action_id)
        selection = self._selection()
        error = self._availability_error(operation, selection)
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
            selection_revision_token=self._selection_revision_token(),
            related_state_surface_ids=self._related_state_surface_ids(action_id),
        )

    def invoke(self, request: UiActionInvokeRequest) -> UiActionInvokeResult:
        try:
            operation = self._operation(request.action_id)
        except Exception as exc:
            return self._result(request, (AgentError.from_exception("unknown_ui_action", exc),))
        selection = self._selection()
        if request.selected_scope_ids and request.selected_scope_ids != selection:
            return self._result(
                request,
                (
                    AgentError(
                        code="stale_ui_action_selection",
                        message="Requested target scopes do not match the current selection.",
                    ),
                ),
            )
        observed = request.observed_selection_revision_token
        if observed is not None and observed != self._selection_revision_token():
            return self._result(
                request,
                (
                    AgentError(
                        code="stale_ui_action_revision",
                        message="The selection changed after the action was planned.",
                    ),
                ),
            )
        error = self._availability_error(operation, selection)
        if error is None and operation.confirmation_required and request.confirmation_is_required():
            error = AgentError(
                code="confirmation_required",
                message=(
                    f"{operation.label} mutates state or starts work; set "
                    "require_confirmation=False to dispatch it."
                ),
            )
        if error is not None:
            return self._result(request, (error,))
        commit_focused_widget_edits()
        session_request = (
            self._session.renderer.prompt(operation)
            if issubclass(operation, PromptedOperation)
            else operation.request_for_selection(self._session, selection)
        )
        if session_request is None:
            return self._result(
                request,
                (AgentError(code="ui_action_cancelled", message="The user cancelled."),),
            )
        result = self._session.invoke(operation, session_request)
        return self._result(request, result.errors, warnings=result.warnings)

    def _operation(self, action_id: str) -> type[SessionOperation]:
        slot = SessionOperation.named(action_id)
        if slot not in self._operations:
            raise ValueError(f"{self.identity.widget_id} has no action {action_id!r}.")
        return slot.resolved(self._session)

    def _availability_error(
        self,
        operation: type[SessionOperation],
        selection: tuple[str, ...],
    ) -> AgentError | None:
        return operation.available(
            self._session, operation.request_for_selection(self._session, selection)
        )

    def _selection_revision_token(self) -> str:
        parts = (
            self.identity.widget_id,
            self._selection(),
            ObjectStateRegistry.get_token(),
        )
        return hashlib.sha256(repr(parts).encode("utf-8")).hexdigest()

    def _result(
        self,
        request: UiActionInvokeRequest,
        errors: tuple[AgentError, ...],
        *,
        warnings=(),
    ) -> UiActionInvokeResult:
        accepted = not errors
        return UiActionInvokeResult(
            schema_version=SCHEMA_VERSION,
            identity=UiActionIdentity(
                widget_id=request.widget_id,
                action_id=request.action_id,
            ),
            status=(
                UiActionInvocationStatus.ACCEPTED
                if accepted
                else UiActionInvocationStatus.REJECTED
            ).value,
            receipt=(
                UiMutationReceipt.accepted_for(request.request_token)
                if accepted
                else UiMutationReceipt.rejected_for(request.request_token)
            ),
            target_scope_ids=self._selection(),
            selection_revision_token=self._selection_revision_token(),
            workflow_status_surface_ids=self._workflow_status_surface_ids,
            errors=errors,
            warnings=tuple(warnings),
        )
