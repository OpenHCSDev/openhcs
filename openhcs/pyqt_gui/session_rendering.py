"""The Qt GUI as a session renderer.

* :class:`QtSessionEventRelay` re-emits session events on the Qt thread.
* :class:`SessionOperationButtons` binds a manager's buttons to its session
  view's operations: labels, availability and invocation all come from the
  operation classes.
* :class:`GuiRenderer` presents renderer operations through the
  :class:`OperationPresenter` family and prompts for the requests of prompted
  operations through the :class:`RequestPrompter` family.
"""

from __future__ import annotations

import logging
from abc import ABC, abstractmethod
from typing import TYPE_CHECKING, ClassVar

from metaclass_registry import AutoRegisterMeta
from PyQt6.QtCore import QObject, pyqtSignal

from openhcs.agent.dto.common import AgentError
from openhcs.agent.dto.session import SessionOperationResult
from openhcs.authoring.session.operations import SessionOperation
from openhcs.authoring.session.operations.datasets import PromptedOperation
from openhcs.authoring.session.session import Renderer, Session
from openhcs.pyqt_gui.widgets.shared.services.qt_widget_edit_commit import (
    commit_focused_widget_edits,
)

if TYPE_CHECKING:
    from openhcs.authoring.session.views import SessionView

logger = logging.getLogger(__name__)


class QtSessionEventRelay(QObject):
    """Re-emit each session event record on this object's (Qt) thread."""

    published = pyqtSignal(object)

    def __init__(self, session: Session, parent: QObject | None = None) -> None:
        super().__init__(parent)
        self._unsubscribe = session.subscribe(self.published.emit)

    def close(self) -> None:
        self._unsubscribe()


class SessionOperationButtons:
    """Manager buttons bound to ``SESSION_VIEW.operations``."""

    SESSION_VIEW: ClassVar[type["SessionView"]]
    session: Session

    def __init_subclass__(cls, **kwargs) -> None:
        super().__init_subclass__(**kwargs)
        if "SESSION_VIEW" in cls.__dict__:
            cls.BUTTON_CONFIGS = [
                (operation.label, operation.operation_id, operation.tooltip)
                for operation in cls.SESSION_VIEW.operations
            ]

    def selection_scope_ids(self) -> tuple[str, ...]:
        """Scope ids the view's operations act on for the current selection."""

        raise NotImplementedError

    def request_for(self, operation: type[SessionOperation]) -> object | None:
        if issubclass(operation, PromptedOperation):
            return self.session.renderer.prompt(operation)
        return operation.request_for_selection(
            self.session, self.selection_scope_ids()
        )

    def handle_button_action(self, operation_id: str) -> None:
        commit_focused_widget_edits()
        operation = SessionOperation.named(operation_id).resolved(self.session)
        request = self.request_for(operation)
        if request is None:
            return
        self.report_result(self.session.invoke(operation, request))

    def report_result(self, result: SessionOperationResult) -> None:
        for error in result.errors:
            self.status_message.emit(error.message)

    def update_button_states(self) -> None:
        selection = self.selection_scope_ids()
        for slot in self.SESSION_VIEW.operations:
            operation = slot.resolved(self.session)
            button = self.buttons[slot.operation_id]
            request = operation.request_for_selection(self.session, selection)
            button.setEnabled(operation.available(self.session, request) is None)
            button.setText(operation.button_label(self.session))
            button.setToolTip(operation.tooltip)


class OperationPresenter(ABC, metaclass=AutoRegisterMeta):
    """How the desktop GUI presents one renderer operation."""

    __registry_key__ = "operation"
    __skip_if_no_key__ = True

    operation: ClassVar[type[SessionOperation] | None] = None

    @abstractmethod
    def present(self, renderer: "GuiRenderer", request: object) -> None: ...

    def unavailable_reason(
        self,
        renderer: "GuiRenderer",
        request: object,
    ) -> AgentError | None:
        del renderer, request
        return None


class RequestPrompter(ABC, metaclass=AutoRegisterMeta):
    """How the desktop GUI asks its user for one prompted operation's request."""

    __registry_key__ = "operation"
    __skip_if_no_key__ = True

    operation: ClassVar[type[SessionOperation] | None] = None

    @abstractmethod
    def prompt(self, renderer: "GuiRenderer") -> object | None:
        """The request, or ``None`` when the user cancels."""


class GuiRenderer(Renderer):
    """The desktop main window presenting renderer operations."""

    def __init__(self, main_window) -> None:
        self.main_window = main_window

    def presents(self, operation: type[SessionOperation]) -> bool:
        return operation in OperationPresenter.__registry__

    def present(self, operation: type[SessionOperation], request: object) -> None:
        OperationPresenter.__registry__[operation]().present(self, request)

    def unavailable_reason(
        self,
        operation: type[SessionOperation],
        request: object,
    ) -> AgentError | None:
        return OperationPresenter.__registry__[operation]().unavailable_reason(
            self, request
        )

    def prompt(self, operation: type[SessionOperation]) -> object | None:
        return RequestPrompter.__registry__[operation]().prompt(self)

    @property
    def plate_manager(self):
        return self.main_window.plate_manager_widget

    @property
    def pipeline_editor(self):
        return self.main_window.pipeline_editor_widget
