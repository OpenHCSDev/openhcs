"""Qt service stand-ins for widgets that render a session in tests."""

from __future__ import annotations

import asyncio
import inspect
import os
from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import dataclass, field
from pathlib import Path

from objectstate.lazy_factory import ensure_global_config_context
from objectstate.object_state import ObjectStateRegistry
from pyqt_reactive.theming import ColorScheme

from openhcs.authoring.session.datasets import write_dataset_scope_ids
from openhcs.authoring.session.session import CallerThread, Session
from openhcs.core.config import GlobalPipelineConfig
from openhcs.pyqt_gui.services.service_adapter import GlobalEventBus
from openhcs.runtime.zmq_config import OpenHCSZMQConfig


@dataclass
class GuiServiceStub:
    """The Qt services a manager widget asks for; dialogs are recorded."""

    errors: list[str] = field(default_factory=list)
    directory_choices: list[str] = field(default_factory=list)
    event_bus: GlobalEventBus = field(default_factory=GlobalEventBus)
    main_window: object | None = None
    global_config: object | None = None
    file_manager: object | None = None

    def get_file_manager(self):
        return self.file_manager

    def get_current_color_scheme(self) -> ColorScheme:
        return ColorScheme()

    def get_event_bus(self) -> GlobalEventBus:
        return self.event_bus

    def show_error_dialog(self, message: str) -> None:
        self.errors.append(message)

    def show_cached_directory_dialog(self, **_kwargs) -> list[str]:
        return list(self.directory_choices)

    def set_global_config(self, config) -> None:
        self.global_config = config

    def execute_async_operation(self, async_func, *args, **kwargs) -> None:
        """Run widget-started work to completion on the calling thread."""

        result = async_func(*args, **kwargs)
        if inspect.iscoroutine(result):
            asyncio.run(result)


def session_port() -> int:
    """A per-process port no test connects to unless it starts a server."""

    return 26000 + os.getpid() % 10000


@contextmanager
def caller_session(**kwargs) -> Iterator[Session]:
    """A session on the caller's thread over an empty ObjectState registry.

    ``persisted_scope_ids`` is a dataset list the session finds on start, as if
    restored from a saved workspace.
    """

    ObjectStateRegistry.clear()
    global_config = kwargs.pop("global_config", GlobalPipelineConfig())
    ensure_global_config_context(GlobalPipelineConfig, global_config)
    persisted = kwargs.pop("persisted_scope_ids", None)
    if persisted is not None:
        write_dataset_scope_ids(list(persisted))
    session = Session(
        transport_config=OpenHCSZMQConfig(default_port=session_port(), persistent=False),
        global_config=global_config,
        main_thread=kwargs.pop("main_thread", CallerThread()),
        **kwargs,
    )
    _forget_progress(session)
    try:
        yield session
    finally:
        session.close()
        _forget_progress(session)
        ObjectStateRegistry.clear()


def _forget_progress(session: Session) -> None:
    """The progress registry is process-wide; each test starts without events."""

    tracker = session.progress_tracker
    for execution_id in tuple(tracker.get_execution_ids()):
        tracker.clear_execution(execution_id)


def add_datasets(session: Session, root: Path, *names: str) -> tuple[str, ...]:
    """Add one empty dataset directory per name; return their scope ids."""

    roots = []
    for name in names:
        path = root / name
        path.mkdir(parents=True, exist_ok=True)
        roots.append(str(path))
    return session.add_dataset_roots(roots)


_APPLICATION = []


def qt_app():
    """The process's QApplication, kept alive for every widget test."""

    from PyQt6.QtWidgets import QApplication

    if not _APPLICATION:
        _APPLICATION.append(QApplication.instance() or QApplication([]))
    return _APPLICATION[0]


@dataclass
class SessionGui:
    """The dataset list and pipeline editor rendering one session."""

    app: object
    session: Session
    services: GuiServiceStub
    plate_manager: object
    pipeline_editor: object

    def settle(self) -> None:
        self.app.processEvents()


@contextmanager
def session_gui(**session_kwargs) -> Iterator[SessionGui]:
    """Both manager widgets over a caller-thread session, with the GUI renderer."""

    from types import SimpleNamespace

    from openhcs.pyqt_gui.config import get_default_ui_config
    from openhcs.pyqt_gui.session_rendering import GuiRenderer
    from openhcs.pyqt_gui.widgets.pipeline_editor import PipelineEditorWidget
    from openhcs.pyqt_gui.widgets.plate_manager import PlateManagerWidget

    app = qt_app()
    with caller_session(**session_kwargs) as session:
        services = GuiServiceStub()
        plate_manager = PlateManagerWidget(
            services, session, gui_config=get_default_ui_config()
        )
        pipeline_editor = PipelineEditorWidget(services, session)
        services.main_window = SimpleNamespace(
            plate_manager_widget=plate_manager,
            pipeline_editor_widget=pipeline_editor,
        )
        session.attach_renderer(GuiRenderer(services.main_window))
        gui = SessionGui(app, session, services, plate_manager, pipeline_editor)
        gui.settle()
        try:
            yield gui
        finally:
            pipeline_editor.close()
            plate_manager.cleanup()
            plate_manager.close()
            # Free both widget trees now. Left to garbage collection, a later
            # test's application-wide restyle can walk a widget whose wrapper
            # is collected mid-walk.
            release_widgets(app, pipeline_editor, plate_manager)


def release_widgets(app, *widgets) -> None:
    """Delete widgets and process their deferred deletion before returning."""

    from PyQt6.QtCore import QCoreApplication, QEvent

    # Run zero-delay timers the widgets queued first: pyqt-reactive's manager
    # header queues ``QTimer.singleShot(0, status_label.adjustSize)`` with no
    # context object, so it would otherwise fire on the deleted label.
    app.processEvents()
    for widget in widgets:
        widget.deleteLater()
    QCoreApplication.sendPostedEvents(None, QEvent.Type.DeferredDelete.value)
    app.processEvents()
