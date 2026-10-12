"""
OpenHCS PyQt6 Application

Main application class that initializes the PyQt6 application and
manages global configuration and services.
"""

import logging
import sys
from collections.abc import Callable
from typing import TYPE_CHECKING

from objectstate import spawn_thread_with_context
from polystore.base import storage_registry
from polystore.filemanager import FileManager
from PyQt6 import QtCore
from PyQt6.QtCore import qInstallMessageHandler
from PyQt6.QtWidgets import QApplication, QMessageBox
from pyqt_reactive.utils.scroll_filter import install_shift_wheel_scrolling

from openhcs import __version__ as OPENHCS_VERSION
from openhcs.pyqt_gui.branding import openhcs_application_icon
from openhcs.pyqt_gui.config import PyQtGuiRuntimeContext, UIConfig

if TYPE_CHECKING:
    from openhcs.pyqt_gui.main import OpenHCSMainWindow

logger = logging.getLogger(__name__)


class StartupReadinessState:
    """One state of the main-window readiness boundary; each owns its transitions.

    The base answers every event by staying put.
    """

    @staticmethod
    def deferred_initialization_complete(readiness: "MainWindowStartupReadiness") -> None:
        return None

    @staticmethod
    def painted(readiness: "MainWindowStartupReadiness") -> None:
        return None

    @staticmethod
    def report_painted_ready(readiness: "MainWindowStartupReadiness") -> None:
        return None

    @staticmethod
    def fail(readiness: "MainWindowStartupReadiness", error: BaseException) -> None:
        readiness._finish()
        readiness._report_failure(error)


class WaitingForDeferredInitialization(StartupReadinessState):
    @staticmethod
    def deferred_initialization_complete(readiness: "MainWindowStartupReadiness") -> None:
        readiness._state = WaitingForInitializedPaint
        readiness._main_window.update()


class WaitingForInitializedPaint(StartupReadinessState):
    @staticmethod
    def painted(readiness: "MainWindowStartupReadiness") -> None:
        readiness._state = PaintCompletionQueued
        QtCore.QTimer.singleShot(0, readiness._report_painted_ready)


class PaintCompletionQueued(StartupReadinessState):
    @staticmethod
    def report_painted_ready(readiness: "MainWindowStartupReadiness") -> None:
        readiness._finish()
        logger.info("OpenHCS main window painted and ready")
        readiness._report_ready()


class StartupReadinessFinished(StartupReadinessState):
    @staticmethod
    def fail(readiness: "MainWindowStartupReadiness", error: BaseException) -> None:
        return None


class MainWindowStartupReadiness(QtCore.QObject):
    """Report readiness only after initialized main-window content is painted."""

    def __init__(
        self,
        main_window,
        *,
        on_ready: Callable[[], None] | None,
        on_failure: Callable[[BaseException], None] | None,
    ) -> None:
        super().__init__(main_window)
        self._main_window = main_window
        self._on_ready = on_ready
        self._on_failure = on_failure
        self._state: type[StartupReadinessState] = WaitingForDeferredInitialization
        main_window.installEventFilter(self)

    def deferred_initialization_complete(self) -> None:
        """Arm readiness for the first paint containing deferred UI state."""
        self._state.deferred_initialization_complete(self)

    def fail(self, error: BaseException) -> None:
        """Terminate the readiness boundary with its originating failure."""
        self._state.fail(self, error)

    def eventFilter(self, watched, event) -> bool:  # noqa: N802
        if watched is self._main_window and event.type() == QtCore.QEvent.Type.Close:
            self._finish()
            return super().eventFilter(watched, event)
        if watched is self._main_window and event.type() == QtCore.QEvent.Type.Paint:
            self._state.painted(self)
        return super().eventFilter(watched, event)

    def _report_painted_ready(self) -> None:
        self._state.report_painted_ready(self)

    def _report_failure(self, error: BaseException) -> None:
        if self._on_failure is not None:
            self._on_failure(error)

    def _report_ready(self) -> None:
        if self._on_ready is None:
            return
        try:
            self._on_ready()
        except Exception as error:
            if self._on_failure is None:
                raise
            self._on_failure(error)

    def _finish(self) -> None:
        self._state = StartupReadinessFinished
        self._main_window.removeEventFilter(self)
        self.deleteLater()


class OpenHCSPyQtApp(QApplication):
    """
    OpenHCS PyQt6 Application.

    Main application class that manages global state, configuration,
    and the main window lifecycle.
    """

    def __init__(
        self,
        argv: list,
        *,
        runtime_context: PyQtGuiRuntimeContext,
    ):
        """
        Initialize the OpenHCS PyQt6 application.

        Args:
            argv: Command line arguments
            runtime_context: Startup-resolved GUI runtime context
        """
        super().__init__(argv)

        def _qt_message_handler(msg_type, context, message):
            if "QTextCursor::setPosition" in message:
                logger.warning("Qt: %s", message)

        qInstallMessageHandler(_qt_message_handler)

        # Application metadata
        self.setApplicationName("OpenHCS")
        self.setApplicationVersion(OPENHCS_VERSION)
        self.setOrganizationName("OpenHCS Development Team")
        self.setOrganizationDomain("openhcs.org")

        self.runtime_context = runtime_context
        from openhcs.agent.services.endpoint_function_catalog_service import (
            ZMQFunctionCatalogService,
        )

        self.function_catalog_service = ZMQFunctionCatalogService(
            lambda: self.runtime_context.ui_config.zmq,
        )

        # Shared components
        self.storage_registry = storage_registry
        self.file_manager = FileManager(self.storage_registry)

        # Main window
        self.main_window: "OpenHCSMainWindow" | None = None

        # Setup application
        self._previous_exception_hook = sys.excepthook
        self.setup_application()

        # Install global Shift+Wheel horizontal scrolling
        self._scroll_filter = install_shift_wheel_scrolling(self)
        logger.debug("Installed global Shift+Wheel horizontal scrolling")
        logger.info("OpenHCS PyQt6 application initialized")

    @property
    def ui_config(self):
        return self.runtime_context.ui_config

    def setup_application(self):
        """Setup application-wide configuration."""

        # Start async storage registry initialization in background thread
        def init_storage_registry_background():
            from polystore.base import ensure_storage_registry

            ensure_storage_registry()
            logger.info("Storage registry initialized in background")

        spawn_thread_with_context(
            init_storage_registry_background, name="storage-registry-init"
        )
        logger.info("Storage registry initialization started in background")

        # The state that holds the global config is registered by ``Session``
        # (the main window constructs it); until then the config that
        # ``config_cache`` stored is the global config.
        from objectstate.object_state import ObjectState, ObjectStateRegistry

        ui_state = ObjectState(
            object_instance=self.ui_config,
            scope_id=UIConfig.object_state_scope_id(),
        )
        ObjectStateRegistry.register(ui_state, _skip_snapshot=True)

        # Register pyqt-reactor providers (codegen, logs, function selection, etc.)
        from openhcs.pyqt_gui.services.reactor_providers import (
            register_reactor_providers,
        )

        register_reactor_providers(
            lambda: self.runtime_context.ui_config,
            function_catalog_service=self.function_catalog_service,
        )

        self.setWindowIcon(openhcs_application_icon())

        # Setup exception handling
        sys.excepthook = self.handle_exception

    def create_main_window(self) -> "OpenHCSMainWindow":
        """
        Create and show the main window.

        Returns:
            Created main window
        """
        if self.main_window is None:
            from openhcs.pyqt_gui.main import OpenHCSMainWindow

            self.main_window = OpenHCSMainWindow(
                runtime_context=self.runtime_context,
                function_catalog_service=self.function_catalog_service,
            )

            # Connect application-level signals
            self.main_window.ui_config_changed.connect(self.on_ui_config_changed)

        return self.main_window

    def show_main_window(
        self,
        *,
        on_deferred_initialization_complete: Callable[[], None] | None = None,
        on_deferred_initialization_failed: (
            Callable[[BaseException], None] | None
        ) = None,
    ):
        """Show the main window and schedule its authoritative ready boundary."""
        if self.main_window is None:
            self.create_main_window()

        startup_readiness = MainWindowStartupReadiness(
            self.main_window,
            on_ready=on_deferred_initialization_complete,
            on_failure=on_deferred_initialization_failed,
        )
        self._startup_readiness = startup_readiness
        self.main_window.show()
        self.main_window.raise_()
        self.main_window.activateWindow()

        # Trigger deferred initialization AFTER window is visible
        # This includes log viewer and default windows (pipeline editor)
        def _run_deferred_initialization() -> None:
            try:
                self.main_window.deferred_initialization()
                startup_readiness.deferred_initialization_complete()
            except Exception as error:  # noqa: BLE001 - Qt callback failure boundary
                startup_readiness.fail(error)

        QtCore.QTimer.singleShot(100, _run_deferred_initialization)

    def on_ui_config_changed(self, new_config: UIConfig) -> None:
        self.runtime_context = self.runtime_context.with_ui_config(new_config)
        logger.info("UI configuration updated")

    def handle_exception(self, exc_type, exc_value, exc_traceback):
        """
        Handle uncaught exceptions.

        Args:
            exc_type: Exception type
            exc_value: Exception value
            exc_traceback: Exception traceback
        """
        if issubclass(exc_type, KeyboardInterrupt):
            # Handle Ctrl+C gracefully
            sys.__excepthook__(exc_type, exc_value, exc_traceback)
            return

        # Log the exception
        logger.critical(
            "Uncaught exception", exc_info=(exc_type, exc_value, exc_traceback)
        )

        # Show error dialog
        error_msg = f"An unexpected error occurred:\n\n{exc_type.__name__}: {exc_value}"

        if self.main_window:
            QMessageBox.critical(self.main_window, "Unexpected Error", error_msg)
        else:
            # No main window - application is in invalid state
            raise RuntimeError(
                "Uncaught exception occurred but no main window available for error dialog"
            )

    def run(
        self,
        *,
        on_main_window_ready: Callable[[], None] | None = None,
        on_startup_failure: Callable[[BaseException], None] | None = None,
    ) -> int:
        """
        Run the application.

        Returns:
            Application exit code
        """
        startup_complete = False

        def _startup_ready() -> None:
            nonlocal startup_complete
            self.main_window.start_background_services()
            startup_complete = True
            if on_main_window_ready is not None:
                on_main_window_ready()

        def _startup_failed(error: BaseException) -> None:
            if on_startup_failure is not None:
                on_startup_failure(error)
            self.exit(1)

        try:
            # Show main window
            self.show_main_window(
                on_deferred_initialization_complete=_startup_ready,
                on_deferred_initialization_failed=_startup_failed,
            )

            # Start event loop
            exit_code = self.exec()

            # Ensure clean shutdown
            self.cleanup()

            return exit_code

        except Exception as error:  # noqa: BLE001 - application lifecycle boundary
            logger.exception("Error during application run")
            if not startup_complete and on_startup_failure is not None:
                on_startup_failure(error)
            self.cleanup()
            return 1

    def cleanup(self):
        """Clean up application resources."""
        try:
            logger.info("Starting application cleanup...")

            # Process any remaining events
            self.processEvents()

            # Clean up main window
            if self.main_window is not None:
                # Force close if not already closed
                if not self.main_window.isHidden():
                    self.main_window.close()
                self.main_window.deleteLater()
                self.main_window = None

            self.function_catalog_service.close()

            # exec() has returned, so processEvents() cannot deliver deleteLater.
            # Retire the native window tree while QApplication is still alive.
            self.sendPostedEvents(None, QtCore.QEvent.Type.DeferredDelete)

            # Force garbage collection
            import gc

            gc.collect()

            logger.info("Application cleanup completed")

        except Exception as error:  # noqa: BLE001 - shutdown boundary
            logger.warning("Error during application cleanup: %s", error)
        finally:
            if sys.excepthook == self.handle_exception:
                sys.excepthook = self._previous_exception_hook


if __name__ == "__main__":
    # Don't run directly - use launch.py instead
    print(
        "Use 'python -m openhcs.pyqt_gui' or 'python -m openhcs.pyqt_gui.launch' to start the GUI"
    )
    sys.exit(1)
