"""Qt dialogs, async execution, theme and config access for the desktop GUI."""

import logging
from pathlib import Path
from typing import Optional

from PyQt6.QtCore import QObject, pyqtSignal
from PyQt6.QtWidgets import QApplication, QFileDialog, QMessageBox, QWidget
from pyqt_reactive.services.async_operation_executor import AsyncOperationExecutor
from pyqt_reactive.services.ui_thread_dispatch import UiThreadDispatcher
from pyqt_reactive.theming import ColorScheme, ThemeManager

from openhcs.core.path_cache import (
    PathCacheKey,
    cache_path,
    get_initial_path,
)

logger = logging.getLogger(__name__)


class GlobalEventBus(QObject):
    """Cross-window pipeline and configuration change signals."""

    pipeline_changed = pyqtSignal(list)  # list[FunctionStep]
    config_changed = pyqtSignal(object)  # config object

    def emit_pipeline_changed(self, pipeline_steps: list):
        self.pipeline_changed.emit(pipeline_steps)

    def emit_config_changed(self, config):
        self.config_changed.emit(config)


class PyQtServiceAdapter:
    """Qt dialogs, async execution, theme and config access for GUI widgets."""

    def __init__(self, main_window: QWidget):
        """
        Initialize the service adapter.

        Args:
            main_window: Main PyQt6 window for dialog parenting
        """
        self.main_window = main_window
        self.app = QApplication.instance()
        self.ui_dispatcher = UiThreadDispatcher()
        self._async_operations = AsyncOperationExecutor(max_workers=4)

        # Initialize theme manager for centralized color management
        self.theme_manager = ThemeManager()

        # Initialize global event bus for cross-window communication
        self.event_bus = GlobalEventBus()

        # Apply dark theme globally to ensure consistent dialog styling
        self._apply_dark_theme()

        logger.debug("PyQt6 service adapter initialized")

    def _apply_dark_theme(self):
        """Apply dark theme globally for consistent dialog styling."""
        try:
            # Create dark color scheme (same as enhanced path widget)
            dark_scheme = ColorScheme()

            # Apply the dark theme globally so all dialogs use consistent styling
            self.theme_manager.apply_color_scheme(dark_scheme)

            logger.debug("Applied dark theme globally for consistent dialog styling")
        except Exception as e:
            logger.warning(f"Failed to apply dark theme: {e}")

    def execute_async_operation(self, async_func, *args, **kwargs):
        """Execute an async operation through the owned worker lifecycle.

        Args:
            async_func: Async function to execute
            *args: Function arguments
            **kwargs: Function keyword arguments
        """
        future = self._async_operations.submit(async_func, *args, **kwargs)

        def log_failure(completed) -> None:
            if completed.cancelled():
                return
            error = completed.exception()
            if error is not None:
                logger.error("Async operation failed: %s", error, exc_info=error)

        future.add_done_callback(log_failure)
        return future

    def close(self):
        """Fence UI dispatch and retire the owned async-operation executor."""

        self.ui_dispatcher.close()
        self._async_operations.close()

    def create_message_box(
        self,
        *,
        icon: QMessageBox.Icon,
        title: str,
        text: str,
        buttons: QMessageBox.StandardButton,
        default_button: QMessageBox.StandardButton,
    ) -> QMessageBox:
        """Build one message box with the current shared application theme."""

        message_box = QMessageBox(self.main_window)
        message_box.setIcon(icon)
        message_box.setWindowTitle(title)
        message_box.setText(text)
        message_box.setStandardButtons(buttons)
        message_box.setDefaultButton(default_button)
        styles = self.get_current_color_scheme().styles
        message_box.setStyleSheet(
            styles.generate_dialog_style() + "\n" + styles.generate_button_style()
        )
        return message_box

    def show_error_dialog(self, error_message: str, title: str = "Error") -> None:
        """
        Show error dialog with error icon.

        Args:
            error_message: Error message to display
            title: Dialog title
        """
        self.create_message_box(
            icon=QMessageBox.Icon.Critical,
            title=title,
            text=error_message,
            buttons=QMessageBox.StandardButton.Ok,
            default_button=QMessageBox.StandardButton.Ok,
        ).exec()

    def show_info_dialog(self, info_message: str, title: str = "Information") -> None:
        """
        Show information dialog.

        Args:
            info_message: Information message to display
            title: Dialog title
        """
        self.create_message_box(
            icon=QMessageBox.Icon.Information,
            title=title,
            text=info_message,
            buttons=QMessageBox.StandardButton.Ok,
            default_button=QMessageBox.StandardButton.Ok,
        ).exec()

    def show_warning_dialog(
        self,
        warning_message: str,
        title: str = "Warning",
    ) -> None:
        """Show a warning dialog through the shared themed owner."""

        self.create_message_box(
            icon=QMessageBox.Icon.Warning,
            title=title,
            text=warning_message,
            buttons=QMessageBox.StandardButton.Ok,
            default_button=QMessageBox.StandardButton.Ok,
        ).exec()

    def show_cached_directory_dialog(
        self,
        cache_key: PathCacheKey,
        title: str = "Select Directory",
        fallback_path: Optional[Path] = None,
        allow_multiple: bool = False,
    ) -> Optional[Path | list[Path]]:
        """
        Show directory dialog with path caching.

        Args:
            cache_key: Cache key for remembering last used path
            title: Dialog title
            fallback_path: Fallback path if no cached path exists
            allow_multiple: If True, allow selecting multiple directories

        Returns:
            Selected directory path(s) or None if cancelled
            - Single Path if allow_multiple=False
            - List[Path] if allow_multiple=True
        """
        # Get cached initial directory
        initial_path = get_initial_path(cache_key, fallback_path)
        initial_dir = str(initial_path)

        try:
            if allow_multiple:
                # Use custom QFileDialog for multi-directory selection.
                # NOTE: DontUseNativeDialog is required for multi-select.
                dialog = QFileDialog(self.main_window, title, initial_dir)
                dialog.setFileMode(QFileDialog.FileMode.Directory)
                dialog.setOption(QFileDialog.Option.DontUseNativeDialog, True)

                # Enable multi-selection in the list/tree views.
                list_view = dialog.findChild(QWidget, "listView")
                if list_view:
                    from PyQt6.QtWidgets import QAbstractItemView

                    list_view.setSelectionMode(
                        QAbstractItemView.SelectionMode.ExtendedSelection
                    )

                tree_view = dialog.findChild(QWidget, "treeView")
                if tree_view:
                    from PyQt6.QtWidgets import QAbstractItemView

                    tree_view.setSelectionMode(
                        QAbstractItemView.SelectionMode.ExtendedSelection
                    )

                # Make the path bar editable so users can paste paths.
                # In the non-native dialog, the path widget is a QComboBox ("lookInCombo").
                try:
                    from PyQt6.QtWidgets import QComboBox

                    look_in = dialog.findChild(QComboBox, "lookInCombo")
                    if look_in:
                        look_in.setEditable(True)
                        line_edit = look_in.lineEdit()
                        if line_edit:
                            line_edit.setPlaceholderText("Paste a path and press Enter")

                            def _jump_to_typed_path() -> None:
                                raw = line_edit.text().strip().strip('"').strip("'")
                                if not raw:
                                    return
                                try:
                                    p = Path(raw).expanduser()
                                    if p.exists() and p.is_dir():
                                        dialog.setDirectory(str(p))
                                except Exception:
                                    # Leave the dialog as-is if the path is invalid.
                                    return

                            line_edit.returnPressed.connect(_jump_to_typed_path)
                except Exception:
                    # If the internal widget names differ across platforms, fail gracefully.
                    pass

                if dialog.exec():
                    selected_paths = [Path(p) for p in dialog.selectedFiles()]
                    if selected_paths:
                        # Cache the first selected directory
                        cache_path(cache_key, selected_paths[0])
                        return selected_paths
                return None
            else:
                # Single directory selection (native dialog)
                dir_path = QFileDialog.getExistingDirectory(
                    self.main_window, title, initial_dir
                )

                if dir_path:
                    selected_path = Path(dir_path)
                    # Cache the selected directory
                    cache_path(cache_key, selected_path)
                    return selected_path

                return None

        except Exception as e:
            logger.error(f"Directory dialog failed: {e}")
            raise

    def get_global_config(self):
        """
        Get global configuration from application.

        Returns:
            Global configuration object
        """
        return self.main_window.pipeline_runtime_config

    def set_global_config(self, config):
        """
        Set global configuration on application.

        Args:
            config: Global configuration object
        """
        self.main_window.set_pipeline_runtime_config(config)

    def get_current_color_scheme(self) -> ColorScheme:
        """
        Get the current color scheme.

        Returns:
            ColorScheme: Current color scheme
        """
        return self.theme_manager.color_scheme

    def get_file_manager(self):
        """
        Get FileManager instance from application.

        Returns:
            FileManager instance
        """
        return self.main_window.file_manager

    def get_event_bus(self) -> GlobalEventBus:
        """Get the global event bus for cross-window communication.

        Returns:
            GlobalEventBus instance
        """
        return self.event_bus
