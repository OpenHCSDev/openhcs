"""Qt projection of process-local custom-function domain changes."""

from PyQt6.QtCore import QObject, pyqtSignal

from openhcs.processing.custom_functions.events import custom_function_changed


class CustomFunctionSignals(QObject):
    """Project domain changes through Qt's thread-aware signal delivery."""

    functions_changed = pyqtSignal()

    def __init__(self) -> None:
        super().__init__()
        subscription = custom_function_changed.subscribe(self._emit_functions_changed)
        self.destroyed.connect(subscription.cancel)

    def _emit_functions_changed(self) -> None:
        """Project one live domain notification through the Qt adapter."""

        self.functions_changed.emit()


custom_function_signals = CustomFunctionSignals()
