"""Domain change events for process-local custom-function declarations."""

from pyqt_reactive.weak_events import WeakCallbackEvent


class CustomFunctionChangedEvent(WeakCallbackEvent[[]]):
    """Notification that the process-local custom-function declarations changed."""


custom_function_changed = CustomFunctionChangedEvent()
