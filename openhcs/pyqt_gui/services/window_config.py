"""
Window Configuration - Declarative specs for application windows.

Centralized window definitions replacing hardcoded creation code.
"""

from dataclasses import dataclass
from typing import Type
from PyQt6.QtWidgets import QDialog, QVBoxLayout


class ManagedWindow(QDialog):
    """Base class for managed application windows."""

    def __init__(self, main_window, service_adapter):
        super().__init__(main_window)
        self.main_window = main_window
        self.service_adapter = service_adapter
        self.setup_ui()
        self.setup_connections()

    def setup_ui(self):
        """Setup window UI. Subclasses implement this."""
        pass

    def setup_connections(self):
        """Setup signal connections. Subclasses implement this."""
        pass


@dataclass(frozen=True)
class WindowSpec:
    """
    Declarative specification for an application window.

    Centralizes window configuration (widget, title, size) in one place.
    """

    window_id: str
    title: str
    window_class: Type[ManagedWindow]
    initialize_on_startup: bool = False
