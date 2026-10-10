"""Qt service stand-ins for widgets that render a session in tests."""

from __future__ import annotations

from dataclasses import dataclass, field

from pyqt_reactive.theming import ColorScheme

from openhcs.pyqt_gui.services.service_adapter import GlobalEventBus


@dataclass
class GuiServiceStub:
    """The Qt services a manager widget asks for; dialogs are recorded."""

    errors: list[str] = field(default_factory=list)
    directory_choices: list[str] = field(default_factory=list)
    event_bus: GlobalEventBus = field(default_factory=GlobalEventBus)
    main_window: object | None = None
    global_config: object | None = None

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
