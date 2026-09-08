from types import SimpleNamespace

import pytest
from zmqruntime.startup import EndpointStartupPhase, EndpointStartupStatus

from openhcs.agent.ui_bridge_actions import (
    CompilationActionProjection,
    PlateManagerAction,
)
from openhcs.pyqt_gui.widgets.plate_manager import PlateManagerWidget
from openhcs.pyqt_gui.services.ui_bridge_plate_manager import PlateManagerActionProvider
from PyQt6.QtWidgets import QPushButton


@pytest.mark.parametrize(
    "phase, expected",
    [
        (EndpointStartupPhase.DISCONNECTED, PlateManagerAction.CONNECT_SERVER),
        (EndpointStartupPhase.FAILED, PlateManagerAction.CONNECT_SERVER),
        (EndpointStartupPhase.CONNECTED, PlateManagerAction.COMPILE_PLATE),
        *[
            (phase, PlateManagerAction.CONNECTING_SERVER)
            for phase in EndpointStartupPhase
            if phase
            not in {
                EndpointStartupPhase.DISCONNECTED,
                EndpointStartupPhase.FAILED,
                EndpointStartupPhase.CONNECTED,
            }
        ],
    ],
)
def test_endpoint_phase_projects_compile_action(phase, expected):
    assert (
        CompilationActionProjection.from_status(EndpointStartupStatus(phase, "test"))
        is expected
    )


def test_connect_needs_no_plate_and_startup_is_disabled():
    assert PlateManagerAction.CONNECT_SERVER.selection_enabled(False)
    assert not PlateManagerAction.CONNECTING_SERVER.selection_enabled(True)
    assert not PlateManagerAction.COMPILE_PLATE.selection_enabled(False)
    assert PlateManagerAction.COMPILE_PLATE.selection_enabled(True)


def test_action_route_resolves_again_when_endpoint_changes():
    async def connect():
        pass

    async def compile_plate():
        pass

    manager = SimpleNamespace(
        compilation_action=PlateManagerAction.CONNECT_SERVER,
        ensure_execution_server=connect,
        action_compile_plate=compile_plate,
    )
    route = PlateManagerWidget.ACTION_ROUTES[PlateManagerAction.COMPILE_PLATE]
    assert route.resolve_callable(manager) is connect
    manager.compilation_action = PlateManagerAction.COMPILE_PLATE
    assert route.resolve_callable(manager) is compile_plate
    manager.compilation_action = PlateManagerAction.CONNECT_SERVER
    assert route.resolve_callable(manager) is connect


def test_connection_variants_share_existing_button():
    assert len(PlateManagerWidget.BUTTON_CONFIGS) == 9
    assert PlateManagerAction.CONNECT_SERVER not in PlateManagerWidget.ACTION_ROUTES
    assert PlateManagerAction.CONNECTING_SERVER not in PlateManagerWidget.ACTION_ROUTES


def test_mcp_connect_action_has_no_compile_selection_precondition(qapp):
    button = QPushButton()
    manager = SimpleNamespace(
        compilation_action=PlateManagerAction.CONNECT_SERVER,
        ACTION_ROUTES=PlateManagerWidget.ACTION_ROUTES,
        get_selected_items=lambda: [],
        buttons={PlateManagerAction.COMPILE_PLATE.value: button},
    )
    provider = PlateManagerActionProvider(manager)
    connected = provider.summary(PlateManagerAction.COMPILE_PLATE.value)
    assert connected.title == "Connect"
    assert connected.enabled
    assert connected.side_effects == ("connects_or_starts_execution_server",)
    manager.compilation_action = PlateManagerAction.COMPILE_PLATE
    compiled = provider.summary(PlateManagerAction.COMPILE_PLATE.value)
    assert compiled.title == "Compile"
    assert not compiled.enabled
    assert compiled.disabled_error.code == "plate_selection_required"
