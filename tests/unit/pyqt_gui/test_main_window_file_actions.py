"""File-menu routing for whole-workspace dataset code documents."""

from __future__ import annotations

from types import SimpleNamespace

import pytest

from openhcs.core.selection import SelectedAllSelectionMode
from openhcs.pyqt_gui.main import OpenHCSMainWindow


class _PlateManagerProbe:
    def __init__(self) -> None:
        self.selection_modes = []

    def show_dataset_code(self, selection_mode) -> None:
        self.selection_modes.append(selection_mode)


@pytest.mark.parametrize(
    "action, mode",
    (
        (OpenHCSMainWindow.load_orchestrator_configuration, SelectedAllSelectionMode.SELECTED),
        (OpenHCSMainWindow.save_orchestrator_configuration, SelectedAllSelectionMode.ALL),
    ),
)
def test_file_actions_open_the_dataset_code_document(action, mode) -> None:
    plate_manager = _PlateManagerProbe()

    action(SimpleNamespace(plate_manager_widget=plate_manager))

    assert plate_manager.selection_modes == [mode]
