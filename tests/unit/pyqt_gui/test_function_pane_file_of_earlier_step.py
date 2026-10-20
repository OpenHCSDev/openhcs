"""A function pane shows an input-file argument that names an earlier step's file."""

from __future__ import annotations

from objectstate.object_state import ObjectStateRegistry
from pyqt_reactive.widgets.function_pane import FunctionPaneWidget

from openhcs.core.vfs_protocol import OutputFileOf, PlateInputFile


def read_model(image, *, model_file: PlateInputFile):
    return image


def test_pane_builds_and_keeps_an_output_file_of_argument(qapp) -> None:
    ObjectStateRegistry.clear()
    link = OutputFileOf(step="fit", parameter="model_file")
    pane = FunctionPaneWidget(
        (read_model, {"model_file": link}),
        0,
        None,
        scope_id="file-of-earlier-step",
        func_scope_token="function-1",
    )
    pane.show()

    try:
        for _ in range(20):
            qapp.processEvents()

        assert "model_file" in pane.form_manager.widgets
        assert pane.get_current_kwargs()["model_file"] == link
    finally:
        pane.close()
        pane.deleteLater()
        ObjectStateRegistry.clear()
