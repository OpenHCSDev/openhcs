"""Readable step captions leave the persisted pipeline name unchanged."""

import pytest

from openhcs.core.steps.function_step import FunctionStep
from openhcs.pyqt_gui.widgets.pipeline_editor import PipelineEditorWidget


@pytest.mark.parametrize("index", [None, 0])
@pytest.mark.parametrize(
    ("name", "caption"),
    [
        ("IdentifyPrimaryObjects", "Identify Primary Objects"),
        ("mean_cell_GFP", "Mean Cell GFP"),
        ("User's custom step", "User's custom step"),
    ],
)
def test_step_caption_preserves_the_source_name(
    name: str, caption: str, index: int | None
) -> None:
    step = FunctionStep(name=name)
    display, unnumbered = PipelineEditorWidget._numbered_step_display_name(step, index)
    assert unnumbered == caption
    assert display == (caption if index is None else f"{index + 1}. {caption}")
    assert step.name == name
