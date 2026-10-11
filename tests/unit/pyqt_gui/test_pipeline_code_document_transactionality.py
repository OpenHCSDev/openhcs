"""Transactional validation for Pipeline Editor code documents."""

from __future__ import annotations

from contextlib import contextmanager

import pytest

from openhcs.authoring.session.events import PipelineChanged
from openhcs.constants.constants import OrchestratorState
from openhcs.domains.microscopy.axes import Microscopy
from tests.unit.pyqt_gui.session_harness import add_datasets, session_gui


@contextmanager
def _editor(tmp_path):
    """The pipeline editor showing one initialized dataset, with its changes."""

    with session_gui() as gui:
        (scope_id,) = add_datasets(gui.session, tmp_path, "plate")
        gui.session.set_dataset_state(scope_id, OrchestratorState.READY)
        gui.settle()
        changes = []
        gui.session.subscribe(
            lambda record: changes.append(record.event.scope_id)
            if isinstance(record.event, PipelineChanged)
            else None
        )
        yield gui, scope_id, gui.pipeline_editor.code_document_driver(), changes


INVALID_SOURCE = """
from openhcs.core.config import LazyProcessingConfig, PipelineConfig
from openhcs.core.steps.function_step import FunctionStep

pipeline_config = PipelineConfig()
pipeline_steps = [
    FunctionStep(func=[], processing_config=LazyProcessingConfig(group_by='banana'))
]
"""

VALID_SOURCE = """
from openhcs.domains.microscopy.axes import Microscopy
from openhcs.core.config import LazyProcessingConfig, PipelineConfig
from openhcs.core.steps.function_step import FunctionStep

pipeline_config = PipelineConfig()
pipeline_steps = [
    FunctionStep(
        func=[], processing_config=LazyProcessingConfig(group_by=Microscopy.Channel)
    )
]
"""

VALID_DEFAULT_CONFIG_SOURCE = """
from openhcs.domains.microscopy.axes import Microscopy
from openhcs.core.config import LazyProcessingConfig
from openhcs.core.steps.function_step import FunctionStep

pipeline_steps = [
    FunctionStep(
        func=[], processing_config=LazyProcessingConfig(group_by=Microscopy.Channel)
    )
]
"""


def test_invalid_config_is_rejected_before_pipeline_editor_mutation(tmp_path) -> None:
    with _editor(tmp_path) as (gui, scope_id, driver, changes):
        with pytest.raises(TypeError, match="LazyProcessingConfig.group_by"):
            driver.validate_source(INVALID_SOURCE)
        with pytest.raises(TypeError, match="LazyProcessingConfig.group_by"):
            driver.apply_source(INVALID_SOURCE)

        assert gui.session.pipeline_steps(scope_id) == []
        assert changes == []

        driver.validate_source(VALID_SOURCE)
        driver.apply_source(VALID_SOURCE)
        gui.settle()

        (step,) = gui.session.pipeline_steps(scope_id)
        assert step.processing_config.group_by is Microscopy.Channel
        assert gui.pipeline_editor.item_list.count() == 1
        assert changes == [scope_id]


def test_pipeline_editor_accepts_steps_without_pipeline_config(tmp_path) -> None:
    with _editor(tmp_path) as (gui, scope_id, driver, _changes):
        driver.validate_source(VALID_DEFAULT_CONFIG_SOURCE)
        driver.apply_source(VALID_DEFAULT_CONFIG_SOURCE)
        gui.settle()

        assert len(gui.session.pipeline_steps(scope_id)) == 1
        assert gui.pipeline_editor.item_list.count() == 1
