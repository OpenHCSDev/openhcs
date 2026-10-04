from openhcs.core.pipeline.compilation_session import ResolvedPipelineDefinition
import pytest

from openhcs.constants import VariableComponents
from openhcs.constants.input_source import InputSource
from openhcs.core.config import ProcessingConfig, StepMaterializationConfig
from openhcs.core.source_bindings import (
    ComponentSelector,
    NamedSourceBinding,
    SourceSelector,
    StepSourceBindingsConfig,
)
from openhcs.core.steps.function_step import FunctionStep


def _identity(image):
    return image


class StateStub:
    def __init__(self, scope_id="plate::functionstep_0"):
        self.scope_id = scope_id

    def to_object(self):
        raise AssertionError("Resolved pipeline must not call ObjectState.to_object()")


def test_resolved_pipeline_reads_steps_without_object_conversion():
    source_bindings = StepSourceBindingsConfig(
        bindings=(
            NamedSourceBinding(
                alias="OrigBlue",
                selector=SourceSelector(
                    components=(ComponentSelector("channel", "1"),)
                ),
            ),
        )
    )
    step = FunctionStep(
        func=_identity,
        name="identity",
        source_bindings=source_bindings,
        processing_config=ProcessingConfig(
            variable_components=[VariableComponents.SITE],
            group_by=None,
            input_source=InputSource.PIPELINE_START,
        ),
        step_materialization_config=StepMaterializationConfig(enabled=False),
    )
    state = StateStub()

    pipeline = ResolvedPipelineDefinition([step], {0: state})
    assert pipeline.steps[0] is step
    assert pipeline.step_state_map[0] is state
    assert pipeline.steps[0].source_bindings is source_bindings
    assert (
        pipeline.steps[0].processing_config.input_source is InputSource.PIPELINE_START
    )
    assert pipeline.steps[0].processing_config.variable_components == [
        VariableComponents.SITE
    ]


def test_resolved_pipeline_requires_matching_objectstate():
    step = FunctionStep(func=_identity, name="missing")

    with pytest.raises(ValueError, match="missing ObjectState"):
        ResolvedPipelineDefinition([step], {})
