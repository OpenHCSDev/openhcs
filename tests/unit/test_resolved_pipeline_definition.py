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
from openhcs.core.function_patterns import normalize_function_pattern


def _identity(image):
    return image


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
    scope = "plate::functionstep_0"

    pipeline = ResolvedPipelineDefinition([step], {0: scope}, step_provenance={0: {}})
    assert pipeline.steps[0].name == step.name
    assert step.func is _identity
    assert next(normalize_function_pattern(pipeline.steps[0].func).iter_items()).func is _identity
    assert pipeline.step_scope_ids[0] == scope
    assert pipeline.steps[0].source_bindings is source_bindings
    assert (
        pipeline.steps[0].processing_config.input_source is InputSource.PIPELINE_START
    )
    assert pipeline.steps[0].processing_config.variable_components == [
        VariableComponents.SITE
    ]


def test_resolved_pipeline_requires_matching_scope():
    step = FunctionStep(func=_identity, name="missing")

    with pytest.raises(ValueError, match="missing scope/provenance facts"):
        ResolvedPipelineDefinition([step], {}, step_provenance={})
