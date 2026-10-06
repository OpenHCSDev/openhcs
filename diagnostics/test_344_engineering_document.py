"""Source-authoring checks only: no data loading, compile, execution or processes."""

from pathlib import Path

from openhcs.constants import AllComponents, GroupBy, Microscope, VariableComponents
from openhcs.core.aligned_image_payload import ImagePayloadExecutionMode
from openhcs.core.artifacts import ArtifactInputPlan, ArtifactOutputPlan, ImageArtifactType
from openhcs.core.callable_contract import CallableContract
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.processing.backends.cellprofiler.intensity import (
    RescaleIntensityModule,
    rescale_intensity,
)
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract


def test_complete_engineering_document_uses_declared_primary_sources():
    source = (
        Path(__file__).resolve().parents[1]
        / "docs/refactor/examples/344-aligned-rescale-engineering.py"
    ).read_text()
    document = PipelineDocumentAuthority.from_source(source)
    assert document.original_source == source
    assert document.pipeline_config.microscope is Microscope.IMAGEXPRESS
    plan = document.pipeline_config.source_bindings_config
    # Each fixture file is 2-D. Z varies across files, not inside each TIFF.
    assert plan.source_stack_components == ()
    assert plan.source_voxel_spacing.values_zyx == (4.0, 0.5, 0.5)
    assert tuple(binding.alias for binding in plan.bindings) == (
        "EngineeringCH1", "EngineeringCH2",
    )
    assert tuple(binding.selector.components[0].value for binding in plan.bindings) == (
        "1", "2",
    )
    (step,) = document.pipeline_steps
    assert step.processing_config.variable_components == [VariableComponents.Z_INDEX]
    assert step.processing_config.group_by is GroupBy.NONE
    assert step.source_bindings.enabled
    func, kwargs = step.func
    # The document authority canonicalizes decorator callables via RegistryService.
    contract = CallableContract.from_callable(func)
    assert CellProfilerModule.require_callable_contract_owner(contract) is RescaleIntensityModule
    assert contract.resolve_canonical_raw_callable() is (
        CallableContract.from_callable(rescale_intensity).resolve_canonical_raw_callable()
    )
    bindings = RescaleIntensityModule.declared_artifact_bindings(
        plan_type=ArtifactInputPlan, artifact_type=ImageArtifactType,
    )
    assert len(bindings) == 2
    assert all(binding.runtime_parameter_name is None for binding in bindings)
    assert tuple(kwargs[binding.require_parameter_name()] for binding in bindings) == (
        "EngineeringCH1", "EngineeringCH2",
    )
    (output,) = RescaleIntensityModule.declared_artifact_bindings(
        plan_type=ArtifactOutputPlan, artifact_type=ImageArtifactType,
    )
    assert kwargs[output.require_parameter_name()] == "EngineeringRescaled"
    assert contract.runtime_image_execution_mode is ImagePayloadExecutionMode.FULL_STACK
    assert contract.metadata.processing_contract is ProcessingContract.PURE_2D
