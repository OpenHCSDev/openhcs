# OpenHCS pipeline
# Corrected engineering recipe; predecessor failure remains in Git/receipts.
from pathlib import Path
from openhcs.constants import AllComponents, GroupBy, Microscope, VariableComponents
from openhcs.constants.input_source import InputSource
from openhcs.core.artifacts import ArtifactInputPlan, ArtifactOutputPlan, ImageArtifactType
from openhcs.core.config import LazyPathPlanningConfig, LazyProcessingConfig, LazyVFSConfig, MaterializationBackend, PipelineConfig
from openhcs.core.source_bindings import ComponentSelector, LazySourceBindingsConfig, LazyStepSourceBindingsConfig, MetadataExtractionRule, MetadataSource, NamedSourceBinding, SourceBindingMatchDimension, SourceBindingMatchField, SourceBindingMatchMethod, SourceBindingMatchPlan, SourceFilterClause, SourceFilterMatchType, SourceFilterSubject, SourceSelector
from openhcs.core.source_metadata import SourceVoxelSpacing, SourceVoxelSpacingUnit
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.cellprofiler.intensity import RescaleIntensityModule, rescale_intensity

primary_binding, reference_binding = RescaleIntensityModule.declared_artifact_bindings(plan_type=ArtifactInputPlan, artifact_type=ImageArtifactType)
(output_binding,) = RescaleIntensityModule.declared_artifact_bindings(plan_type=ArtifactOutputPlan, artifact_type=ImageArtifactType)

pipeline_config = PipelineConfig(
    num_workers=1,
    use_threading=False,
    microscope=Microscope.IMAGEXPRESS,
    materialization_results_path=Path("results"),
    path_planning_config=LazyPathPlanningConfig(
        global_output_folder=Path("/home/ts/wt/openhcs-344-engineering-20261001/output"),
        output_dir_suffix="_openhcs",
    ),
    vfs_config=LazyVFSConfig(materialization_backend=MaterializationBackend.DISK),
    source_bindings_config=LazySourceBindingsConfig(
        source_filters=(SourceFilterClause(SourceFilterSubject.EXTENSION, SourceFilterMatchType.IS_TIF),),
        metadata_rules=(MetadataExtractionRule(
            MetadataSource.FILE_NAME,
            r"(?P<well>A01)_s0*(?P<site>[1-9][0-9]*)_w(?P<channel>[1-9][0-9]*)_z0*(?P<z_index>[1-9][0-9]*)_t0*(?P<timepoint>[1-9][0-9]*)\.tif$",
        ),),
        match_plan=SourceBindingMatchPlan(
            method=SourceBindingMatchMethod.METADATA,
            dimensions=tuple(SourceBindingMatchDimension(fields=tuple(
                SourceBindingMatchField(alias=alias, metadata_field=field)
                for alias in ("EngineeringCH1", "EngineeringCH2")
            )) for field in ("well", "site", "z_index", "timepoint")),
        ),
        source_voxel_spacing=SourceVoxelSpacing((4.0, 0.5, 0.5), SourceVoxelSpacingUnit.MICROMETERS),
        bindings=(
            NamedSourceBinding(alias="EngineeringCH1", selector=SourceSelector(components=(ComponentSelector(AllComponents.CHANNEL, "1"), ComponentSelector(AllComponents.SITE, "1"))), component_identity=(ComponentSelector(AllComponents.CHANNEL, "1"),)),
            NamedSourceBinding(alias="EngineeringCH2", selector=SourceSelector(components=(ComponentSelector(AllComponents.CHANNEL, "2"), ComponentSelector(AllComponents.SITE, "1"))), component_identity=(ComponentSelector(AllComponents.CHANNEL, "2"),)),
        ),
    ),
)
pipeline_steps = [
    FunctionStep(
        name="Engineering aligned full-stack RescaleIntensity",
        func=(rescale_intensity, {
            primary_binding.require_parameter_name(): "EngineeringCH1",
            reference_binding.require_parameter_name(): "EngineeringCH2",
            output_binding.require_parameter_name(): "EngineeringRescaled",
        }),
        processing_config=LazyProcessingConfig(input_source=InputSource.PIPELINE_START, variable_components=[VariableComponents.Z_INDEX], group_by=GroupBy.NONE),
        source_bindings=LazyStepSourceBindingsConfig(enabled=True),
    ),
]
