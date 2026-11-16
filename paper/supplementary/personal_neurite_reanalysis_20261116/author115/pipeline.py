from pathlib import Path
from openhcs.constants.constants import Microscope, GroupBy, VariableComponents
from openhcs.constants.input_source import InputSource
from openhcs.core.config import LazyCompilationDebugConfig, LazyNapariStreamingConfig, PipelineConfig, LazySourceBindingsConfig, LazyPathPlanningConfig, LazyProcessingConfig
from openhcs.core.source_bindings import MetadataExtractionRule, MetadataSource, NamedSourceBinding, SourceSelector, SourceFilterClause, SourceFilterSubject, SourceFilterMatchType, SourceBindingOrigin, SourceBindingMatchPlan, SourceBindingMatchMethod, SourceBindingMatchDimension, SourceBindingMatchField
from openhcs.core.source_metadata import SourceVoxelSpacing, SourceVoxelSpacingUnit
pipeline_config = PipelineConfig(
    microscope=Microscope.SOURCE_BINDINGS,
    num_workers=2,
    compilation_debug_config=LazyCompilationDebugConfig(enabled=True,compiled_execution_bundle_path=Path('/run/media/ts/hdd/openhcs-science/personal-neurite-graphical-three-20261008/P001_GRAPHICAL_115/final-attempt/source-plate_openhcs/compiled.bundle.pkl')),
    materialize_runtime_artifacts=True,
    materialization_results_path=Path('/run/media/ts/hdd/openhcs-science/personal-neurite-graphical-three-20261008/P001_GRAPHICAL_115/final-attempt/source-plate_openhcs/results'),
    path_planning_config=LazyPathPlanningConfig(global_output_folder=Path('/run/media/ts/hdd/openhcs-science/personal-neurite-graphical-three-20261008/P001_GRAPHICAL_115/final-attempt'), well_filter=0),
    processing_config=LazyProcessingConfig(variable_components=[VariableComponents.CHANNEL],group_by=GroupBy.NONE,input_source=InputSource.PIPELINE_START),
    source_bindings_config=LazySourceBindingsConfig(
        metadata_rules=(MetadataExtractionRule(source=MetadataSource.FILE_NAME, pattern=r'^(?P<well>A\d{2})_s0*(?P<site>[1-9])_w(?P<channel>[12])_z0*(?P<z_index>1)_t0*(?P<timepoint>1)\.tif$'),),
        source_filters=(SourceFilterClause(subject=SourceFilterSubject.EXTENSION,match_type=SourceFilterMatchType.IS_IMAGE),),
        bindings=(
            NamedSourceBinding(alias='DAPI',selector=SourceSelector(filters=(SourceFilterClause(subject=SourceFilterSubject.FILE,match_type=SourceFilterMatchType.CONTAINS,value='_w1_'),)),origin=SourceBindingOrigin.PIPELINE_START,load_as_monochrome=True),
            NamedSourceBinding(alias='FITC',selector=SourceSelector(filters=(SourceFilterClause(subject=SourceFilterSubject.FILE,match_type=SourceFilterMatchType.CONTAINS,value='_w2_'),)),origin=SourceBindingOrigin.PIPELINE_START,load_as_monochrome=True),
        ),
        match_plan=SourceBindingMatchPlan(method=SourceBindingMatchMethod.METADATA,dimensions=(
            SourceBindingMatchDimension(fields=(SourceBindingMatchField(alias='DAPI',metadata_field='well'),SourceBindingMatchField(alias='FITC',metadata_field='well'))),
            SourceBindingMatchDimension(fields=(SourceBindingMatchField(alias='DAPI',metadata_field='site'),SourceBindingMatchField(alias='FITC',metadata_field='site'))),
            SourceBindingMatchDimension(fields=(SourceBindingMatchField(alias='DAPI',metadata_field='z_index'),SourceBindingMatchField(alias='FITC',metadata_field='z_index'))),
            SourceBindingMatchDimension(fields=(SourceBindingMatchField(alias='DAPI',metadata_field='timepoint'),SourceBindingMatchField(alias='FITC',metadata_field='timepoint'))),
        )),
        source_voxel_spacing=SourceVoxelSpacing(values_zyx=(1.3556,1.3556),unit=SourceVoxelSpacingUnit.MICROMETERS),
    ),
)
from openhcs.core.steps.function_step import FunctionStep
from zmqruntime.config import TransportMode
from openhcs.processing.backends.analysis.neurite_outgrowth import neurite_outgrowth_metaxpress, MetaXpressCellBodySettings, MetaXpressOutgrowthSettings
from openhcs.processing.backends.processors.numpy_processor import gaussian_blur
pipeline_steps = [FunctionStep(
    name="FITCSomaConnectedArbor",
    func=[(gaussian_blur, dict(sigma=0.8)), (neurite_outgrowth_metaxpress, dict(
        neurite_channel_index=1,
        use_nuclear_stain=False,
        cell_body=MetaXpressCellBodySettings(approximate_max_width=35.0, minimum_area=40.0, intensity_above_local_background=500.0, channel_index=1, minimum_inscribed_diameter_px=4.0),
        outgrowth=MetaXpressOutgrowthSettings(maximum_width=4.0, intensity_above_local_background=100.0, minimum_cell_growth_to_log_as_significant=10.0, candidate_threshold_correction_factor=0.7, enhance_neurites=False),
    ))],
    napari_streaming_config=LazyNapariStreamingConfig(enabled=False,persistent=True,port=6073,transport_mode=TransportMode.TCP,colormap="magenta"),
)]
