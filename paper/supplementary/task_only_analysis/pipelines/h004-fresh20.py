from pathlib import Path
from openhcs.constants.constants import AllComponents, Microscope, GroupBy, VariableComponents
from openhcs.constants.input_source import InputSource
from openhcs.core.config import PipelineConfig, LazySourceBindingsConfig, LazyStepSourceBindingsConfig, LazyPathPlanningConfig, LazyProcessingConfig, LazyNapariStreamingConfig, LazyWellFilterConfig
from openhcs.core.source_bindings import NamedSourceBinding, SourceSelector, SourceFilterClause, SourceFilterSubject, SourceFilterMatchType, ComponentSelector
from openhcs.core.source_metadata import SourceVoxelSpacing, SourceVoxelSpacingUnit
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.analysis.neurite_outgrowth import neurite_outgrowth_metaxpress_pixels, PixelCellBodySettings, PixelNuclearSettings, PixelOutgrowthSettings, NeuriteIllumination
from zmqruntime.config import TransportMode

pipeline_config = PipelineConfig(
    microscope=Microscope.SOURCE_BINDINGS,
    num_workers=2, use_threading=False,
    well_filter_config=LazyWellFilterConfig(well_filter='paired'),
    path_planning_config=LazyPathPlanningConfig(global_output_folder=Path('/run/media/ts/hdd/openhcs-science/next-h004-retina-fresh20-95-96-20261005/H004_FRESH20_95/repair03'), well_filter=0),
    materialization_results_path=Path('results'), materialize_runtime_artifacts=True,
    source_bindings_config=LazySourceBindingsConfig(
        source_voxel_spacing=SourceVoxelSpacing(values_zyx=(1.0,1.0),unit=SourceVoxelSpacingUnit.PIXELS),
        bindings=(
            NamedSourceBinding(alias='SomaProcess', selector=SourceSelector(filters=(SourceFilterClause(subject=SourceFilterSubject.FILE,match_type=SourceFilterMatchType.EQUALS,value='field_w1.tif'),)),component_identity=(ComponentSelector(AllComponents.WELL,'paired'),ComponentSelector(AllComponents.SITE,'1'),ComponentSelector(AllComponents.CHANNEL,'1'),ComponentSelector(AllComponents.Z_INDEX,'1'),ComponentSelector(AllComponents.TIMEPOINT,'1')),load_as_monochrome=True),
            NamedSourceBinding(alias='NuclearLike', selector=SourceSelector(filters=(SourceFilterClause(subject=SourceFilterSubject.FILE,match_type=SourceFilterMatchType.EQUALS,value='field_w2.tif'),)),component_identity=(ComponentSelector(AllComponents.WELL,'paired'),ComponentSelector(AllComponents.SITE,'1'),ComponentSelector(AllComponents.CHANNEL,'2'),ComponentSelector(AllComponents.Z_INDEX,'1'),ComponentSelector(AllComponents.TIMEPOINT,'1')),load_as_monochrome=True),
        ),
    ),
)
pipeline_steps = [FunctionStep(
    name='PairedPixelSomaOutgrowth',
    func=(neurite_outgrowth_metaxpress_pixels,{
        'neurite_channel_index':0, 'illumination':NeuriteIllumination.FLUORESCENCE,
        'cell_body':PixelCellBodySettings(approximate_max_width=55.0,minimum_area=150.0,intensity_above_local_background=15.0,channel_index=0,minimum_inscribed_diameter_px=10),
        'outgrowth':PixelOutgrowthSettings(maximum_width=6.0,intensity_above_local_background=3.0,minimum_cell_growth_to_log_as_significant=10.0,candidate_threshold_correction_factor=0.04,candidate_hysteresis_seed_correction_factor=None),
        'use_nuclear_stain':True,
        'nuclear_stain':PixelNuclearSettings(channel_index=1,approx_min_width=15.0,approx_max_width=55.0,intensity_above_local_background=20.0),
    }),
    processing_config=LazyProcessingConfig(variable_components=[VariableComponents.CHANNEL],group_by=GroupBy.NONE,input_source=InputSource.PIPELINE_START),
    source_bindings=LazyStepSourceBindingsConfig(enabled=True,bindings=(NamedSourceBinding(alias='SomaProcess'),NamedSourceBinding(alias='NuclearLike'))),
    napari_streaming_config=LazyNapariStreamingConfig(enabled=True,persistent=True,host='127.0.0.1',port=6015,transport_mode=TransportMode.TCP),
)]
