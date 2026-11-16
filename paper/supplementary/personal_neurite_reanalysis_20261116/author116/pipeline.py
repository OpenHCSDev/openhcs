from zmqruntime.config import TransportMode
from pathlib import Path
from openhcs.processing.custom_functions import selected_channel_gaussian_v1, rooted_arbor_compact_v1, coded_well_summary_v1
from openhcs.constants.constants import AllComponents, GroupBy, VariableComponents, Microscope
from openhcs.constants.input_source import InputSource
from openhcs.core.config import NapariDimensionMode, PipelineConfig, LazyWellFilterConfig, LazyProcessingConfig, LazySourceBindingsConfig, LazyPathPlanningConfig, LazyNapariStreamingConfig
from openhcs.core.source_bindings import ComponentSelector, MetadataExtractionRule, MetadataSource, NamedSourceBinding, SourceFilterClause, SourceFilterMatchType, SourceFilterSubject, SourceSelector
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.analysis.neurite_outgrowth import neurite_outgrowth_metaxpress, MetaXpressCellBodySettings, MetaXpressOutgrowthSettings, MetaXpressNuclearSettings

pipeline_config = PipelineConfig(
    microscope=Microscope.SOURCE_BINDINGS,
    well_filter_config=LazyWellFilterConfig(well_filter=["A02","A08","A11","A17","A24","A25","A27","A28","A29","A30","A31","A32","A34","A37","A47","A49","A52","A54","A59","A60"]),
    path_planning_config=LazyPathPlanningConfig(well_filter=None, global_output_folder=Path('/run/media/ts/hdd/openhcs-science/personal-neurite-graphical-three-20261008/P001_GRAPHICAL_116/final-analysis')),
    source_bindings_config=LazySourceBindingsConfig(
        metadata_rules=(MetadataExtractionRule(source=MetadataSource.FILE_NAME, pattern=r'^(?P<Well>A[0-9]{2})_s(?P<Site>[0-9]+)_w(?P<Stain>[12])_z(?P<Z_Index>[0-9]+)_t(?P<Timepoint>[0-9]+)\.tif$'),),
        bindings=(
            NamedSourceBinding(alias='DAPI', selector=SourceSelector(filters=(SourceFilterClause(subject=SourceFilterSubject.FILE,match_type=SourceFilterMatchType.CONTAINS,value='_w1_'),)),component_identity=(ComponentSelector(AllComponents.CHANNEL,'1'),)),
            NamedSourceBinding(alias='FITC', selector=SourceSelector(filters=(SourceFilterClause(subject=SourceFilterSubject.FILE,match_type=SourceFilterMatchType.CONTAINS,value='_w2_'),)),component_identity=(ComponentSelector(AllComponents.CHANNEL,'2'),)),
        ),
        source_voxel_spacing=SourceVoxelSpacing(values_zyx=(1.3556,1.3556)),
    ),
)
pipeline_steps = [FunctionStep(
    name='RootedArborFinal',
    func=[(selected_channel_gaussian_v1, {'channel_index':1, 'sigma':0.7}), (rooted_arbor_compact_v1, {'soma_terminal_shaft_width_um':24.0, 'neurite_channel_index':1, 'use_nuclear_stain':True, 'cell_body':MetaXpressCellBodySettings(approximate_max_width=60.0,minimum_area=50.0,intensity_above_local_background=2000.0,minimum_inscribed_diameter_px=5), 'outgrowth':MetaXpressOutgrowthSettings(maximum_width=4.0,intensity_above_local_background=75.0,candidate_threshold_correction_factor=0.85,candidate_hysteresis_seed_correction_factor=None,enhance_neurites=False), 'nuclear_stain':MetaXpressNuclearSettings(channel_index=0,approx_min_width=5.0,approx_max_width=30.0,intensity_above_local_background=400.0)})],
    processing_config=LazyProcessingConfig(variable_components=[VariableComponents.CHANNEL],group_by=GroupBy.NONE,input_source=InputSource.PIPELINE_START),
    napari_streaming_config=LazyNapariStreamingConfig(enabled=False),
), FunctionStep(name='CodedWellSummaryFinal', func=coded_well_summary_v1)]
