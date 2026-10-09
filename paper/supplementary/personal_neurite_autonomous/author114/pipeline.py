from pathlib import Path
from openhcs.constants.constants import Microscope, VariableComponents, GroupBy
from openhcs.constants.input_source import InputSource
from openhcs.core.config import PipelineConfig, LazyProcessingConfig, LazySourceBindingsConfig, LazyPathPlanningConfig, LazyNapariStreamingConfig
from openhcs.core.source_bindings import MetadataExtractionRule, MetadataSource, NamedSourceBinding, SourceSelector, SourceFilterClause, SourceFilterSubject, SourceFilterMatchType, SourceBindingMatchPlan, SourceBindingMatchMethod, SourceBindingMatchDimension, SourceBindingMatchField
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.analysis.neurite_outgrowth import neurite_outgrowth_metaxpress, MetaXpressCellBodySettings, MetaXpressNuclearSettings, MetaXpressOutgrowthSettings
from zmqruntime.config import TransportMode

pipeline_config = PipelineConfig(
    microscope=Microscope.SOURCE_BINDINGS,
    source_bindings_config=LazySourceBindingsConfig(
        metadata_rules=(MetadataExtractionRule(source=MetadataSource.FILE_NAME, pattern=r"^(?P<well>A[0-9]{2})_s0*(?P<site>[1-9])_w(?P<channel>[12])_z0*(?P<z_index>1)_t0*(?P<timepoint>1)\.tif$"),),
        bindings=(
            NamedSourceBinding(alias="DAPI", selector=SourceSelector(filters=(SourceFilterClause(subject=SourceFilterSubject.FILE, match_type=SourceFilterMatchType.CONTAINS, value="_w1_"),)), load_as_monochrome=True),
            NamedSourceBinding(alias="FITC", selector=SourceSelector(filters=(SourceFilterClause(subject=SourceFilterSubject.FILE, match_type=SourceFilterMatchType.CONTAINS, value="_w2_"),)), load_as_monochrome=True),
        ),
        match_plan=SourceBindingMatchPlan(method=SourceBindingMatchMethod.METADATA, dimensions=tuple(SourceBindingMatchDimension(fields=tuple(SourceBindingMatchField(alias=alias, metadata_field=field) for alias in ("DAPI","FITC"))) for field in ("well","site","z_index","timepoint"))),
        source_voxel_spacing=SourceVoxelSpacing(values_zyx=(1.3556,1.3556)),
    ),
    path_planning_config=LazyPathPlanningConfig(well_filter=0, global_output_folder=Path("/run/media/ts/hdd/openhcs-science/personal-neurite-graphical-three-20261008/P001_GRAPHICAL_114/candidate03")),
    materialization_results_path=Path("results"),
    materialize_runtime_artifacts=True,
)
pipeline_steps = [FunctionStep(
    name="SomaConnectedArbors03",
    func=(neurite_outgrowth_metaxpress, {
        "neurite_channel_index":1,
        "cell_body":MetaXpressCellBodySettings(channel_index=1, approximate_max_width=35.0, minimum_area=40.0, intensity_above_local_background=1000.0, minimum_inscribed_diameter_px=5.0),
        "outgrowth":MetaXpressOutgrowthSettings(maximum_width=4.0, intensity_above_local_background=100.0, candidate_threshold_correction_factor=0.025, candidate_hysteresis_seed_correction_factor=None),
        "use_nuclear_stain":True,
        "nuclear_stain":MetaXpressNuclearSettings(channel_index=0, approx_min_width=4.0, approx_max_width=25.0, intensity_above_local_background=1000.0),
    }),
    processing_config=LazyProcessingConfig(variable_components=[VariableComponents.CHANNEL], group_by=GroupBy.NONE, input_source=InputSource.PIPELINE_START),
    napari_streaming_config=LazyNapariStreamingConfig(enabled=False, persistent=True, port=6071, transport_mode=TransportMode.TCP, colormap="gray"),
)]
