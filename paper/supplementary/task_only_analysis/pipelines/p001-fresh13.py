"""Final attempted PipelineDocument. Nine development fields; provisional bodies and paths."""
from pathlib import Path
from openhcs.constants.constants import AllComponents, Microscope, VariableComponents, GroupBy
from openhcs.constants.input_source import InputSource
from openhcs.core.config import PipelineConfig, LazyProcessingConfig, LazyPathPlanningConfig, LazyWellFilterConfig, LazyNapariStreamingConfig, NapariDimensionMode
from zmqruntime.config import TransportMode
from openhcs.core.source_bindings import LazySourceBindingsConfig, NamedSourceBinding, SourceSelector, SourceFilterClause, SourceFilterSubject, SourceFilterMatchType, MetadataExtractionRule, MetadataSource, SourceBindingMatchPlan, SourceBindingMatchMethod, SourceBindingMatchDimension, SourceBindingMatchField
from openhcs.core.source_metadata import SourceVoxelSpacing, SourceVoxelSpacingUnit
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.analysis.neurite_outgrowth import neurite_outgrowth_metaxpress, MetaXpressCellBodySettings, MetaXpressOutgrowthSettings, MetaXpressNuclearSettings

aliases=("DAPI", "FITC")
bindings=tuple(NamedSourceBinding(alias=alias,selector=SourceSelector(filters=(SourceFilterClause(subject=SourceFilterSubject.FILE,match_type=SourceFilterMatchType.CONTAINS,value=f"_w{ch}_"),))) for alias,ch in zip(aliases,(1,2)))
match=SourceBindingMatchPlan(method=SourceBindingMatchMethod.METADATA,dimensions=tuple(SourceBindingMatchDimension(fields=tuple(SourceBindingMatchField(alias=a,metadata_field=f) for a in aliases)) for f in ("well","site","z_index","timepoint")))
pipeline_config=PipelineConfig(
 microscope=Microscope.SOURCE_BINDINGS,num_workers=2,
 well_filter_config=LazyWellFilterConfig(well_filter="A01"),
 processing_config=LazyProcessingConfig(variable_components=[VariableComponents.CHANNEL],group_by=GroupBy.NONE,input_source=InputSource.PIPELINE_START),
 source_bindings_config=LazySourceBindingsConfig(
  bindings=bindings,match_plan=match,grouping_metadata_fields=("well",),
  metadata_rules=(MetadataExtractionRule(source=MetadataSource.FILE_NAME,pattern=r"^(?P<well>A01)_s(?P<site>00[1-9])_w(?P<channel>[12])_z(?P<z_index>001)_t(?P<timepoint>001)\.tif$"),),
  source_voxel_spacing=SourceVoxelSpacing(values_zyx=(1.3556,1.3556),unit=SourceVoxelSpacingUnit.MICROMETERS),
  source_spatial_domain=SourceSpatialDomain(origin_yx=(0,0),source_shape_yx=(1024,1024))),
 path_planning_config=LazyPathPlanningConfig(well_filter=0,global_output_folder=Path("/run/media/ts/hdd/openhcs-science/next-bbbc01388-p00196-fresh13-20261005/P001_FRESH13_96/analysis/final-attempt")),
 materialization_results_path=Path("results"),materialize_runtime_artifacts=True)
pipeline_steps=[FunctionStep(name="NeuronalOutgrowth",func=(neurite_outgrowth_metaxpress,{
 "neurite_channel_index":1,"use_nuclear_stain":True,
 "cell_body":MetaXpressCellBodySettings(channel_index=1,approximate_max_width=40.0,minimum_area=60.0,intensity_above_local_background=500.0,minimum_inscribed_diameter_px=6),
 "nuclear_stain":MetaXpressNuclearSettings(channel_index=0,approx_min_width=5.0,approx_max_width=30.0,intensity_above_local_background=300.0),
 "outgrowth":MetaXpressOutgrowthSettings(maximum_width=4.0,intensity_above_local_background=60.0,minimum_cell_growth_to_log_as_significant=10.0,candidate_threshold_correction_factor=0.10,candidate_hysteresis_seed_correction_factor=None)}),
 napari_streaming_config=LazyNapariStreamingConfig(enabled=False,persistent=True,host="127.0.0.1",port=6017,transport_mode=TransportMode.TCP,channel_mode=NapariDimensionMode.LAYER,site_mode=NapariDimensionMode.STACK))]

