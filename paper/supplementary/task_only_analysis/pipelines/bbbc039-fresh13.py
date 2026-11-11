# OpenHCS pipeline
# Final full acquisition materialization of qualified candidate05; cell-count acceptance withheld.
from pathlib import Path
from zmqruntime.config import TransportMode
# Derived OpenHCS source-binding declaration

from openhcs.constants.constants import AllComponents
from openhcs.core.source.source_bindings import (
    ComponentSelector,
    ImportedMetadataJoin,
    ImportedMetadataTable,
    MetadataSelector,
    NamedSourceBinding,
    SourceBindingOrigin,
    SourceBindingsConfig,
    SourceSelector,
)

source_bindings_config = SourceBindingsConfig(
    metadata_rules=(
        MetadataExtractionRule(
            source=MetadataSource.FILE_NAME,
            pattern='^(?:plate-(?P<plate>[^_]+)_)?well-(?P<well>[A-P]\\d{2})_site-(?P<site>[^_]+)_channel-(?P<channel>[^.]+)\\.(?:tif|tiff|bmp|png)$'
        ),
    ),
    source_filters=(
        SourceFilterClause(
            subject=SourceFilterSubject.FILE,
            match_type=SourceFilterMatchType.IS_IMAGE
        ),
    ),
    bindings=(
        NamedSourceBinding(
            alias='dna',
            selector=SourceSelector(
                metadata=(
                    MetadataSelector(
                        field='channel',
                        value='DNA'
                    ),
                )
            ),
            origin=SourceBindingOrigin.PIPELINE_START,
            component_identity=(
                ComponentSelector(
                    component=AllComponents.CHANNEL,
                    value='DNA'
                ),
            )
        ),
    ),
    imported_metadata_tables=(
        ImportedMetadataTable(
            location='source_manifest.csv',
            joins=(
                ImportedMetadataJoin(
                    image_metadata_field='well',
                    imported_metadata_field='well'
                ),
                ImportedMetadataJoin(
                    image_metadata_field='site',
                    imported_metadata_field='site'
                ),
                ImportedMetadataJoin(
                    image_metadata_field='channel',
                    imported_metadata_field='channel'
                )
            )
        ),
    ),
    grouping_metadata_fields=(
        'plate',
        'well'
    )
)
# End byte-identical public binding declaration (inlined for native importability).
from openhcs.core.source.source_bindings import ImportedMetadataTable, ImportedMetadataJoin
from openhcs.core.config.pipeline_config import PipelineConfig, LazySourceBindingsConfig, LazyPathPlanningConfig, LazyProcessingConfig, LazyWellFilterConfig, LazyStepSourceBindingsConfig, LazyNapariStreamingConfig
from openhcs.constants.constants import Microscope, GroupBy, VariableComponents
from openhcs.constants.input_source import InputSource
from openhcs.core.source.source_bindings import NamedSourceBinding
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.func_registry import get_function
from openhcs.processing.backends.cellprofiler.primary_objects import UnclumpMethod, WatershedMethod
from openhcs.processing.backends.cellprofiler.morphology import FillHolesOption
from openhcs.processing.backends.cellprofiler.thresholding import CellProfilerThresholdMethod, CellProfilerThresholdScope
from openhcs.processing.backends.cellprofiler.object_images import ImageMode
from openhcs.core.source.source_metadata import (
    MetadataExtractionRule,
    MetadataSource,
    SourceFilterClause,
    SourceFilterMatchType,
    SourceFilterSubject,
    SourceVoxelSpacing,
    SourceVoxelSpacingUnit,
)
pipeline_config = PipelineConfig(
 num_workers=2,
 materialize_runtime_artifacts=True,
 materialization_results_path=Path("results"),
 well_filter_config=LazyWellFilterConfig(well_filter=None),
 microscope=Microscope.SOURCE_BINDINGS,
 source_bindings_config=LazySourceBindingsConfig(
  metadata_rules=source_bindings_config.metadata_rules,
  source_filters=source_bindings_config.source_filters,
  bindings=source_bindings_config.bindings,
  imported_metadata_tables=(ImportedMetadataTable(location="source_manifest.csv",joins=tuple(ImportedMetadataJoin(image_metadata_field=k, imported_metadata_field=k) for k in ("plate","well","site","channel"))),),
  grouping_metadata_fields=source_bindings_config.grouping_metadata_fields,
  source_voxel_spacing=SourceVoxelSpacing(values_zyx=(1.0,1.0),unit=SourceVoxelSpacingUnit.RELATIVE),
 ),
 path_planning_config=LazyPathPlanningConfig(global_output_folder=Path('/run/media/ts/hdd/openhcs-science/next-bbbc039-fresh13-88-after-bbbc013-20261005/BBBC039_FRESH13_88/full200-technical01')),  
 processing_config=LazyProcessingConfig(variable_components=[VariableComponents.SITE],group_by=GroupBy.NONE),
)
pipeline_steps = [
 FunctionStep(
  name="DNA instance segmentation",
  func=(get_function("openhcs:cellprofiler_identify_primary_objects"), {
   "select_the_input_image":"dna", "name_the_primary_objects_to_be_identified":"Nuclei",
   "min_diameter":12, "max_diameter":80, "exclude_size":True, "exclude_border_objects":False,
   "unclump_method":UnclumpMethod.SHAPE, "watershed_method":WatershedMethod.SHAPE,
   "automatic_smoothing":False, "smoothing_filter_size":2,
   "automatic_suppression":False, "maxima_suppression_size":10.0, "low_res_maxima":False,
   "fill_holes":FillHolesOption.AFTER_DECLUMP,
   "use_advanced_settings":True, "threshold_method":CellProfilerThresholdMethod.MINIMUM_CROSS_ENTROPY,
   "threshold_scope":CellProfilerThresholdScope.GLOBAL, "threshold_smoothing_scale":1.0,
   "threshold_correction_factor":1.10, "threshold_min":200.0/65535.0, "threshold_max":1.0,
  }),
  processing_config=LazyProcessingConfig(input_source=InputSource.PIPELINE_START),
  source_bindings=LazyStepSourceBindingsConfig(enabled=True,bindings=(NamedSourceBinding(alias="dna"),)),
  napari_streaming_config=LazyNapariStreamingConfig(enabled=False,host="127.0.0.1",port=6021,transport_mode=TransportMode.TCP,persistent=True,well_filter=['plate-20586-well-A06', 'plate-20585-well-A24', 'plate-20594-well-E08', 'plate-20595-well-F21', 'plate-20630-well-H06', 'plate-20589-well-J11', 'plate-20585-well-N18', 'plate-20607-well-C18', 'plate-20646-well-N12', 'plate-20585-well-F14', 'plate-20625-well-K01', 'plate-20646-well-N21']),
 ),
 FunctionStep(name="Registered object measurements",func=(get_function("openhcs:cellprofiler_measure_object_size_shape"), {
  "select_object_sets_to_measure":("Nuclei",),"calculate_advanced":False,"calculate_zernikes":False,
 })),
 FunctionStep(name="Materialize instance labels",func=(get_function("openhcs:cellprofiler_convert_objects_to_image"), {
  "select_the_input_objects":"Nuclei", "name_the_output_image":"instance_labels", "image_mode":ImageMode.UINT16,
 })),
]
