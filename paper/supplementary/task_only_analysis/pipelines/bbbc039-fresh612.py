from pathlib import Path
from openhcs.constants.constants import GroupBy, Microscope, VariableComponents
from openhcs.constants.input_source import InputSource
from openhcs.core.config import PipelineConfig, LazyProcessingConfig, LazySourceBindingsConfig, LazyStepSourceBindingsConfig, LazyPathPlanningConfig, LazyNapariStreamingConfig, LazyTiffConfig
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.func_registry import get_function
from openhcs.processing.backends.cellprofiler.primary_objects import UnclumpMethod, WatershedMethod
from openhcs.processing.backends.cellprofiler.thresholding import CellProfilerThresholdMethod
from openhcs.processing.backends.cellprofiler.morphology import FillHolesOption
from openhcs.processing.backends.cellprofiler.object_images import ImageMode
from polystore.config import TiffCompression
from zmqruntime.config import TransportMode

# Original declaration adapted with absolute manifest and fullscope plate join.
# Derived OpenHCS source-binding declaration

from openhcs.constants.constants import AllComponents
from openhcs.core.source_bindings import (
    ComponentSelector,
    ImportedMetadataJoin,
    ImportedMetadataTable,
    MetadataExtractionRule,
    MetadataSelector,
    MetadataSource,
    NamedSourceBinding,
    SourceBindingOrigin,
    SourceBindingsConfig,
    SourceFilterClause,
    SourceFilterMatchType,
    SourceFilterSubject,
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
            location='/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc039-preparation-20261002/BBBC039/input/source_manifest.csv',
            joins=(
                ImportedMetadataJoin(image_metadata_field="plate", imported_metadata_field="plate"),
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

pipeline_config = PipelineConfig(
    microscope=Microscope.SOURCE_BINDINGS,
    num_workers=1, use_threading=True,
    source_bindings_config=LazySourceBindingsConfig(
        metadata_rules=source_bindings_config.metadata_rules,
        source_filters=source_bindings_config.source_filters,
        bindings=source_bindings_config.bindings,
        imported_metadata_tables=source_bindings_config.imported_metadata_tables,
        grouping_metadata_fields=source_bindings_config.grouping_metadata_fields),
    processing_config=LazyProcessingConfig(variable_components=[VariableComponents.SITE],group_by=GroupBy.NONE,input_source=InputSource.PREVIOUS_STEP),
    path_planning_config=LazyPathPlanningConfig(global_output_folder=Path('/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc01395-after612-20261004/BBBC039_FRESH612_96/author-workspace/output/results/final_full200'),output_dir_suffix='_final_full200'),
    materialize_runtime_artifacts=True,
    tiff_config=LazyTiffConfig(compression=TiffCompression.DEFLATE,compression_level=1),
)
pipeline_steps = [
    FunctionStep(name='Identify DNA nuclei',func=(get_function('openhcs:cellprofiler_identify_primary_objects'),{
        'select_the_input_image':'dna',
        'name_the_primary_objects_to_be_identified':'Nuclei',
        'min_diameter':10,'max_diameter':80,
        'exclude_size':True,'exclude_border_objects':False,
        'unclump_method':UnclumpMethod.SHAPE,'watershed_method':WatershedMethod.SHAPE,
        'automatic_smoothing':False,'smoothing_filter_size':3,
        'automatic_suppression':False,'maxima_suppression_size':10.0,
        'low_res_maxima':False,'use_advanced_settings':True,
        'threshold_method':CellProfilerThresholdMethod.MINIMUM_CROSS_ENTROPY,
        'threshold_smoothing_scale':1.0,'threshold_correction_factor':1.0,
        'fill_holes':FillHolesOption.AFTER_BOTH}),
        processing_config=LazyProcessingConfig(input_source=InputSource.PIPELINE_START),
        source_bindings=LazyStepSourceBindingsConfig(enabled=True,bindings=(NamedSourceBinding(alias='dna'),))),
    FunctionStep(name='Measure nuclear geometry',func=(get_function('openhcs:cellprofiler_measure_object_size_shape'),{
        'select_object_sets_to_measure':('Nuclei',),'calculate_advanced':False,'calculate_zernikes':False})),
]
