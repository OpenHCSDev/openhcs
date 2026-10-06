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
    SourceBindingMatchDimension,
    SourceBindingMatchField,
    SourceBindingMatchMethod,
    SourceBindingMatchPlan,
    SourceBindingOrigin,
    LazySourceBindingsConfig,
    SourceFilterClause,
    SourceFilterMatchType,
    SourceFilterSubject,
    SourceSelector,
)

source_bindings_config = LazySourceBindingsConfig(
    metadata_rules=(
        MetadataExtractionRule(
            source=MetadataSource.FILE_NAME,
            pattern='^(?:plate-(?P<plate>[^_]+)_)?well-(?P<well>[A-P]\\d{2})_site-(?P<site>[^_]+)_channel-(?P<channel>[^.]+)\\.(?:tif|tiff|bmp|png)$'
        ),
    ),
    match_plan=SourceBindingMatchPlan(
        method=SourceBindingMatchMethod.METADATA,
        dimensions=(
            SourceBindingMatchDimension(
                fields=(
                    SourceBindingMatchField(
                        alias='dna',
                        metadata_field='well'
                    ),
                    SourceBindingMatchField(
                        alias='actin',
                        metadata_field='well'
                    )
                )
            ),
            SourceBindingMatchDimension(
                fields=(
                    SourceBindingMatchField(
                        alias='dna',
                        metadata_field='site'
                    ),
                    SourceBindingMatchField(
                        alias='actin',
                        metadata_field='site'
                    )
                )
            )
        )
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
        NamedSourceBinding(
            alias='actin',
            selector=SourceSelector(
                metadata=(
                    MetadataSelector(
                        field='channel',
                        value='ACTIN'
                    ),
                )
            ),
            origin=SourceBindingOrigin.PIPELINE_START,
            component_identity=(
                ComponentSelector(
                    component=AllComponents.CHANNEL,
                    value='ACTIN'
                ),
            )
        )
    ),
    imported_metadata_tables=(
        ImportedMetadataTable(
            location='source_sets.csv',
            joins=(
                ImportedMetadataJoin(
                    image_metadata_field='well',
                    imported_metadata_field='well'
                ),
                ImportedMetadataJoin(
                    image_metadata_field='site',
                    imported_metadata_field='site'
                )
            )
        ),
    ),
    grouping_metadata_fields=(
        'well',
    )
)

from dataclasses import replace
from pathlib import Path
from openhcs.core.source_metadata import SourceVoxelSpacing, SourceVoxelSpacingUnit
from openhcs.core.config import (PipelineConfig, LazyPathPlanningConfig, LazyProcessingConfig, LazyNapariStreamingConfig, LazyStepMaterializationConfig, NapariDimensionMode, NapariVariableSizeHandling)
from openhcs.constants.constants import VariableComponents, GroupBy
from openhcs.constants.input_source import InputSource
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.func_registry import get_function
from openhcs.processing.backends.cellprofiler.intensity import RescaleMethod
from zmqruntime.config import TransportMode
source_bindings_config = replace(source_bindings_config,
    bindings=tuple(replace(b,load_as_monochrome=True) for b in source_bindings_config.bindings),
    source_voxel_spacing=SourceVoxelSpacing(values_zyx=(1.,1.,1.),unit=SourceVoxelSpacingUnit.PIXELS),
    )
pipeline_config=PipelineConfig(source_bindings_config=source_bindings_config,num_workers=2,
    processing_config=LazyProcessingConfig(variable_components=[VariableComponents.SITE],group_by=GroupBy.CHANNEL),
    path_planning_config=LazyPathPlanningConfig(global_output_folder=Path('/run/media/ts/hdd/openhcs-science/next-bbbc007-fresh26-96-after-bbbc013-20261006/BBBC007_FRESH26_96/FINAL_REPAIR05')))
pipeline_steps=[FunctionStep(name='AnalyticalNormalization',func={
    'DNA':(get_function('openhcs:cellprofiler_rescale_intensity'),{'select_the_input_image':'dna','name_the_output_image':'NormalDNA','rescale_method':RescaleMethod.STRETCH,'source_low':0.,'source_high':1.,'dest_low':0.,'dest_high':1.}),
    'ACTIN':(get_function('openhcs:cellprofiler_rescale_intensity'),{'select_the_input_image':'actin','name_the_output_image':'NormalActin','rescale_method':RescaleMethod.STRETCH,'source_low':0.,'source_high':1.,'dest_low':0.,'dest_high':1.})},
    processing_config=LazyProcessingConfig(input_source=InputSource.PIPELINE_START),
    step_materialization_config=LazyStepMaterializationConfig(enabled=True,sub_dir='normalized'),
    napari_streaming_config=LazyNapariStreamingConfig(enabled=False,port=6017,host='127.0.0.1',transport_mode=TransportMode.TCP,persistent=True,channel_mode=NapariDimensionMode.LAYER,variable_size_handling=NapariVariableSizeHandling.SEPARATE_LAYERS))]

from openhcs.processing.backends.cellprofiler.primary_objects import UnclumpMethod, WatershedMethod
from openhcs.processing.backends.cellprofiler.morphology import FillHolesOption
from openhcs.processing.backends.cellprofiler.thresholding import CellProfilerThresholdScope, CellProfilerThresholdMethod
from openhcs.processing.backends.cellprofiler.secondary import SecondaryMethod
from openhcs.processing.backends.cellprofiler.object_images import ImageMode
from openhcs.processing.backends.cellprofiler.outlines import LineMode, OutlineSourceKind
view_config=LazyNapariStreamingConfig(enabled=False,port=6017,host='127.0.0.1',transport_mode=TransportMode.TCP,persistent=True,channel_mode=NapariDimensionMode.LAYER,variable_size_handling=NapariVariableSizeHandling.SEPARATE_LAYERS)
pipeline_steps += [
 FunctionStep(name='Nuclei',func={'DNA':(get_function('openhcs:cellprofiler_identify_primary_objects'),{
  'select_the_input_image':'NormalDNA','name_the_primary_objects_to_be_identified':'Nuclei',
  'min_diameter':10,'max_diameter':50,'exclude_size':True,'exclude_border_objects':False,
  'unclump_method':UnclumpMethod.INTENSITY,'watershed_method':WatershedMethod.INTENSITY,
  'automatic_smoothing':False,'smoothing_filter_size':8,'automatic_suppression':False,'maxima_suppression_size':8.,'low_res_maxima':False,
  'fill_holes':FillHolesOption.AFTER_BOTH,'use_advanced_settings':True,
  'threshold_scope':CellProfilerThresholdScope.ADAPTIVE,'threshold_method':CellProfilerThresholdMethod.MINIMUM_CROSS_ENTROPY,
  'adaptive_window_size':80,'threshold_correction_factor':1.,'threshold_smoothing_scale':1.3488})},napari_streaming_config=view_config),
 FunctionStep(name='Cells',func={'ACTIN':(get_function('openhcs:cellprofiler_identify_secondary_objects'),{
  'select_the_input_image':'NormalActin','select_the_input_objects':'Nuclei','name_the_objects_to_be_identified':'Cells',
  'method':SecondaryMethod.PROPAGATION,'threshold_method':CellProfilerThresholdMethod.MINIMUM_CROSS_ENTROPY,
  'threshold_scope':CellProfilerThresholdScope.GLOBAL,'threshold_correction_factor':.8,
  'regularization_factor':.05,'fill_holes':True,'discard_edge_objects':False})},napari_streaming_config=view_config),
 FunctionStep(name='NucleusLabels',func={'DNA':(get_function('openhcs:cellprofiler_convert_objects_to_image'),{
  'select_the_input_objects':'Nuclei','name_the_output_image':'nucleus_labels','image_mode':ImageMode.UINT16})},
  step_materialization_config=LazyStepMaterializationConfig(enabled=True,sub_dir='nucleus_labels')),
 FunctionStep(name='CellLabels',func={'ACTIN':(get_function('openhcs:cellprofiler_convert_objects_to_image'),{
  'select_the_input_objects':'Cells','name_the_output_image':'cell_labels','image_mode':ImageMode.UINT16})},
  step_materialization_config=LazyStepMaterializationConfig(enabled=True,sub_dir='cell_labels')),
 FunctionStep(name='Geometry',func=(get_function('openhcs:cellprofiler_measure_object_size_shape'),{
  'select_object_sets_to_measure':('Nuclei','Cells'),'calculate_advanced':False,'calculate_zernikes':False}),
  processing_config=LazyProcessingConfig(variable_components=[VariableComponents.SITE,VariableComponents.CHANNEL],group_by=GroupBy.NONE)),
 FunctionStep(name='RawPhotometry',func=(get_function('openhcs:cellprofiler_measure_object_intensity'),{
  'select_object_sets_to_measure':('Nuclei','Cells'),'select_images_to_measure':('dna','actin')}),
  processing_config=LazyProcessingConfig(input_source=InputSource.PIPELINE_START,variable_components=[VariableComponents.SITE,VariableComponents.CHANNEL],group_by=GroupBy.NONE)),
 FunctionStep(name='ResultOutlines',func={'DNA':(get_function('openhcs:cellprofiler_overlay_outlines'),{
  'select_image_on_which_to_display_outlines':'dna','select_objects_to_display':('Nuclei','Cells'),
  'outline_source_kinds':(OutlineSourceKind.OBJECTS,OutlineSourceKind.OBJECTS),
  'outline_colors':('cyan','yellow'),'line_mode':LineMode.INNER,'blank_image':True,'name_the_output_image':'ResultOutlines'})},
  processing_config=LazyProcessingConfig(input_source=InputSource.PIPELINE_START),napari_streaming_config=view_config),
 FunctionStep(name='CombinedOutlines',func={
  'DNA':(get_function('openhcs:cellprofiler_overlay_outlines'),{
   'select_image_on_which_to_display_outlines':'dna','select_objects_to_display':('Nuclei','Cells'),
   'outline_source_kinds':(OutlineSourceKind.OBJECTS,OutlineSourceKind.OBJECTS),'outline_colors':('cyan','yellow'),
   'line_mode':LineMode.INNER,'name_the_output_image':'DNACombined'}),
  'ACTIN':(get_function('openhcs:cellprofiler_overlay_outlines'),{
   'select_image_on_which_to_display_outlines':'actin','select_objects_to_display':('Nuclei','Cells'),
   'outline_source_kinds':(OutlineSourceKind.OBJECTS,OutlineSourceKind.OBJECTS),'outline_colors':('cyan','yellow'),
   'line_mode':LineMode.INNER,'name_the_output_image':'ActinCombined'})},
  processing_config=LazyProcessingConfig(input_source=InputSource.PIPELINE_START),napari_streaming_config=view_config)
]

from openhcs.processing.backends.cellprofiler.feature_enhancement import OperationMethod, EnhanceMethod, SpeckleAccuracy
repair_view=replace(view_config,enabled=True)
enhance=FunctionStep(name='NuclearBackgroundCorrection',func={'DNA':(get_function('openhcs:cellprofiler_enhance_or_suppress_features'),{
 'select_the_input_image':'NormalDNA','name_the_output_image':'CleanDNA',
 'method':OperationMethod.ENHANCE,'enhance_method':EnhanceMethod.SPECKLES,'radius':20.,'speckle_accuracy':SpeckleAccuracy.SLOW})},
 step_materialization_config=LazyStepMaterializationConfig(enabled=True,sub_dir='clean_dna'))
pipeline_steps.insert(1,enhance)
pipeline_steps[2].func['DNA'][1]['select_the_input_image']='CleanDNA'
pipeline_steps[-2].napari_streaming_config=repair_view
pipeline_steps[-1].napari_streaming_config=repair_view
