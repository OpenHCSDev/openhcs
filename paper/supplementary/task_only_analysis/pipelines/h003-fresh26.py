from pathlib import Path
from openhcs.constants.constants import AllComponents, GroupBy, VariableComponents, Microscope
from openhcs.constants.input_source import InputSource
from openhcs.core.config import PipelineConfig, NapariDimensionMode, LazyProcessingConfig, LazySourceBindingsConfig, LazyPathPlanningConfig, LazyStepSourceBindingsConfig, LazyNapariStreamingConfig
from openhcs.core.source_bindings import NamedSourceBinding, SourceSelector, SourceFilterClause, SourceFilterSubject, SourceFilterMatchType, ComponentSelector, SourceBindingOrigin, SourceBindingMatchPlan, SourceBindingMatchMethod
from openhcs.core.source_metadata import SourceVoxelSpacing, SourceVoxelSpacingUnit
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.func_registry import get_function
from openhcs.processing.backends.cellprofiler.intensity import RescaleMethod
from zmqruntime.config import TransportMode

pipeline_config = PipelineConfig(
    microscope=Microscope('source_bindings'),
    num_workers=2,
    materialize_runtime_artifacts=True,
    processing_config=LazyProcessingConfig(variable_components=[VariableComponents.SITE],group_by=GroupBy.CHANNEL),
    path_planning_config=LazyPathPlanningConfig(global_output_folder=Path('/run/media/ts/hdd/openhcs-science/next-retina-h003-fresh26-94-89-20261006/H003_FRESH26_89/REPAIR03'),output_dir_suffix='_analysis'),
    source_bindings_config=LazySourceBindingsConfig(
        source_filters=(SourceFilterClause(subject=SourceFilterSubject.FILE,match_type=SourceFilterMatchType.CONTAINS_REGEX,value=r'^A02_s001_w[12]_z001_t001\.tif$'),),
        match_plan=SourceBindingMatchPlan(method=SourceBindingMatchMethod.ORDER),
        source_voxel_spacing=SourceVoxelSpacing(values_zyx=(1.0,1.0),unit=SourceVoxelSpacingUnit('pixels')),
        bindings=(
            NamedSourceBinding(alias='DNA',selector=SourceSelector(filters=(SourceFilterClause(subject=SourceFilterSubject.FILE,match_type=SourceFilterMatchType.EQUALS,value='A02_s001_w1_z001_t001.tif'),)),origin=SourceBindingOrigin.PIPELINE_START,component_identity=(ComponentSelector(AllComponents.WELL,'A02'),ComponentSelector(AllComponents.SITE,'1'),ComponentSelector(AllComponents.CHANNEL,'1'),ComponentSelector(AllComponents.Z_INDEX,'1'),ComponentSelector(AllComponents.TIMEPOINT,'1')),load_as_monochrome=True),
            NamedSourceBinding(alias='Actin',selector=SourceSelector(filters=(SourceFilterClause(subject=SourceFilterSubject.FILE,match_type=SourceFilterMatchType.EQUALS,value='A02_s001_w2_z001_t001.tif'),)),origin=SourceBindingOrigin.PIPELINE_START,component_identity=(ComponentSelector(AllComponents.WELL,'A02'),ComponentSelector(AllComponents.SITE,'1'),ComponentSelector(AllComponents.CHANNEL,'2'),ComponentSelector(AllComponents.Z_INDEX,'1'),ComponentSelector(AllComponents.TIMEPOINT,'1')),load_as_monochrome=True),
        ),
    ),
    napari_streaming_config=LazyNapariStreamingConfig(enabled=False,port=6023,host='127.0.0.1',transport_mode=TransportMode('tcp'),persistent=True,channel_mode=NapariDimensionMode('layer')),
)
from openhcs.processing.backends.cellprofiler.primary_objects import UnclumpMethod, WatershedMethod
from openhcs.processing.backends.cellprofiler.thresholding import CellProfilerThresholdMethod
from openhcs.processing.backends.cellprofiler.morphology import FillHolesOption
from openhcs.processing.backends.cellprofiler.secondary import SecondaryMethod
from openhcs.processing.backends.cellprofiler.object_images import ImageMode

from openhcs.processing.backends.cellprofiler.image_math import ImageMathOperation
from openhcs.processing.backends.cellprofiler.object_filtering import FilterMode, FilterMethod

pipeline_steps = [
    FunctionStep(name='NormalizeDetectionInputs',func={
        '1':(get_function('openhcs:cellprofiler_rescale_intensity'),{'rescale_method':RescaleMethod.STRETCH,'select_the_input_image':'DNA','name_the_output_image':'DNA_norm'}),
        '2':(get_function('openhcs:cellprofiler_rescale_intensity'),{'rescale_method':RescaleMethod.STRETCH,'select_the_input_image':'Actin','name_the_output_image':'Actin_norm'}),
    },processing_config=LazyProcessingConfig(input_source=InputSource.PIPELINE_START),napari_streaming_config=LazyNapariStreamingConfig(enabled=True)),
    FunctionStep(name='IdentifyNuclei',func={'1':(get_function('openhcs:cellprofiler_identify_primary_objects'),{
        'select_the_input_image':'DNA_norm','name_the_primary_objects_to_be_identified':'Nuclei',
        'min_diameter':8,'max_diameter':40,'exclude_size':True,'exclude_border_objects':False,
        'unclump_method':UnclumpMethod.SHAPE,'watershed_method':WatershedMethod.SHAPE,
        'automatic_suppression':False,'maxima_suppression_size':6.0,'low_res_maxima':False,
        'fill_holes':FillHolesOption.AFTER_DECLUMP,'use_advanced_settings':True,
        'threshold_method':CellProfilerThresholdMethod.MANUAL,'manual_threshold':0.10,
        'threshold_smoothing_scale':1.3488,
    })},napari_streaming_config=LazyNapariStreamingConfig(enabled=True)),
    FunctionStep(name='IdentifyCells',func={'2':(get_function('openhcs:cellprofiler_identify_secondary_objects'),{
        'select_the_input_image':'Actin_norm','select_the_input_objects':'Nuclei','name_the_objects_to_be_identified':'CellsCandidate',
        'method':SecondaryMethod.PROPAGATION,'threshold_method':CellProfilerThresholdMethod.MANUAL,
        'manual_threshold':0.06,'threshold_smoothing_scale':0.0,'regularization_factor':0.05,
        'fill_holes':True,'discard_edge_objects':False,
    })},napari_streaming_config=LazyNapariStreamingConfig(enabled=True)),
    FunctionStep(name='MeasureNuclei',func={'1':(get_function('openhcs:cellprofiler_measure_object_size_shape'),{
        'select_object_sets_to_measure':('Nuclei',),'calculate_advanced':False,'calculate_zernikes':False,
    })}),
    FunctionStep(name='MeasureCells',func={'2':(get_function('openhcs:cellprofiler_measure_object_size_shape'),{
        'select_object_sets_to_measure':('CellsCandidate',),'calculate_advanced':False,'calculate_zernikes':False,
    })}),
    FunctionStep(name='MeasureCellGrowth',func={'2':(get_function('openhcs:cellprofiler_calculate_math'),{
        'select_the_numerator_objects':'CellsCandidate','select_the_denominator_objects':'Nuclei',
        'operand1_feature':'AreaShape_Area','operand2_feature':'AreaShape_Area',
        'operation':ImageMathOperation.DIVIDE,'output_name':'CellToNucleusAreaRatio',
    })}),
    FunctionStep(name='FilterSupportedCells',func={'2':(get_function('openhcs:cellprofiler_filter_objects'),{
        'select_the_object_to_filter':'CellsCandidate','name_the_output_objects':'Cells',
        'mode':FilterMode.MEASUREMENTS,'filter_method':FilterMethod.LIMITS,
        'measurement_features':('Math_CellToNucleusAreaRatio',),
        'measurement_min_values':(1.1,),'measurement_max_values':(None,),
        'measurement_use_minimum':(True,),'measurement_use_maximum':(False,),
        'emit_removed_objects':True,'name_the_objects_removed_by_the_filter':'UnsupportedCells',
    })},napari_streaming_config=LazyNapariStreamingConfig(enabled=True)),
    FunctionStep(name='MeasureSupportedCells',func={'2':(get_function('openhcs:cellprofiler_measure_object_size_shape'),{
        'select_object_sets_to_measure':('Cells',),'calculate_advanced':False,'calculate_zernikes':False,
    })}),
    FunctionStep(name='SaveNucleusLabels',func={'1':(get_function('openhcs:cellprofiler_convert_objects_to_image'),{
        'select_the_input_objects':'Nuclei','name_the_output_image':'NucleusLabels','image_mode':ImageMode.UINT16,
    })},napari_streaming_config=LazyNapariStreamingConfig(enabled=True)),
    FunctionStep(name='SaveCellLabels',func={'2':(get_function('openhcs:cellprofiler_convert_objects_to_image'),{
        'select_the_input_objects':'Cells','name_the_output_image':'CellLabels','image_mode':ImageMode.UINT16,
    })},napari_streaming_config=LazyNapariStreamingConfig(enabled=True)),
    FunctionStep(name='ExportTables',func=(get_function('openhcs:cellprofiler_export_to_spreadsheet'),{
        'add_image_file_names':True,'add_filename_prefix':False,
    }),processing_config=LazyProcessingConfig(variable_components=[],group_by=GroupBy.NONE)),
]
