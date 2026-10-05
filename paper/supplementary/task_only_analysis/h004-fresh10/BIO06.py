from pathlib import Path
from zmqruntime.config import TransportMode
from openhcs.constants.constants import AllComponents, GroupBy, VariableComponents, Microscope
from openhcs.constants.input_source import InputSource
from openhcs.core.config import PipelineConfig, LazyPathPlanningConfig, LazyProcessingConfig, LazyNapariStreamingConfig, NapariDimensionMode
from openhcs.core.source_bindings import LazySourceBindingsConfig, LazyStepSourceBindingsConfig, NamedSourceBinding, SourceSelector, SourceFilterClause, SourceFilterSubject, SourceFilterMatchType, ComponentSelector, SourceBindingOrigin, SourceBindingMatchPlan, SourceBindingMatchMethod
from openhcs.core.source_metadata import SourceVoxelSpacing, SourceVoxelSpacingUnit
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.func_registry import get_function

pipeline_config = PipelineConfig(
    microscope=Microscope.SOURCE_BINDINGS,
    num_workers=1,
    materialization_results_path=Path('results'),
    materialize_runtime_artifacts=True,
    path_planning_config=LazyPathPlanningConfig(global_output_folder=Path('/run/media/ts/hdd/openhcs-science/next-h004-fresh10-89-20261005/H004_FRESH10_89/BIO06'), well_filter=0),
    source_bindings_config=LazySourceBindingsConfig(
        match_plan=SourceBindingMatchPlan(method=SourceBindingMatchMethod.ORDER),
        source_voxel_spacing=SourceVoxelSpacing(values_zyx=(1.0,1.0), unit=SourceVoxelSpacingUnit.RELATIVE),
        bindings=(
            NamedSourceBinding(alias='Process', selector=SourceSelector(filters=(SourceFilterClause(subject=SourceFilterSubject.FILE,match_type=SourceFilterMatchType.EQUALS,value='field_w1.tif'),)), origin=SourceBindingOrigin.PIPELINE_START, component_identity=(ComponentSelector(AllComponents.WELL,'A01'), ComponentSelector(AllComponents.SITE,'1'), ComponentSelector(AllComponents.CHANNEL,'1'), ComponentSelector(AllComponents.Z_INDEX,'1'), ComponentSelector(AllComponents.TIMEPOINT,'1'))),
            NamedSourceBinding(alias='Nuclear', selector=SourceSelector(filters=(SourceFilterClause(subject=SourceFilterSubject.FILE,match_type=SourceFilterMatchType.EQUALS,value='field_w2.tif'),)), origin=SourceBindingOrigin.PIPELINE_START, component_identity=(ComponentSelector(AllComponents.WELL,'A01'), ComponentSelector(AllComponents.SITE,'1'), ComponentSelector(AllComponents.CHANNEL,'2'), ComponentSelector(AllComponents.Z_INDEX,'1'), ComponentSelector(AllComponents.TIMEPOINT,'1')))
        )
    )
)
from openhcs.processing.backends.cellprofiler.primary_objects import UnclumpMethod, WatershedMethod
from openhcs.processing.backends.cellprofiler.morphology import FillHolesOption
from openhcs.processing.backends.cellprofiler.secondary import SecondaryMethod
from openhcs.processing.backends.cellprofiler.thresholding import CellProfilerThresholdScope, CellProfilerThresholdMethod
from openhcs.processing.backends.cellprofiler.feature_enhancement import OperationMethod, EnhanceMethod, NeuriteMethod
from openhcs.core.config import LazyStepMaterializationConfig
from openhcs.processing.backends.cellprofiler.image_geometry import MaskSource
from openhcs.processing.backends.cellprofiler.image_math import ImageMathOperation

def step(name, function_id, kwargs, alias=None, raw=False, checkpoint=False):
    return FunctionStep(name=name, func=(get_function(function_id),kwargs),
        processing_config=LazyProcessingConfig(variable_components=[VariableComponents.CHANNEL if name in ('NuclearAnchors','SignalSomata') else VariableComponents.SITE],group_by=GroupBy.NONE,input_source=InputSource.PIPELINE_START if raw else InputSource.PREVIOUS_STEP),
        source_bindings=LazyStepSourceBindingsConfig(enabled=alias is not None,bindings=(NamedSourceBinding(alias=alias),) if alias else ()),
        step_materialization_config=LazyStepMaterializationConfig(enabled=checkpoint,sub_dir='qa_'+name),
        napari_streaming_config=LazyNapariStreamingConfig(enabled=True,persistent=True,port=6023,transport_mode=TransportMode.TCP,channel_mode=NapariDimensionMode.LAYER))

# BIO01: only pixel-coordinate modules; no fabricated physical pixel size.
pipeline_steps = [
    step('NuclearAnchors','openhcs:cellprofiler_identify_primary_objects', {
        'name_the_primary_objects_to_be_identified':'Nuclei',
        'min_diameter':10,'max_diameter':50,'exclude_size':True,'exclude_border_objects':False,
        'unclump_method':UnclumpMethod.SHAPE,'watershed_method':WatershedMethod.SHAPE,
        'automatic_suppression':False,'maxima_suppression_size':15.0,'low_res_maxima':False,
        'fill_holes':FillHolesOption.AFTER_BOTH,'threshold_method':CellProfilerThresholdMethod.MANUAL,
        'manual_threshold':12.0/255.0,'threshold_smoothing_scale':1.0},'Nuclear',True),
    step('SignalSomata','openhcs:cellprofiler_identify_secondary_objects', {
        'select_the_input_objects':'Nuclei','name_the_objects_to_be_identified':'Somata',
        'method':SecondaryMethod.DISTANCE_B,'distance_to_dilate':8,
        'threshold_method':CellProfilerThresholdMethod.MANUAL,'manual_threshold':12.0/255.0,
        'threshold_smoothing_scale':0.0,'fill_holes':True,'discard_edge_objects':False},'Process',True),
    step('RawProcess','openhcs:cellprofiler_measure_image_intensity', {'calculate_percentiles':True,'percentiles':(10,50,90,99)},'Process',True),
    step('EnhancedProcesses','openhcs:cellprofiler_enhance_or_suppress_features', {
        'method':OperationMethod.ENHANCE,'enhance_method':EnhanceMethod.NEURITES,
        'neurite_method':NeuriteMethod.TUBENESS,'smoothing_value':2.25,'neurite_rescale':True,
        'name_the_output_image':'EnhancedProcesses'},'Process',True,True),
    step('CandidateProcesses','openhcs:cellprofiler_threshold', {
        'select_the_input_image':'EnhancedProcesses','name_the_output_image':'CandidateProcesses',
        'threshold_scope':CellProfilerThresholdScope.ADAPTIVE,'threshold_method':CellProfilerThresholdMethod.OTSU,
        'window_size':128,'smoothing':1.5,'threshold_correction_factor':0.2},checkpoint=True),
    step('StrongRawSupport','openhcs:cellprofiler_threshold', {
        'name_the_output_image':'StrongRawSupport','predefined_threshold':20.0/255.0,'smoothing':0.0},'Process',True,True),
    step('SupportUnion','openhcs:cellprofiler_image_math', {
        'operation':ImageMathOperation.OR,'select_the_first_image':'CandidateProcesses',
        'select_the_second_image':'StrongRawSupport','name_the_output_image':'SupportUnion'},checkpoint=True),
    step('OutsideSomata','openhcs:cellprofiler_mask_image', {
        'select_the_input_image':'SupportUnion','name_the_output_image':'OutsideSomata',
        'mask_source':MaskSource.OBJECTS,'select_object_for_mask':'Somata','invert_mask':True},checkpoint=True),
    step('ProcessMedialAxis','openhcs:cellprofiler_medialaxis', {
        'select_the_input_image':'OutsideSomata','name_the_output_image':'ProcessSkeleton'},checkpoint=True),
    step('ImageSkeletonDiagnostics','openhcs:cellprofiler_measure_image_skeleton', {'select_images_to_measure':('ProcessSkeleton',)}),
    step('SeedRelativeTopology','openhcs:cellprofiler_measure_object_skeleton', {
        'select_the_seed_objects':'Somata','select_the_skeletonized_image':'ProcessSkeleton',
        'fill_small_holes':False},checkpoint=True),
    step('SomaGeometry','openhcs:cellprofiler_measure_object_size_shape', {
        'select_object_sets_to_measure':('Somata',),'calculate_advanced':True,'calculate_zernikes':False},checkpoint=False)
]

