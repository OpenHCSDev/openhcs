from pathlib import Path
from zmqruntime.config import TransportMode
from openhcs.constants.constants import AllComponents, VariableComponents, GroupBy
from openhcs.constants.input_source import InputSource
from openhcs.core.config import (PipelineConfig, LazyProcessingConfig, LazySourceBindingsConfig,
    LazyStepSourceBindingsConfig, LazyPathPlanningConfig, LazyNapariStreamingConfig,
    LazyStepMaterializationConfig)
from openhcs.core.source_bindings import NamedSourceBinding, SourceSelector, ComponentSelector
from openhcs.processing.func_registry import get_function
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.cellprofiler.intensity import RescaleMethod, AutomaticLow, AutomaticHigh
from openhcs.processing.backends.cellprofiler.smoothing import SmoothingMethod
from openhcs.processing.backends.cellprofiler.image_math import ImageMathOperation

payload = Path('/run/media/ts/hdd/openhcs-science/next-retina-h003-fresh26-94-89-20261006/R0010_FRESH26_94')
pipeline_config = PipelineConfig(
    num_workers=2,
    processing_config=LazyProcessingConfig(variable_components=[VariableComponents.SITE], group_by=GroupBy.CHANNEL),
    source_bindings_config=LazySourceBindingsConfig(bindings=tuple(
        NamedSourceBinding(alias=alias, selector=SourceSelector(components=(ComponentSelector(AllComponents.CHANNEL, channel),)))
        for alias, channel in [('RBPMS','1'), ('AF488','2'), ('Hoechst','3')])),
    path_planning_config=LazyPathPlanningConfig(global_output_folder=payload/'repair03', output_dir_suffix='_openhcs'),
    materialize_runtime_artifacts=True,
    napari_streaming_config=LazyNapariStreamingConfig(enabled=False, port=6013, host='127.0.0.1', transport_mode=TransportMode.TCP, persistent=True),
)
pipeline_steps = [
    FunctionStep(name='Normalize acquisition codebook',
        func=(get_function('openhcs:cellprofiler_rescale_intensity'), {
            'rescale_method': RescaleMethod.MANUAL_IO_RANGE,
            'automatic_low': AutomaticLow.CUSTOM, 'automatic_high': AutomaticHigh.CUSTOM,
            'source_low':0.0, 'source_high':1.0, 'dest_low':0.0, 'dest_high':1.0,
            'select_the_input_image':'RBPMS', 'name_the_output_image':'UnitRBPMS'}),
        processing_config=LazyProcessingConfig(input_source=InputSource.PIPELINE_START),
        source_bindings=LazyStepSourceBindingsConfig(enabled=True, bindings=(NamedSourceBinding(alias='RBPMS'),))),
    FunctionStep(name='Suppress fine grain',
        func=(get_function('openhcs:cellprofiler_smooth'), {'smoothing_method':SmoothingMethod.GAUSSIAN_FILTER,
            'auto_object_size':False, 'object_size':20.0, 'select_the_input_image':'UnitRBPMS', 'name_the_output_image':'FineRBPMS'})),
    FunctionStep(name='Estimate broad additive background',
        func=(get_function('openhcs:cellprofiler_smooth'), {'smoothing_method':SmoothingMethod.GAUSSIAN_FILTER,
            'auto_object_size':False, 'object_size':160.0, 'select_the_input_image':'UnitRBPMS', 'name_the_output_image':'BackgroundRBPMS'})),
    FunctionStep(name='Body contrast response',
        func=(get_function('openhcs:cellprofiler_image_math'), {'operation':ImageMathOperation.SUBTRACT,
            'select_the_first_image':'FineRBPMS', 'select_the_second_image':'BackgroundRBPMS',
            'factors':(1.0,1.0), 'truncate_low':True, 'truncate_high':False, 'name_the_output_image':'BodyResponse'}),
        napari_streaming_config=LazyNapariStreamingConfig(enabled=False),
        step_materialization_config=LazyStepMaterializationConfig(enabled=True)),
]

from openhcs.processing.backends.cellprofiler.primary_objects import UnclumpMethod, WatershedMethod
from openhcs.processing.backends.cellprofiler.morphology import FillHolesOption
from openhcs.processing.backends.cellprofiler.thresholding import CellProfilerThresholdMethod
from openhcs.processing.backends.cellprofiler.object_images import ImageMode
from openhcs.processing.backends.cellprofiler.structuring_elements import StructuringElement
pipeline_steps += [
    FunctionStep(name='Join short interruptions in body response', func=(get_function('openhcs:cellprofiler_closing'), {
        'select_the_input_image':'BodyResponse', 'name_the_output_image':'ClosedBodyResponse',
        'structuring_element':StructuringElement.DISK, 'size':8}),
        step_materialization_config=LazyStepMaterializationConfig(enabled=True)),
    FunctionStep(name='RBPMS soma instances', func=(get_function('openhcs:cellprofiler_identify_primary_objects'), {
        'select_the_input_image':'ClosedBodyResponse', 'name_the_primary_objects_to_be_identified':'RBPMS_Somata',
        'min_diameter':35, 'max_diameter':180, 'exclude_size':True, 'exclude_border_objects':False,
        'threshold_method':CellProfilerThresholdMethod.MANUAL, 'manual_threshold':0.015,
        'threshold_smoothing_scale':1.0, 'use_advanced_settings':True,
        'unclump_method':UnclumpMethod.SHAPE, 'watershed_method':WatershedMethod.SHAPE,
        'automatic_smoothing':False, 'smoothing_filter_size':6,
        'automatic_suppression':False, 'maxima_suppression_size':45.0, 'low_res_maxima':False,
        'fill_holes':FillHolesOption.AFTER_BOTH}),
        napari_streaming_config=LazyNapariStreamingConfig(enabled=True),
        step_materialization_config=LazyStepMaterializationConfig(enabled=True)),
    FunctionStep(name='Persist integer instance IDs', func=(get_function('openhcs:cellprofiler_convert_objects_to_image'), {
        'select_the_input_objects':'RBPMS_Somata','name_the_output_image':'SomaInstanceIDs','image_mode':ImageMode.UINT16}),
        step_materialization_config=LazyStepMaterializationConfig(enabled=True)),
    FunctionStep(name='Per soma morphology',func=(get_function('openhcs:cellprofiler_measure_object_size_shape'), {
        'select_object_sets_to_measure':('RBPMS_Somata',),'calculate_advanced':False,'calculate_zernikes':False})),
    FunctionStep(name='Original RBPMS photometry',func=(get_function('openhcs:cellprofiler_measure_object_intensity'), {
        'select_object_sets_to_measure':('RBPMS_Somata',), 'select_images_to_measure':('RBPMS',)}),
        processing_config=LazyProcessingConfig(input_source=InputSource.PIPELINE_START),
        source_bindings=LazyStepSourceBindingsConfig(enabled=True,bindings=(NamedSourceBinding(alias='RBPMS'),))),
]
