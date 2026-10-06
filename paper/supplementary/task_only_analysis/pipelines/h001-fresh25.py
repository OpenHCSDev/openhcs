from pathlib import Path
from openhcs.constants.constants import AllComponents, GroupBy, VariableComponents
from openhcs.constants.input_source import InputSource
from openhcs.core.config import PipelineConfig, LazyProcessingConfig, LazyPathPlanningConfig, LazyNapariStreamingConfig, LazyStepMaterializationConfig
from openhcs.core.source_bindings import LazySourceBindingsConfig, NamedSourceBinding, SourceSelector, ComponentSelector, SourceBindingOrigin, LazyStepSourceBindingsConfig
from openhcs.processing.backends.cellprofiler.intensity import RescaleMethod
from openhcs.processing.backends.cellprofiler.primary_objects import UnclumpMethod, WatershedMethod
from openhcs.processing.backends.cellprofiler.morphology import FillHolesOption
from openhcs.processing.backends.cellprofiler.thresholding import CellProfilerThresholdMethod, CellProfilerThresholdScope
from openhcs.processing.backends.cellprofiler.object_images import ImageMode
from openhcs.processing.func_registry import get_function
from openhcs.core.steps.function_step import FunctionStep
from zmqruntime.config import TransportMode

pipeline_config = PipelineConfig(
    num_workers=2,
    materialize_runtime_artifacts=True,
    processing_config=LazyProcessingConfig(variable_components=[VariableComponents.SITE], group_by=GroupBy.CHANNEL, input_source=InputSource.PREVIOUS_STEP),
    path_planning_config=LazyPathPlanningConfig(global_output_folder=Path('/run/media/ts/hdd/openhcs-science/next-h001-fresh25-94-after-retina-20261006/H001_FRESH25_ROTATION_94/REPAIR02'), output_dir_suffix='_openhcs'),
    source_bindings_config=LazySourceBindingsConfig(bindings=(
        NamedSourceBinding(alias='Raw', selector=SourceSelector(), origin=SourceBindingOrigin.PIPELINE_START,
                           component_identity=(ComponentSelector(component=AllComponents.CHANNEL, value='1'),), load_as_monochrome=True),
    )),
)

pipeline_steps = [
    FunctionStep(name='ScaleForDetection', func=(get_function('openhcs:cellprofiler_rescale_intensity'), {
        'rescale_method': RescaleMethod.DIVIDE_BY_VALUE, 'divisor_value': 248.0,
        'select_the_input_image': 'Raw', 'name_the_output_image': 'Detection',
    }), source_bindings=LazyStepSourceBindingsConfig(enabled=True, bindings=pipeline_config.source_bindings_config.bindings), step_materialization_config=LazyStepMaterializationConfig(enabled=True)),
    FunctionStep(name='SegmentBrightObjects', func=(get_function('openhcs:cellprofiler_identify_primary_objects'), {
        'min_diameter': 6, 'max_diameter': 40, 'exclude_size': True, 'exclude_border_objects': False,
        'use_advanced_settings': True, 'threshold_scope': CellProfilerThresholdScope.GLOBAL,
        'threshold_method': CellProfilerThresholdMethod.OTSU, 'threshold_smoothing_scale': 1.0,
        'threshold_correction_factor': 1.0, 'threshold_min': 0.0, 'threshold_max': 1.0,
        'unclump_method': UnclumpMethod.SHAPE, 'watershed_method': WatershedMethod.SHAPE,
        'automatic_suppression': False, 'maxima_suppression_size': 15.0, 'low_res_maxima': False,
        'fill_holes': FillHolesOption.AFTER_DECLUMP,
        'select_the_input_image': 'Detection', 'name_the_primary_objects_to_be_identified': 'BrightObjects',
    }), napari_streaming_config=LazyNapariStreamingConfig(enabled=True, port=6013, host='localhost', transport_mode=TransportMode.TCP, persistent=True)),
    FunctionStep(name='MeasurePixelArea', func=(get_function('openhcs:cellprofiler_measure_object_size_shape'), {
        'calculate_advanced': False, 'calculate_zernikes': False, 'select_object_sets_to_measure': ('BrightObjects',),
    })),
    FunctionStep(name='IntegerLabels', func=(get_function('openhcs:cellprofiler_convert_objects_to_image'), {
        'image_mode': ImageMode.UINT16, 'select_the_input_objects': 'BrightObjects', 'name_the_output_image': 'InstanceLabels',
    }), step_materialization_config=LazyStepMaterializationConfig(enabled=True)),
    FunctionStep(name='ExportMeasurements', func=(get_function('openhcs:cellprofiler_export_to_spreadsheet'), {
        'add_filename_prefix': False,
    }), processing_config=LazyProcessingConfig(variable_components=[], group_by=GroupBy.NONE)),
]
