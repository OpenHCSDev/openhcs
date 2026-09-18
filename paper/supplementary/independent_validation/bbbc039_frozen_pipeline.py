# OpenHCS pipeline

from openhcs.core.config import (
    LazyNapariStreamingConfig,
    PipelineConfig,
)
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.cellprofiler.primary_objects import identify_primary_objects
from openhcs.processing.backends.cellprofiler.shape import measure_object_size_shape
from pathlib import Path
from zmqruntime.config import TransportMode

pipeline_config = PipelineConfig(
    materialization_results_path=Path('/home/ts/code/projects/openhcs/mcp_outputs/slas-validation-20260915/trials/BBBC039/sol-independent-03/native_outputs'),
    materialize_runtime_artifacts=True
)

pipeline_steps = [
    FunctionStep(
        func=(identify_primary_objects, {
                'exclude_border_objects': False
            }),
        name='Segment nuclei',
        napari_streaming_config=LazyNapariStreamingConfig(
            enabled=True,
            persistent=True,
            host='127.0.0.1',
            transport_mode=TransportMode.TCP,
            port=5643
        )
    ),
    FunctionStep(
        func=(measure_object_size_shape, {
                'calculate_advanced': False,
                'calculate_zernikes': False
            }),
        name='Measure nuclei area and centroid'
    )
]
