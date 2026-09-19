# Edit this pipeline and save to apply changes

# Automatically collected imports
from openhcs.constants.constants import VariableComponents
from openhcs.core.config import LazyNapariStreamingConfig
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.processors.numpy_processor import (
    stack_percentile_normalize,
)
from openhcs.pyclesperanto import crop, top_hat

# Pipeline steps
pipeline_steps = []

# Step 1: crop
step_1 = FunctionStep(
    func=(
        crop,
        {
            "slice_by_slice": True,
            "start_x": 2340,
            "width": 2400,
            "start_y": 100,
            "height": 3500,
        },
    ),
    name="crop",
    variable_components=[VariableComponents.CHANNEL],
)
pipeline_steps.append(step_1)

# Step 2: blur_tophat
step_2 = FunctionStep(
    func={
        "4": [
            (top_hat, {"slice_by_slice": True, "radius_x": 30.0, "radius_y": 30.0}),
            (
                stack_percentile_normalize,
                {"low_percentile": 0.1, "high_percentile": 99.9},
            ),
        ]
    },
    name="blur_tophat",
    napari_streaming_config=LazyNapariStreamingConfig(well_filter="3"),
)
pipeline_steps.append(step_2)
