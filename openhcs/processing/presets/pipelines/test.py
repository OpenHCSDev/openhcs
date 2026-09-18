# Edit this pipeline and save to apply changes

# Automatically collected imports
from openhcs.core.config import LazyNapariStreamingConfig
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.processors.cupy_processor import (
    stack_percentile_normalize,
)
from openhcs.pyclesperanto import gaussian_blur

# Pipeline steps
pipeline_steps = []

# Step 1: Step_1
step_1 = FunctionStep(
    func=[
        (gaussian_blur, {"sigma_x": 1.0, "sigma_y": 1.0}),
        stack_percentile_normalize,
    ],
    name="Step_1",
    napari_streaming_config=LazyNapariStreamingConfig(well_filter="12"),
)
pipeline_steps.append(step_1)
