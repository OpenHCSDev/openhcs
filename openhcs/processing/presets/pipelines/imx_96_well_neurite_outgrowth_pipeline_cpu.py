# Edit this pipeline and save to apply changes

# Automatically collected imports
from openhcs.constants.constants import VariableComponents
from openhcs.constants.input_source import InputSource
from openhcs.core.config import LazyNapariStreamingConfig
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.assemblers.assemble_stack_cupy import (
    assemble_stack_cupy,
)
from openhcs.processing.backends.pos_gen.ashlar_main_cpu import (
    ashlar_compute_tile_positions_cpu,
)
from openhcs.processing.backends.processors.cupy_processor import (
    create_composite,
    stack_percentile_normalize as stack_percentile_normalize_cupy_processor,
    tophat,
)
from openhcs.processing.backends.processors.numpy_processor import mean_projection
from openhcs.processing.backends.processors.torch_processor import (
    stack_percentile_normalize as stack_percentile_normalize_torch_processor,
)

# Pipeline steps
pipeline_steps = []

# Step 1: preprocess1
step_1 = FunctionStep(
    func=[stack_percentile_normalize_cupy_processor, tophat],
    name="preprocess1",
    napari_streaming_config=LazyNapariStreamingConfig(),
)
pipeline_steps.append(step_1)

# Step 2: z_flatten
step_2 = FunctionStep(
    func=mean_projection,
    name="z_flatten",
    variable_components=[VariableComponents.Z_INDEX],
    napari_streaming_config=LazyNapariStreamingConfig(),
)
pipeline_steps.append(step_2)

# Step 3: composite
step_3 = FunctionStep(
    func=create_composite,
    name="composite",
    variable_components=[VariableComponents.CHANNEL],
    napari_streaming_config=LazyNapariStreamingConfig(),
)
pipeline_steps.append(step_3)

# Step 4: find_stitch_positions
step_4 = FunctionStep(
    func=(ashlar_compute_tile_positions_cpu, {"stitch_alpha": 0.2}),
    name="find_stitch_positions",
)
pipeline_steps.append(step_4)

# Step 5: preprocess2
step_5 = FunctionStep(
    func=[stack_percentile_normalize_torch_processor, tophat],
    name="preprocess2",
    input_source=InputSource.PIPELINE_START,
)
pipeline_steps.append(step_5)

# Step 6: assemble
step_6 = FunctionStep(
    func=assemble_stack_cupy,
    name="assemble",
    napari_streaming_config=LazyNapariStreamingConfig(),
)
pipeline_steps.append(step_6)
