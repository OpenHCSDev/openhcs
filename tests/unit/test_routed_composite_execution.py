"""An image reduction must replace the routed source planes in main flow."""

from multiprocessing import SimpleQueue

import numpy as np
import pytest
import tifffile
from objectstate import ObjectStateRegistry
from objectstate.lazy_factory import ensure_global_config_context

from openhcs.constants import InputSource, Microscope, VariableComponents
from openhcs.core.config import (
    GlobalPipelineConfig,
    LazyPathPlanningConfig,
    LazyProcessingConfig,
    PipelineConfig,
)
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.progress import set_progress_queue
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.assemblers.assemble_stack_cpu import assemble_stack_cpu
from openhcs.processing.backends.analysis.multi_template_matching import (
    multi_template_crop_reference_channel,
)
from openhcs.processing.backends.pos_gen.ashlar_main_cpu import (
    ashlar_compute_tile_positions_cpu,
)
from openhcs.processing.backends.processors.numpy_processor import (
    create_composite,
    crop,
    tophat,
)


@pytest.mark.parametrize("channels", [(1, 2), (2, 3)])
@pytest.mark.parametrize("preprocess", [False, True])
@pytest.mark.parametrize(
    "stitch,reduce_channels", [(False, False), (False, True), (True, True)]
)
@pytest.mark.parametrize("finish_with_crop", [False, True])
def test_reduced_channel_stack_is_the_next_steps_only_input(
    tmp_path, channels, preprocess, stitch, reduce_channels, finish_with_crop
):
    plate = tmp_path / "plate"
    images = plate / "TimePoint_1"
    images.mkdir(parents=True)
    (plate / "plate.HTD").write_text('"XSites", 1\n"YSites", 1\n"PixelSizeUM", 1.0\n')
    for channel in range(1, 5):
        tifffile.imwrite(
            images / f"A01_s001_w{channel}_z001_t001.tif",
            np.full((16, 18), channel * 10, dtype=np.uint16),
        )
    identity = (crop, {"width": 18, "height": 16, "depth": 1})
    stack_function = (
        create_composite
        if reduce_channels
        else (crop, {"width": 18, "height": 16, "depth": len(channels)})
    )
    steps = [
        FunctionStep(func={str(channel): identity for channel in channels}),
        FunctionStep(
            func=[tophat, stack_function] if preprocess else stack_function,
            processing_config=LazyProcessingConfig(
                variable_components=[VariableComponents.CHANNEL]
            ),
        ),
        FunctionStep(func=identity),
    ]
    if stitch:
        steps[2:] = [
            FunctionStep(func=ashlar_compute_tile_positions_cpu),
            FunctionStep(
                func=identity,
                processing_config=LazyProcessingConfig(
                    input_source=InputSource.PIPELINE_START
                ),
            ),
            FunctionStep(func=assemble_stack_cpu),
        ]
    if finish_with_crop:
        template = tmp_path / "template.tif"
        tifffile.imwrite(template, np.ones((8, 8), dtype=np.uint8))
        steps.append(
            FunctionStep(
                func=(
                    multi_template_crop_reference_channel,
                    {"template_path": str(template), "rotate_result": False},
                ),
                processing_config=LazyProcessingConfig(
                    variable_components=[VariableComponents.CHANNEL]
                ),
            )
        )
    ObjectStateRegistry.clear()
    ensure_global_config_context(
        GlobalPipelineConfig,
        GlobalPipelineConfig(
            microscope=Microscope.IMAGEXPRESS, num_workers=1, use_threading=True
        ),
    )
    queue = SimpleQueue()
    set_progress_queue(queue)
    try:
        orchestrator = PipelineOrchestrator(
            plate,
            pipeline_config=PipelineConfig(
                path_planning_config=LazyPathPlanningConfig(
                    global_output_folder=tmp_path / "output"
                )
            ),
        ).initialize()
        compiled = orchestrator.compile_pipelines(
            pipeline_definition=steps,
            well_filter=["A01"],
            enable_visualizer_override=False,
        )
        context = compiled.runtime_contexts["A01"]
        if not reduce_channels:
            assert not context.step_plans[2].execution_group_scope.is_ungrouped
        if stitch:
            context = compiled.runtime_contexts["A01"]
            assert context.step_plans[2].main_input_dependency.source_step_index == 1
            assert context.step_plans[2].execution_group_scope.is_ungrouped
        result = orchestrator.execute_compiled_plate(
            execution_bundle=compiled,
            max_workers=1,
            progress_queue=queue,
            progress_context={
                "execution_id": str(tmp_path),
                "plate_id": str(plate),
                "axis_id": "",
            },
        )
    finally:
        set_progress_queue(None)
    assert result["A01"].is_success(), result["A01"].error_message
    outputs = list((tmp_path / "output/plate_openhcs/images").glob("*.tif*"))
    assert len(outputs) == (
        4 if stitch else 1 if reduce_channels else len(channels)
    ), outputs
    for output in outputs:
        channel = int(output.name.split("_w")[1].split("_")[0])
        expected = (
            channel * 10
            if stitch
            else (
                0
                if preprocess
                else (np.mean(channels) if reduce_channels else channel) * 10
            )
        )
        # Assembly blends in float32 before converting back to integer pixels.
        np.testing.assert_allclose(
            tifffile.imread(output),
            np.full((8, 8) if finish_with_crop else (16, 18), expected),
            rtol=0,
            atol=1 if stitch else 0,
        )
