"""Real compiler, runtime and TIFF persistence for native stack cropping."""

from multiprocessing import SimpleQueue

import cv2
import numpy as np
import pytest
import tifffile
from objectstate import ObjectStateRegistry
from objectstate.lazy_factory import ensure_global_config_context

from openhcs.constants import GroupBy, Microscope, VariableComponents
from openhcs.core.config import (
    GlobalPipelineConfig,
    LazyPathPlanningConfig,
    LazyProcessingConfig,
    PipelineConfig,
)
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.progress import set_progress_queue
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.analysis.multi_template_matching import (
    OpenCVTemplateMatchMethod,
    multi_template_crop,
    multi_template_crop_reference_channel,
    multi_template_crop_subset,
)
from openhcs.processing.backends.processors.numpy_processor import crop


@pytest.mark.parametrize(
    "function,kwargs,channels,input_channels",
    [
        (multi_template_crop, {}, (1, 2), 2),
        (multi_template_crop_reference_channel, {}, (1, 2), 2),
        (multi_template_crop_subset, {}, (1, 2), 2),
        (multi_template_crop_subset, {"target_channels": [1]}, (2,), 2),
        (multi_template_crop_subset, {"target_channels": [1, 0]}, (2, 1), 2),
        (multi_template_crop, {}, (1,), 1),
        (multi_template_crop_reference_channel, {}, (1,), 1),
        (multi_template_crop_subset, {}, (1,), 1),
    ],
)
@pytest.mark.parametrize("first_step", [False, True])
def test_template_crop_persists_each_source_channel(
    function, kwargs, channels, input_channels, first_step, tmp_path
):
    plate = tmp_path / "plate"
    image_dir = plate / "TimePoint_1"
    image_dir.mkdir(parents=True)
    (plate / "plate.HTD").write_text(
        "\n".join(('"XSites", 1', '"YSites", 1', '"PixelSizeUM", 1.0'))
    )
    image = np.random.default_rng(31).integers(0, 256, (32, 42), dtype=np.uint8)
    template = image[5:17, 7:23].copy()
    template_path = tmp_path / "template.tif"
    assert cv2.imwrite(str(template_path), template)
    for channel in range(1, input_channels + 1):
        pixels = np.clip(image.astype(np.int16) + (channel - 1) * 5, 0, 255).astype(
            np.uint8
        )
        tifffile.imwrite(image_dir / f"A01_s001_w{channel}_z001_t001.tif", pixels)

    processing = LazyProcessingConfig(
        variable_components=[VariableComponents.CHANNEL], group_by=GroupBy.SITE
    )
    steps = [
        FunctionStep(
            func=(crop, {"width": 42, "height": 32, "depth": input_channels}),
            processing_config=processing,
        ),
        FunctionStep(
            func=(
                function,
                {
                    "template_path": template_path,
                    "method": OpenCVTemplateMatchMethod.SQDIFF_NORMED,
                    "normalize_input": False,
                    "rotate_result": False,
                    **kwargs,
                },
            ),
            processing_config=processing,
        ),
    ]
    if first_step:
        steps = steps[1:]
    ObjectStateRegistry.clear()
    queue = SimpleQueue()
    set_progress_queue(queue)
    try:
        ensure_global_config_context(
            GlobalPipelineConfig,
            GlobalPipelineConfig(
                microscope=Microscope.IMAGEXPRESS, num_workers=1, use_threading=True
            ),
        )
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
    images = sorted((tmp_path / "output" / "plate_openhcs" / "images").glob("A01*.tif"))
    assert len(images) == len(channels), images
    assert {path.name for path in images} == {
        f"A01_s001_w{channel}_z001_t001_cropped_stack.tif" for channel in channels
    }
    for path in images:
        channel = int(path.name.split("_w")[1].split("_")[0])
        expected = np.clip(
            template.astype(np.int16) + (channel - 1) * 5, 0, 255
        ).astype(np.uint8)
        np.testing.assert_array_equal(tifffile.imread(path), expected)
