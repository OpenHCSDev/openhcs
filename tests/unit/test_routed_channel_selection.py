"""Channel selection must not relabel pixels from a different producer group."""

from multiprocessing import SimpleQueue
from contextlib import nullcontext

import numpy as np
import pytest
import tifffile
from objectstate import ObjectStateRegistry
from objectstate.lazy_factory import ensure_global_config_context

from openhcs.constants import InputSource, Microscope
from openhcs.core.config import (
    AnalysisConsolidationConfig,
    GlobalPipelineConfig,
    LazyPathPlanningConfig,
    LazyProcessingConfig,
    LazyStepMaterializationConfig,
    PipelineConfig,
)
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.progress import set_progress_queue
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.processors.numpy_processor import crop
from openhcs.processing.backends.analysis.count_cells_simple import count_cells_simple


@pytest.fixture
def channel_plate(tmp_path):
    plate = tmp_path / "plate"
    images = plate / "TimePoint_1"
    images.mkdir(parents=True)
    (plate / "plate.HTD").write_text('"XSites", 1\n"YSites", 1\n"PixelSizeUM", 1.0\n')
    for channel in (2, 3):
        tifffile.imwrite(
            images / f"A01_s001_w{channel}_z001_t001.tif",
            np.full((16, 18), channel * 10, dtype=np.uint16),
        )
    return plate


def _execute_steps(plate, steps, output_root):
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
                    global_output_folder=output_root
                )
            ),
        ).initialize()
        compiled = orchestrator.compile_pipelines(
            pipeline_definition=steps,
            well_filter=["A01"],
            enable_visualizer_override=False,
        )
        return orchestrator.execute_compiled_plate(
            execution_bundle=compiled,
            max_workers=1,
            progress_queue=queue,
            progress_context={
                "execution_id": str(output_root),
                "plate_id": str(plate),
                "axis_id": "",
            },
        )
    finally:
        set_progress_queue(None)


@pytest.mark.parametrize("requested_channel", [2, 3])
@pytest.mark.parametrize("restart_from_source", [False, True])
def test_grouped_consumer_requires_its_channel_in_previous_main_flow(
    tmp_path, channel_plate, requested_channel, restart_from_source
):
    identity = (crop, {"width": 18, "height": 16})
    steps = [
        FunctionStep(func=identity),
        FunctionStep(func={"3": identity}),
        FunctionStep(
            func=identity,
            processing_config=LazyProcessingConfig(
                input_source=(
                    InputSource.PIPELINE_START
                    if restart_from_source
                    else InputSource.PREVIOUS_STEP
                )
            ),
        ),
        FunctionStep(func={str(requested_channel): identity}),
    ]
    missing_channel = requested_channel == 2 and not restart_from_source
    outcome = (
        pytest.raises(ValueError, match="No components match")
        if missing_channel
        else nullcontext()
    )
    with outcome:
        result = _execute_steps(channel_plate, steps, tmp_path / "output")
    if not missing_channel:
        assert result["A01"].is_success(), result["A01"].error_message
        outputs = tuple((tmp_path / "output/plate_openhcs/images").glob("*.tif*"))
        assert len(outputs) == 1
        np.testing.assert_array_equal(
            tifffile.imread(outputs[0]), requested_channel * 10
        )


def test_analysis_steps_consolidate_their_own_output_directories(
    tmp_path, channel_plate
):
    steps = [
        FunctionStep(
            func=count_cells_simple,
            step_materialization_config=LazyStepMaterializationConfig(
                enabled=True,
                sub_dir=subdir,
            ),
        )
        for subdir in ("first", "second")
    ]
    result = _execute_steps(channel_plate, steps, tmp_path / "output")
    assert result["A01"].is_success(), result["A01"].error_message
    config = AnalysisConsolidationConfig()
    for subdir in ("first", "second"):
        summary = (
            tmp_path
            / "output/plate_openhcs"
            / f"{subdir}_results"
            / config.output_filename
        )
        assert summary.is_file(), summary
        assert "A01" in summary.read_text()
    global_summary = tmp_path / "output/plate_openhcs" / config.global_summary_filename
    assert global_summary.is_file()
    summary_text = global_summary.read_text()
    assert "Cell Counts Step0" in summary_text
    assert "Cell Counts Step1" in summary_text
    assert not (channel_plate / config.global_summary_filename).exists()
