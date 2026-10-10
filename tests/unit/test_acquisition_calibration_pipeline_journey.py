"""Acquisition calibration survives real preparation, Gaussian and persistence."""

import json
from multiprocessing import SimpleQueue

import numpy as np
import tifffile
from objectstate import ObjectStateRegistry
from objectstate.lazy_factory import ensure_global_config_context

from openhcs.core.config import (
    GlobalPipelineConfig,
    LazyPathPlanningConfig,
    LazyProcessingConfig,
    PipelineConfig,
)
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.progress import set_progress_queue
from openhcs.core.source_metadata import SourceVoxelSpacing, SourceVoxelSpacingUnit
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.processors.numpy_processor import gaussian_blur
from openhcs.domains.microscopy.axes import Microscopy
from openhcs.microscopes.imagexpress import ImageXpressHandler


def test_htd_spacing_survives_gaussian_compile_execute_and_persist(tmp_path):
    plate = tmp_path / "plate"
    image_dir = plate / "TimePoint_1"
    image_dir.mkdir(parents=True)
    (plate / "plate.HTD").write_text(
        '"XSites", 1\n"YSites", 1\n"PixelSizeUM", 0.65'
    )
    pixels = np.random.default_rng(31).integers(0, 1000, (96, 96), dtype=np.uint16)
    filename = "A01_s001_w1_z001_t001.tif"
    tifffile.imwrite(image_dir / filename, pixels)
    ObjectStateRegistry.clear()
    queue = SimpleQueue()
    set_progress_queue(queue)
    try:
        ensure_global_config_context(
            GlobalPipelineConfig,
            GlobalPipelineConfig(
                dataset_source=ImageXpressHandler, num_workers=1, use_threading=True
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
            pipeline_definition=[
                FunctionStep(
                    func=(gaussian_blur, {"sigma": 1}),
                    processing_config=LazyProcessingConfig(
                        variable_components=[Microscopy.ZIndex]
                    ),
                )
            ],
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
        queue.close()
    assert result["A01"].is_success(), result["A01"].error_message
    output = tmp_path / "output" / "plate_openhcs"
    images = list((output / "images").glob("A01*.tif"))
    assert len(images) == 1
    assert tifffile.imread(images[0]).shape == pixels.shape
    expected = SourceVoxelSpacing((0.65, 0.65), SourceVoxelSpacingUnit.MICROMETERS)
    for root in (plate, output):
        document = json.loads((root / "openhcs_metadata.json").read_text())
        sources = [
            values
            for subdir in document["subdirectories"].values()
            for values in subdir["source_metadata"].values()
        ]
        assert sources
        assert all(
            SourceVoxelSpacing.from_source_metadata(values) == expected
            for values in sources
        )
