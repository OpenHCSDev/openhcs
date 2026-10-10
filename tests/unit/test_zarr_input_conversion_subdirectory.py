"""Zarr input conversion of a prepared workspace whose images live in a subdirectory."""

from __future__ import annotations

import json
import queue
from pathlib import Path

from objectstate.lazy_factory import ensure_global_config_context

from openhcs.constants.constants import Backend
from openhcs.core.config import (
    GlobalPipelineConfig,
    LazyVFSConfig,
    MaterializationBackend,
    PipelineConfig,
    VFSConfig,
)
from openhcs.core.dataset_sources.choice import DatasetSourceChoice
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.progress import set_progress_queue
from openhcs.core.steps import FunctionStep
from openhcs.core.axes import AxisFamily
from openhcs.demo.synthetic_data import SyntheticMicroscopyGenerator
from openhcs.processing.backends.processors.numpy_processor import (
    stack_percentile_normalize,
)


def _prepared_workspace_plate(root: Path) -> Path:
    generator = SyntheticMicroscopyGenerator(
        output_dir=str(root),
        grid_size=(1, 1),
        tile_size=(16, 16),
        overlap_percent=0,
        wavelengths=1,
        z_stack_levels=2,
        num_cells=0,
        wells=["A01"],
        format="ImageXpress",
        include_all_components=True,
        random_seed=1,
    )
    generator.generate_dataset()
    generator.generate_openhcs_metadata(sub_dir="TimePoint_1")
    return root


def test_zarr_conversion_keys_store_outputs_by_plate_relative_virtual_path(tmp_path):
    """Store paths are relative to the source subdirectory; virtual paths are not."""
    plate = _prepared_workspace_plate(tmp_path / "plate")
    ensure_global_config_context(
        GlobalPipelineConfig,
        GlobalPipelineConfig(
            num_workers=1,
            use_threading=True,
            dataset_source=DatasetSourceChoice.named("openhcsdata"),
            vfs_config=VFSConfig(materialization_backend=MaterializationBackend.ZARR),
        ),
    )
    orchestrator = PipelineOrchestrator(
        plate,
        pipeline_config=PipelineConfig(
            vfs_config=LazyVFSConfig(materialization_backend=MaterializationBackend.ZARR)
        ),
    ).initialize()
    wells = orchestrator.get_component_keys(AxisFamily.active().partition_axis())
    progress_queue = queue.Queue()
    set_progress_queue(progress_queue)
    try:
        bundle = orchestrator.compile_pipelines(
            pipeline_definition=[FunctionStep(func=stack_percentile_normalize)],
            well_filter=wells,
        )
        results = orchestrator.execute_compiled_plate(
            execution_bundle=bundle,
            progress_queue=progress_queue,
            progress_context={
                "execution_id": "zarr-conversion-subdirectory",
                "plate_id": str(plate),
                "axis_id": "",
            },
        )
    finally:
        set_progress_queue(None)
    assert all(result.is_success() for result in results.values()), results

    subdirectories = json.loads((plate / "openhcs_metadata.json").read_text())[
        "subdirectories"
    ]
    assert subdirectories["TimePoint_1"]["main"] is False
    converted = subdirectories["zarr"]
    assert converted["main"] is True
    source_files = {
        Path(path).name for path in subdirectories["TimePoint_1"]["image_files"]
    }
    assert {Path(path).name for path in converted["image_files"]} == source_files
    assert all(path.startswith("zarr/") for path in converted["image_files"])
    assert {
        record["ref"]["backend"] for record in converted["source_projection"]
    } == {Backend.ZARR.value}
