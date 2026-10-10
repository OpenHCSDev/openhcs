"""Run a two-step pipeline over a remote-sensing dataset in a fresh process.

Executed by ``test_axis_family_witness.py`` as a script: the family is
activated before any kernel module is imported, as a domain entry point does,
so the kernel config, registries and dataset sources see only this family.
Prints one JSON line describing what was written.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np
import tifffile

import openhcs  # noqa: F401  (the product package; activation below replaces its family)
from openhcs.core.axes import (
    Axis,
    AxisFamily,
    ColourAxis,
    DefaultGroupBy,
    DefaultVariable,
    LabelValued,
    OrdinalValued,
    PartitionAxis,
    TileAxis,
    TimeAxis,
)


class RemoteSensing(AxisFamily):
    """Scenes in parallel; tiles, spectral bands and acquisition dates within each."""

    class Tile(Axis, TileAxis, DefaultVariable, OrdinalValued):
        name = "tile"
        filename_prefix = "f"
        filename_padding = 3

    class Band(Axis, ColourAxis, DefaultGroupBy, OrdinalValued):
        name = "band"
        filename_prefix = "b"

    class Date(Axis, TimeAxis, OrdinalValued):
        name = "date"
        filename_prefix = "d"
        filename_padding = 3

    class Scene(Axis, PartitionAxis, LabelValued):
        name = "scene"


RemoteSensing.activate()

SCENES = ("S01", "S02")
TILES = ("1", "2")
BANDS = {"1": "red", "2": "nir"}
DATES = ("1", "2", "3")


def write_dataset(root: Path) -> None:
    """Write planes and their openhcsdata record through the kernel writer."""
    from openhcs.core.dataset_sources.openhcs_format import OpenHCSMetadata
    from openhcs.core.source_projection import OpenHCSPlaneAddress
    from openhcs.core.virtual_workspace_metadata import (
        AtomicMetadataWriter,
        get_metadata_path,
    )

    images = root / "images"
    images.mkdir(parents=True)
    image_files = []
    rng = np.random.default_rng(0)
    for scene in SCENES:
        for tile in TILES:
            for band in BANDS:
                for date in DATES:
                    address = OpenHCSPlaneAddress.from_component_values(
                        (
                            (RemoteSensing.Scene, scene),
                            (RemoteSensing.Tile, tile),
                            (RemoteSensing.Band, band),
                            (RemoteSensing.Date, date),
                        )
                    )
                    name = address.filename(".tif")
                    pixels = rng.integers(0, 1000, size=(16, 16), dtype=np.uint16)
                    pixels[0, 0] = 100 * int(date)  # the date maximum is known
                    tifffile.imwrite(images / name, pixels)
                    image_files.append(f"images/{name}")

    labels = {
        RemoteSensing.Scene: {scene: None for scene in SCENES},
        RemoteSensing.Tile: {tile: None for tile in TILES},
        RemoteSensing.Band: dict(BANDS),
        RemoteSensing.Date: {date: None for date in DATES},
    }
    record = OpenHCSMetadata(
        microscope_handler_name="openhcsdata",
        source_filename_parser_name="SourceSchemaFilenameParser",
        grid_dimensions=[1, len(TILES)],
        pixel_size=10.0,
        image_files=image_files,
        axis_value_labels=OpenHCSMetadata.labels_by_field(labels),
        available_backends={"disk": True},
        main=True,
    )
    AtomicMetadataWriter().merge_subdirectory_metadata(
        get_metadata_path(root), {"images": record.to_document()}
    )


def run_pipeline(root: Path, output_root: Path) -> dict:
    from multiprocessing import SimpleQueue

    from objectstate import ObjectStateRegistry
    from objectstate.lazy_factory import ensure_global_config_context

    from openhcs.core.config import (
        GlobalPipelineConfig,
        LazyPathPlanningConfig,
        LazyProcessingConfig,
        PipelineConfig,
    )
    from openhcs.core.dataset_sources.openhcs_format import OpenHCSDatasetSource
    from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
    from openhcs.core.progress import set_progress_queue
    from openhcs.core.steps.function_step import FunctionStep
    from openhcs.processing.backends.processors.numpy_processor import (
        percentile_normalize,
        stack_percentile_normalize,
    )

    steps = [
        FunctionStep(
            func=(percentile_normalize, {"target_max": 1000.0}),
            processing_config=LazyProcessingConfig(
                variable_components=[RemoteSensing.Tile],
                group_by=RemoteSensing.Band,
            ),
        ),
        FunctionStep(
            func=(stack_percentile_normalize, {"target_max": 500.0}),
            processing_config=LazyProcessingConfig(
                variable_components=[RemoteSensing.Date],
                group_by=RemoteSensing.Band,
            ),
        ),
    ]
    ObjectStateRegistry.clear()
    queue = SimpleQueue()
    set_progress_queue(queue)
    try:
        ensure_global_config_context(
            GlobalPipelineConfig,
            GlobalPipelineConfig(num_workers=1, use_threading=True),
        )
        orchestrator = PipelineOrchestrator(
            root,
            pipeline_config=PipelineConfig(
                path_planning_config=LazyPathPlanningConfig(
                    global_output_folder=output_root
                )
            ),
        ).initialize()
        compiled = orchestrator.compile_pipelines(
            pipeline_definition=steps,
            well_filter=list(SCENES),
            enable_visualizer_override=False,
        )
        results = orchestrator.execute_compiled_plate(
            execution_bundle=compiled,
            max_workers=1,
            progress_queue=queue,
            progress_context={
                "execution_id": str(root),
                "plate_id": str(root),
                "axis_id": "",
            },
        )
    finally:
        set_progress_queue(None)

    from dataclasses import fields

    from openhcs.core.config import GlobalPipelineConfig as Config

    output_plate = next(output_root.iterdir())
    metadata = json.loads((output_plate / "openhcs_metadata.json").read_text())
    return {
        "source_type": type(orchestrator.microscope_handler).__name__,
        "is_kernel_source": isinstance(
            orchestrator.microscope_handler, OpenHCSDatasetSource
        ),
        "results": {key: result.is_success() for key, result in results.items()},
        "errors": {
            key: result.error_message
            for key, result in results.items()
            if not result.is_success()
        },
        "outputs": sorted(
            path.relative_to(output_plate).as_posix()
            for path in output_plate.rglob("*.tif")
        ),
        "output_maxima": {
            path.name: int(tifffile.imread(path).max())
            for path in output_plate.rglob("*.tif")
        },
        "output_subdirectories": {
            name: sorted(record) for name, record in metadata["subdirectories"].items()
        },
        "output_band_labels": metadata["subdirectories"]["images"]["bands"],
        "config_fields": sorted(field.name for field in fields(Config)),
        "loaded_domain_modules": sorted(
            name for name in sys.modules if name.startswith("openhcs.microscopes")
        ),
    }


if __name__ == "__main__":
    dataset_root = Path(sys.argv[1]) / "survey"
    write_dataset(dataset_root)
    print(json.dumps(run_pipeline(dataset_root, Path(sys.argv[1]) / "output")))
