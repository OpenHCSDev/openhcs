"""Run a pipeline over a remote-sensing dataset in a fresh process.

Executed by ``test_axis_family_witness.py`` as a script: the family is
activated before any kernel module is imported, as a domain entry point does,
so the kernel config, registries and dataset sources see only this family.

``direct`` runs the orchestrator in this process. ``zmq`` submits the same
pipeline to an execution server this process spawns (with worker processes)
and streams the last step's output to a headless napari viewer, then reads
the viewer's state back. Prints one JSON line describing what was written.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np
import tifffile

import openhcs  # noqa: F401  (the product package; activation below replaces its family)
from tests.unit.remote_sensing_witness_domain import RemoteSensing

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


def pipeline_steps(napari_streaming_config=None) -> list:
    from openhcs.core.config import LazyProcessingConfig
    from openhcs.core.steps.function_step import FunctionStep
    from openhcs.processing.backends.analysis.count_cells_simple import (
        count_cells_simple,
    )
    from openhcs.processing.backends.processors.numpy_processor import (
        percentile_normalize,
        stack_percentile_normalize,
    )

    streaming = (
        {} if napari_streaming_config is None
        else {"napari_streaming_config": napari_streaming_config}
    )
    return [
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
            **streaming,
        ),
        FunctionStep(
            func=count_cells_simple,
            processing_config=LazyProcessingConfig(
                variable_components=[RemoteSensing.Date],
                group_by=RemoteSensing.Band,
            ),
        ),
    ]


def run_direct(root: Path, output_root: Path) -> dict:
    from multiprocessing import SimpleQueue

    from objectstate import set_global_config

    from openhcs.core.config import (
        GlobalPipelineConfig,
        LazyPathPlanningConfig,
        PipelineConfig,
    )
    from openhcs.core.dataset_sources.openhcs_format import OpenHCSDatasetSource
    from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
    from openhcs.core.progress import ProgressExecutionContext, set_progress_queue

    queue = SimpleQueue()
    set_progress_queue(queue)
    try:
        set_global_config(
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
            pipeline_definition=pipeline_steps(),
            partition_values=list(SCENES),
            enable_visualizer_override=False,
        )
        results = orchestrator.execute_compiled_bundle(
            execution_bundle=compiled,
            max_workers=1,
            progress_queue=queue,
            progress_context=ProgressExecutionContext(
                execution_id=str(root),
                subject_id=str(root),
            ),
        )
    finally:
        set_progress_queue(None)

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
        **describe_output(output_root),
    }


def run_zmq(
    root: Path, output_root: Path, execution_port: int, viewer_port: int | None
) -> dict:
    from openhcs.core.config import (
        GlobalPipelineConfig,
        LazyNapariStreamingConfig,
        LazyPathPlanningConfig,
        PipelineConfig,
    )
    from openhcs.core.pipeline_document import PipelineDocumentCodec
    from openhcs.runtime.zmq_execution_client import (
        OpenHCSExecutionSubmission,
        ZMQExecutionClient,
    )

    napari = (
        None
        if viewer_port is None
        else LazyNapariStreamingConfig(enabled=True, persistent=True, port=viewer_port)
    )
    client = ZMQExecutionClient(port=execution_port, persistent=False)
    try:
        client.connect(timeout=300)
        response = client.execute_pipeline(
            OpenHCSExecutionSubmission(
                subject_id=str(root),
                pipeline_document=PipelineDocumentCodec.from_values(
                    pipeline_config=PipelineConfig(
                        path_planning_config=LazyPathPlanningConfig(
                            global_output_folder=output_root
                        )
                    ),
                    pipeline_steps=pipeline_steps(napari),
                ),
                # Two spawned worker processes: each must serve this family.
                global_config=GlobalPipelineConfig(num_workers=2, use_threading=False),
            )
        )
    finally:
        client.disconnect()
    if response.get("status") != "complete":
        raise RuntimeError(f"ZMQ execution failed: {response!r}")
    return {
        "partition_values": response["results"]["partition_values"],
        "viewer": None if napari is None else viewer_state(napari),
        **describe_output(output_root),
    }


def viewer_state(napari) -> dict:
    """Read the streamed layers back from the viewer, then shut it down."""

    from openhcs.agent.dto.execution import ExecutionConnectionSpec
    from openhcs.agent.dto.viewer import ViewerWindowStateRequest
    from openhcs.agent.services.viewer_window_service import ViewerWindowService
    from openhcs.runtime.viewer_protocol import (
        ViewerControlMessageRequest,
        ViewerRuntimeEndpoint,
    )
    from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG

    transport = napari.viewer_runtime_config().transport_endpoint
    endpoint = ViewerRuntimeEndpoint(transport, OPENHCS_ZMQ_CONFIG)
    try:
        state = ViewerWindowService().window_state(
            ViewerWindowStateRequest.from_fields(
                connection=ExecutionConnectionSpec(
                    port=transport.port,
                    host=transport.host,
                    transport_mode=transport.transport_mode,
                    persistent=True,
                ),
                timeout_ms=60_000,
                include_component_values=True,
            )
        )
    finally:
        ViewerControlMessageRequest(
            endpoint=endpoint, message_type="force_shutdown", timeout=5.0
        ).send()
        endpoint.wait_until_released(timeout=10.0)
    return {
        "observed": state.observed,
        "errors": [str(error) for error in state.errors],
        "layers": [
            {
                "axis_labels": list(layer.axis_labels),
                "stack_axes": list(layer.stack_axes),
                "item_count": layer.item_count,
                "component_values": [dict(values) for values in layer.component_values],
            }
            for layer in state.layers
        ],
    }


def describe_output(output_root: Path) -> dict:
    from dataclasses import fields

    from openhcs.core.config import GlobalPipelineConfig as Config

    output_dataset = next(output_root.iterdir())
    metadata = json.loads((output_dataset / "openhcs_metadata.json").read_text())
    return {
        "outputs": sorted(
            path.relative_to(output_dataset).as_posix()
            for path in output_dataset.rglob("*.tif")
        ),
        "output_maxima": {
            path.name: int(tifffile.imread(path).max())
            for path in output_dataset.rglob("*.tif")
        },
        "output_subdirectories": {
            name: sorted(record) for name, record in metadata["subdirectories"].items()
        },
        "output_band_labels": metadata["subdirectories"]["images"]["bands"],
        "config_fields": sorted(field.name for field in fields(Config)),
        "measurement_headers": sorted(
            {
                path.read_text().splitlines()[0]
                for path in output_dataset.rglob("*cell_counts*.csv")
            }
        ),
        "loaded_domain_modules": sorted(
            name
            for name in sys.modules
            if name.startswith(
                (
                    "openhcs.microscopes",
                    "openhcs.interop",
                    "openhcs.processing.backends.cellprofiler",
                )
            )
        ),
    }


if __name__ == "__main__":
    work_root = Path(sys.argv[1])
    mode = sys.argv[2]
    dataset_root = work_root / "survey"
    write_dataset(dataset_root)
    if mode == "direct":
        report = run_direct(dataset_root, work_root / "output")
    else:
        report = run_zmq(
            dataset_root,
            work_root / "output",
            int(sys.argv[3]),
            int(sys.argv[4]) if len(sys.argv) > 4 else None,
        )
    print(json.dumps(report))
