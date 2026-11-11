"""Small plates and a private execution server for the Cellpose pipeline tests."""

import csv
import io
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

import numpy as np
import tifffile

from objectstate.lazy_factory import ensure_global_config_context
from zmqruntime.execution.responses import (
    ExecutionSubmissionResponse,
    ExecutionWaitResult,
)

from openhcs.core.config import (
    GlobalPipelineConfig,
    LazyPathPlanningConfig,
    LazyVFSConfig,
    MaterializeToDisk,
    PathPlanningConfig,
    PipelineConfig,
    VFSConfig,
)
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.core.steps import FunctionStep
from openhcs.demo.synthetic_data import SyntheticMicroscopyGenerator
from openhcs.microscopes.imagexpress import ImageXpressHandler
from openhcs.processing.backends.lib_registry.derived import cellpose as derived
from openhcs.runtime.zmq_execution_client import (
    OpenHCSExecutionSubmission,
    ZMQExecutionClient,
)

NUCLEI = derived.SegmentationModel.NUCLEI
DIAMETER = 12.0
SUFFIX = "_cellpose"
EXAMPLES = Path(__file__).parents[1] / "examples" / "custom_functions"
CENTRES = ((20, 20), (60, 30), (40, 70), (75, 75), (30, 100), (100, 50), (105, 105), (3, 64))


def _field(seed: int, size: int = 128) -> np.ndarray:
    """Bright blobs on a noisy background, as a 16-bit camera field."""

    rng = np.random.default_rng(seed)
    yy, xx = np.mgrid[:size, :size]
    field = np.zeros((size, size))
    for cy, cx in CENTRES:
        cy, cx = cy + rng.integers(-3, 4), cx + rng.integers(-3, 4)
        field += np.exp(-((yy - cy) ** 2 + (xx - cx) ** 2) / (2 * 6.0**2))
    return (500 + 20000 * field + rng.normal(0, 100, field.shape)).clip(0).astype(np.uint16)


def make_plate(root: Path, *, wells=("A01",), sites: int = 2, z_levels: int = 1) -> Path:
    """An ImageXpress plate of one channel whose pixels are ``_field`` of the file's index."""

    plate = root / "plate"
    with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
        SyntheticMicroscopyGenerator(
            output_dir=str(plate),
            grid_size=(1, sites),
            tile_size=(128, 128),
            overlap_percent=10,
            stage_error_px=1,
            wavelengths=1,
            z_stack_levels=z_levels,
            num_cells=2,
            wells=list(wells),
            format="ImageXpress",
            random_seed=7,
        ).generate_dataset()
    for index, file in enumerate(sorted(plate.rglob("*.tif"))):
        tifffile.imwrite(file, _field(index))
    return plate


def run_pipeline(plate: Path, steps: list[FunctionStep]) -> Path:
    """Compile and run ``steps`` on a private execution server; return the plate's parent."""

    vfs_config = VFSConfig(materialization_backend=MaterializeToDisk)
    global_config = GlobalPipelineConfig(
        num_workers=1,
        dataset_source=ImageXpressHandler,
        use_threading=False,
        path_planning_config=PathPlanningConfig(output_dir_suffix=SUFFIX),
        vfs_config=vfs_config,
    )
    pipeline_config = PipelineConfig(
        path_planning_config=LazyPathPlanningConfig(output_dir_suffix=SUFFIX),
        vfs_config=LazyVFSConfig.from_config(vfs_config),
    )
    ensure_global_config_context(GlobalPipelineConfig, global_config)

    def submission(**compiled) -> OpenHCSExecutionSubmission:
        return OpenHCSExecutionSubmission(
            subject_id=plate,
            pipeline_document=PipelineDocumentCodec.from_values(
                pipeline_config=pipeline_config, pipeline_steps=steps
            ),
            global_config=global_config,
            **compiled,
        )

    with ZMQExecutionClient.with_private_server() as client:
        compile_id = ExecutionSubmissionResponse.from_wire(
            client.submit_compile(submission())
        ).require_execution_id("Cellpose pipeline compilation")
        ExecutionWaitResult.from_wire(
            client.wait_for_completion(compile_id)
        ).require_complete("Cellpose pipeline compilation")
        execution_id = ExecutionSubmissionResponse.from_wire(
            client.submit_pipeline(submission(compile_artifact_id=compile_id))
        ).require_execution_id("Cellpose pipeline execution")
        ExecutionWaitResult.from_wire(
            client.wait_for_completion(execution_id)
        ).require_complete("Cellpose pipeline execution")
    return plate.parent


def source_stack(plate: Path, well: str = "A01") -> np.ndarray:
    return np.stack([tifffile.imread(file) for file in sorted(plate.rglob(f"{well}_*.tif"))])


def one(root: Path, pattern: str) -> Path:
    (found,) = sorted(root.rglob(pattern))
    return found


def table(root: Path, pattern: str) -> list[dict[str, str]]:
    with one(root, pattern).open(newline="") as handle:
        return list(csv.DictReader(handle))


def output(root: Path, artifact: str) -> np.ndarray:
    return tifffile.imread(one(root, f"*{artifact}_step*.{artifact}.tif"))


def cellpose_planes(masks, flows) -> dict[str, np.ndarray]:
    """One direct Cellpose result, shaped as the derived function publishes it."""

    return {
        "cellpose_labels": np.stack(masks),
        "cell_probability": np.stack([flow[2] for flow in flows]),
        "flow_field": np.stack([np.moveaxis(flow[1], 0, -1) for flow in flows]),
        "flow_rgb": np.stack([flow[0] for flow in flows]),
    }


def step(function, **controls) -> FunctionStep:
    return FunctionStep(name=function.__name__, func=(function, controls))
