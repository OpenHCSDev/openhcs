"""Compile and execute a real pipeline in this process on a one-field plate."""

from __future__ import annotations

import io
from collections.abc import Iterator
from contextlib import contextmanager, redirect_stderr, redirect_stdout
from dataclasses import dataclass
from multiprocessing import SimpleQueue
from pathlib import Path

import numpy as np
import tifffile
from objectstate import ObjectStateRegistry
from objectstate.lazy_factory import ensure_global_config_context

from openhcs.core.compiled_execution import CompiledExecutionBundle
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.config import (
    GlobalPipelineConfig,
    LazyPathPlanningConfig,
    PipelineConfig,
)
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.progress import ProgressExecutionContext, set_progress_queue
from openhcs.core.steps import FunctionStep
from openhcs.demo.synthetic_data import SyntheticMicroscopyGenerator

SIDE = 128
NUCLEUS_CENTRES = ((30, 30), (30, 90), (90, 40), (95, 100))


def nuclei_image() -> np.ndarray:
    """One field with four bright blobs on a flat background."""
    yy, xx = np.mgrid[:SIDE, :SIDE]
    image = np.full((SIDE, SIDE), 200.0)
    for centre_y, centre_x in NUCLEUS_CENTRES:
        image += 3000.0 * np.exp(
            -((yy - centre_y) ** 2 + (xx - centre_x) ** 2) / (2 * 6.0**2)
        )
    return image.astype(np.uint16)


@dataclass(frozen=True)
class PipelineRun:
    """What one compile-and-execute left behind."""

    compiled: CompiledExecutionBundle
    output_root: Path

    @property
    def step_plans(self) -> dict[int, CompiledStepPlan]:
        """The compiled step plans of the one well."""
        [context] = self.compiled.runtime_contexts.values()
        return context.step_plans

    @property
    def results_dir(self) -> Path:
        """The folder holding the written analysis results."""
        [results_dir] = self.output_root.glob("*/results")
        return results_dir

    def output_images(self) -> list[np.ndarray]:
        """Every image file the pipeline wrote outside the results folder."""
        return [
            tifffile.imread(path)
            for path in sorted(self.output_root.rglob("*.tif"))
            if "results" not in path.parts
        ]


@contextmanager
def compiled_pipeline(
    root: Path, steps: list[FunctionStep]
) -> Iterator[tuple[PipelineOrchestrator, CompiledExecutionBundle, SimpleQueue]]:
    """Write the one-field plate under ``root`` and compile ``steps`` for it.

    Compilation and execution report progress, so the progress queue is
    installed for the length of the block.
    """
    plate = root / "plate"
    with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
        SyntheticMicroscopyGenerator(
            output_dir=str(plate),
            grid_size=(1, 1),
            tile_size=(SIDE, SIDE),
            overlap_percent=10,
            stage_error_px=1,
            wavelengths=1,
            z_stack_levels=1,
            num_cells=2,
            wells=["A01"],
            format="ImageXpress",
            random_seed=7,
        ).generate_dataset()
    for field in (plate / "TimePoint_1").glob("*.tif"):
        tifffile.imwrite(field, nuclei_image())

    ObjectStateRegistry.clear()
    queue = SimpleQueue()
    set_progress_queue(queue)
    try:
        ensure_global_config_context(
            GlobalPipelineConfig,
            GlobalPipelineConfig(num_workers=1, use_threading=True),
        )
        orchestrator = PipelineOrchestrator(
            plate,
            pipeline_config=PipelineConfig(
                path_planning_config=LazyPathPlanningConfig(
                    global_output_folder=root / "out"
                )
            ),
        ).initialize()
        compiled = orchestrator.compile_pipelines(
            pipeline_definition=steps, enable_visualizer_override=False
        )
        yield orchestrator, compiled, queue
    finally:
        set_progress_queue(None)


def compile_and_run(root: Path, steps: list[FunctionStep]) -> PipelineRun:
    """Compile and execute ``steps`` on the one-field plate; every well must succeed."""
    with compiled_pipeline(root, steps) as (orchestrator, compiled, queue):
        results = orchestrator.execute_compiled_bundle(
            execution_bundle=compiled,
            max_workers=1,
            progress_queue=queue,
            progress_context=ProgressExecutionContext(
                execution_id=str(root), subject_id=str(root)
            ),
        )
    failures = {
        key: result.error_message
        for key, result in results.items()
        if not result.is_success()
    }
    assert not failures, failures
    return PipelineRun(compiled, root / "out")
