"""A run reports the array conversions it made, each beside what its plan states.

Each test compiles and executes a real pipeline on a two-well, two-field plate
(four planes) and reads the compared rows returned with the run's results:
what the plan states for each crossing, what was recorded there, and whether
they match, differ in a way ArrayBridge's record explains, or mismatch. The CuPy and torch pipelines
need those libraries; the accelerator one needs a CUDA device.

Run as a script with a pipeline name, this module executes that pipeline and
prints what was planned and observed as JSON, so a test can run it in a process
that starts with ``CUDA_VISIBLE_DEVICES=``.
"""

from __future__ import annotations

import io
import json
import logging
import os
import subprocess
import sys
from contextlib import redirect_stderr, redirect_stdout
from importlib.util import find_spec
import multiprocessing
from pathlib import Path

import openhcs  # noqa: F401 - prefer repository submodules before direct imports
import pytest
from arraybridge.conversion import ConversionObserver
from objectstate import ObjectStateRegistry
from objectstate.lazy_factory import ensure_global_config_context

from openhcs.core import memory
from openhcs.core.array_conversions import (
    ComparedConversions,
    format_compared_conversions,
)
from openhcs.core.config import (
    GlobalPipelineConfig,
    LazyPathPlanningConfig,
    MultiprocessingStartMethod,
    PipelineConfig,
)
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.progress import ProgressExecutionContext, set_progress_queue
from openhcs.core.steps import FunctionStep
from openhcs.demo.synthetic_data import SyntheticMicroscopyGenerator

PLANE_COUNT = 4


@memory.numpy
def add_one(image):
    return image + 1


@memory.jax
def double_in_jax(image):
    return image * 2


@memory.numpy
def subtract_one(image):
    return image - 1


@memory.cupy
def double_in_cupy(image):
    return image * 2


@memory.torch
def halve_in_torch(image):
    return image / 2


PIPELINES = {
    "numpy_jax_numpy": (add_one, double_in_jax, subtract_one),
    "cupy_torch_numpy": (double_in_cupy, halve_in_torch, subtract_one),
    "torch_numpy": (halve_in_torch, subtract_one),
}


def _compared_conversions(
    root: Path, name: str, execution: GlobalPipelineConfig
) -> tuple[ComparedConversions, ...]:
    """Compile and execute one pipeline; return its conversions beside the plan."""
    plate = root / "plate"
    with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
        SyntheticMicroscopyGenerator(
            output_dir=str(plate),
            grid_size=(2, 1),
            tile_size=(64, 64),
            overlap_percent=10,
            stage_error_px=1,
            wavelengths=1,
            z_stack_levels=1,
            num_cells=2,
            wells=["A01", "A02"],
            format="ImageXpress",
            random_seed=7,
        ).generate_dataset()

    ObjectStateRegistry.clear()
    queue = multiprocessing.get_context(
        execution.multiprocessing_start_method.value
    ).SimpleQueue()
    set_progress_queue(queue)
    try:
        ensure_global_config_context(
            GlobalPipelineConfig,
            execution,
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
            pipeline_definition=[FunctionStep(func=func) for func in PIPELINES[name]],
            enable_visualizer_override=False,
        )
        results = orchestrator.execute_compiled_bundle(
            execution_bundle=compiled,
            max_workers=execution.num_workers,
            progress_queue=queue,
            progress_context=ProgressExecutionContext(
                execution_id=str(root), subject_id=str(root)
            ),
        )
    finally:
        set_progress_queue(None)
    results.require_success()
    return results.extras.conversions


def _crossings(rows: tuple[ComparedConversions, ...]) -> list[tuple]:
    return [
        (
            row.step_index,
            f"{row.source_library} on {row.source_device}",
            f"{row.target_library} on {row.target_device}",
            row.planned,
            row.observed,
            row.agreement,
            row.count,
        )
        for row in rows
    ]


SHARED = "shared host buffer"

IN_PROCESS = GlobalPipelineConfig(num_workers=1, use_threading=True)


@pytest.mark.parametrize(
    "execution",
    [
        IN_PROCESS,
        GlobalPipelineConfig(num_workers=2, use_threading=True),
        GlobalPipelineConfig(
            num_workers=2,
            use_threading=False,
            multiprocessing_start_method=MultiprocessingStartMethod.SPAWN,
        ),
    ],
    ids=["in-process", "threads", "worker-processes"],
)
def test_a_numpy_jax_numpy_run_returns_the_conversions_its_plan_states(
    tmp_path, execution, caplog
):
    observer_before = ConversionObserver.current

    with caplog.at_level(logging.INFO, logger="openhcs.core.orchestrator.bundle_execution"):
        rows = _compared_conversions(tmp_path, "numpy_jax_numpy", execution)

    table = format_compared_conversions(rows)
    # NumPy hands JAX its buffer only when the buffer starts on a 64-byte
    # boundary, which each plane's allocation decides: the plan says shared, and
    # a plane that was copied is recorded as a copy with the shared route declined.
    into_jax = [row for row in rows if row.target_library == "jax"]
    assert {
        (row.planned, row.observed, row.declined_mechanisms, row.agreement)
        for row in into_jax
    } <= {
        (SHARED, SHARED, (), "matches"),
        (SHARED, "host copy", (SHARED,), "explained difference"),
    }, table
    assert sum(row.count for row in into_jax) == PLANE_COUNT, table
    assert {row.boundaries for row in into_jax} == {("add_one -> double_in_jax",)}
    assert _crossings(tuple(row for row in rows if row not in into_jax)) == [
        (0, "numpy on host", "numpy on host", "stays in place", "no record", "matches", 0),
        (2, "jax on host", "numpy on host", SHARED, SHARED, "matches", PLANE_COUNT),
        (2, "numpy on host", "numpy on host", "stays in place", "no record", "matches", 0),
    ], table
    assert ConversionObserver.current is observer_before
    assert not ConversionObserver.current.wants_records
    [logged] = [
        record
        for record in caplog.records
        if record.getMessage().startswith("Array conversions of this run")
    ]
    assert logged.levelno == logging.INFO
    assert logged.getMessage().splitlines()[1:] == table.splitlines()


def _cuda_device_present() -> bool:
    if find_spec("torch") is None or find_spec("cupy") is None:
        return False
    import torch

    return torch.cuda.is_available()


@pytest.mark.skipif(not _cuda_device_present(), reason="needs CuPy, torch and CUDA")
def test_cupy_hands_torch_its_buffer_and_the_run_reports_it(tmp_path):
    rows = _compared_conversions(tmp_path, "cupy_torch_numpy", IN_PROCESS)

    assert _crossings(rows) == [
        (0, "numpy on host", "cupy on accelerator:0", "host copy", "host copy", "matches", 4),
        (1, "cupy on accelerator:0", "torch on accelerator:0", "dlpack", "dlpack", "matches", 4),
        (2, "torch on accelerator:0", "numpy on host", "host copy", "host copy", "matches", 4),
        (2, "numpy on host", "numpy on host", "stays in place", "no record", "matches", 0),
    ], format_compared_conversions(rows)


@pytest.mark.skipif(find_spec("torch") is None, reason="needs torch")
def test_torch_without_a_visible_accelerator_converts_on_host_as_planned(tmp_path):
    completed = subprocess.run(
        [sys.executable, __file__, "torch_numpy", str(tmp_path)],
        env={**os.environ, "CUDA_VISIBLE_DEVICES": ""},
        capture_output=True,
        text=True,
        check=False,
    )
    assert completed.returncode == 0, completed.stderr[-3000:]
    report = json.loads(completed.stdout.splitlines()[-1])

    assert [
        (row["step_index"], row["source_library"], row["source_device"],
         row["target_library"], row["target_device"], row["planned"], row["observed"],
         row["agreement"], row["count"])
        for row in report["conversions"]
    ] == [
        (0, "numpy", "host", "torch", "host", SHARED, SHARED, "matches", PLANE_COUNT),
        (1, "torch", "host", "numpy", "host", SHARED, SHARED, "matches", PLANE_COUNT),
        (1, "numpy", "host", "numpy", "host", "stays in place", "no record", "matches", 0),
    ]
    assert report["cuda_initialized"] is False


if __name__ == "__main__":
    rows = _compared_conversions(Path(sys.argv[2]), sys.argv[1], IN_PROCESS)
    import torch

    print(
        json.dumps(
            {
                "conversions": [row.to_json() for row in rows],
                "cuda_initialized": torch.cuda.is_initialized(),
            }
        )
    )
