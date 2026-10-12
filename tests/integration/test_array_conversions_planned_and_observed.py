"""A run reports the array conversions it made, and they are the ones its plan states.

Each test compiles and executes a real pipeline on a two-well, two-field plate
(four planes) and compares the conversions returned with the run's results to
the conversions derived from the compiled plans. The CuPy and torch pipelines
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
    StepConversions,
    format_planned_and_observed,
    planned_conversions,
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


def _planned_and_observed(root: Path, name: str, execution: GlobalPipelineConfig):
    """Compile and execute one pipeline; return its planned and observed conversions."""
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
    planned = planned_conversions(
        next(iter(compiled.runtime_contexts.values())).step_plans
    )
    return planned, results.extras.conversions


def _planned_keys(planned) -> set[tuple]:
    return {(each.step_index, each.key) for each in planned if each.makes_a_new_array}


def _observed_counts(observed: StepConversions) -> dict[tuple, int]:
    return {
        (step_index, key): total.count
        for step_index, counters in observed.by_step.items()
        for key, total in counters.totals.items()
    }


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
        planned, observed = _planned_and_observed(tmp_path, "numpy_jax_numpy", execution)

    assert _planned_keys(planned) == {
        (1, ("numpy", "host", "jax", "host", "host copy")),
        (2, ("jax", "host", "numpy", "host", "host copy")),
    }
    assert _observed_counts(observed) == dict.fromkeys(
        _planned_keys(planned), PLANE_COUNT
    ), format_planned_and_observed(planned, observed)
    assert ConversionObserver.current is observer_before
    assert not ConversionObserver.current.wants_records
    [logged] = [
        record.getMessage()
        for record in caplog.records
        if record.getMessage().startswith("Array conversions of this run")
    ]
    assert logged.splitlines()[1:] == format_planned_and_observed(
        planned, observed
    ).splitlines()


def _cuda_device_present() -> bool:
    if find_spec("torch") is None or find_spec("cupy") is None:
        return False
    import torch

    return torch.cuda.is_available()


@pytest.mark.skipif(not _cuda_device_present(), reason="needs CuPy, torch and CUDA")
def test_cupy_hands_torch_its_buffer_and_the_run_reports_it(tmp_path):
    planned, observed = _planned_and_observed(tmp_path, "cupy_torch_numpy", IN_PROCESS)

    assert _planned_keys(planned) == {
        (0, ("numpy", "host", "cupy", "accelerator:0", "host copy")),
        (1, ("cupy", "accelerator:0", "torch", "accelerator:0", "dlpack")),
        (2, ("torch", "accelerator:0", "numpy", "host", "host copy")),
    }
    assert _observed_counts(observed) == dict.fromkeys(
        _planned_keys(planned), PLANE_COUNT
    ), format_planned_and_observed(planned, observed)


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

    assert report["planned"] == [
        [0, ["numpy", "host", "torch", "host", "host copy"]],
        [1, ["torch", "host", "numpy", "host", "host copy"]],
    ]
    assert report["observed"] == [
        [0, ["numpy", "host", "torch", "host", "host copy"], PLANE_COUNT],
        [1, ["torch", "host", "numpy", "host", "host copy"], PLANE_COUNT],
    ]
    assert report["cuda_initialized"] is False


if __name__ == "__main__":
    planned, observed = _planned_and_observed(Path(sys.argv[2]), sys.argv[1], IN_PROCESS)
    import torch

    print(
        json.dumps(
            {
                "planned": sorted(_planned_keys(planned)),
                "observed": sorted(
                    (step, key, count)
                    for (step, key), count in _observed_counts(observed).items()
                ),
                "cuda_initialized": torch.cuda.is_initialized(),
            }
        )
    )
