"""Run pipelines of the probe function over a real server with spawn workers.

A spawned worker inherits nothing from the server: it prepares itself when it
starts and is kept for the pipelines that follow. The same probe pipeline is
run twice after a "prepare this pipeline" request and, under a second name,
twice without one; then once more with a different worker count. A last
pipeline adds a catalogue function backed by a Numba kernel. Every load and
call is recorded by ``prepared_resource_trace``; this driver records the
stages, what the records report, and which worker processes are alive.

usage: run_spawned_worker_pipelines.py <work directory>
"""

from __future__ import annotations

import io
import json
import os
import sys
import time
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

import psutil

from prepared_resource_trace import TRACE_VARIABLE, record
from run_custom_function_pipelines import (
    PROBE_SOURCE,
    UNPREPARED_PROBE,
    UNPREPARED_PROBE_SOURCE,
)

KERNEL_PROBE = "probe_with_kernel"


def main() -> None:
    work = Path(sys.argv[1]).resolve()
    import openhcs  # noqa: F401
    from objectstate.lazy_factory import ensure_global_config_context
    from openhcs.core.config import (
        GlobalPipelineConfig,
        LazyPathPlanningConfig,
        LazyVFSConfig,
        MaterializeToDisk,
        MultiprocessingStartMethod,
        PathPlanningConfig,
        PipelineConfig,
        VFSConfig,
    )
    from openhcs.core.pipeline_document import PipelineDocumentCodec
    from openhcs.core.steps import FunctionStep
    from openhcs.demo.synthetic_data import SyntheticMicroscopyGenerator
    from openhcs.microscopes.imagexpress import ImageXpressHandler
    from openhcs.processing.backends.processors.numpy_processor import create_composite
    from openhcs.processing.custom_functions import CustomFunctionManager
    from openhcs.runtime.zmq_execution_client import (
        OpenHCSExecutionSubmission,
        ZMQExecutionClient,
        ZMQExecutionRequestBuilder,
    )
    from zmqruntime.execution.responses import (
        ExecutionSubmissionResponse,
        ExecutionWaitResult,
    )

    from benchmark.timing import (
        completed_server_execution_seconds,
        completed_server_job_seconds,
        completed_server_load_phase,
    )

    plate = work / "plate"
    with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
        SyntheticMicroscopyGenerator(
            output_dir=str(plate), grid_size=(1, 1), tile_size=(64, 64),
            wavelengths=1, z_stack_levels=1, num_cells=5, cell_size_range=(4, 6),
            wells=["A01", "A02", "B01", "B02"], format="ImageXpress", random_seed=7,
        ).generate_dataset()

    manager = CustomFunctionManager()
    functions = {
        name: manager.register_from_code(source, persist=True, emit_signal=False)[0]
        for name, source in (
            ("probe", PROBE_SOURCE),
            (UNPREPARED_PROBE, UNPREPARED_PROBE_SOURCE),
            (
                KERNEL_PROBE,
                PROBE_SOURCE.replace('"probe"', f'"{KERNEL_PROBE}"').replace(
                    "def probe(", f"def {KERNEL_PROBE}("
                ),
            ),
        )
    }

    suffix = "_spawned_workers"
    vfs = VFSConfig(materialization_backend=MaterializeToDisk)

    def global_config(num_workers: int) -> GlobalPipelineConfig:
        return GlobalPipelineConfig(
            num_workers=num_workers, dataset_source=ImageXpressHandler,
            use_threading=False,
            multiprocessing_start_method=MultiprocessingStartMethod.SPAWN,
            path_planning_config=PathPlanningConfig(output_dir_suffix=suffix),
            vfs_config=vfs,
        )

    pipeline_config = PipelineConfig(
        path_planning_config=LazyPathPlanningConfig(output_dir_suffix=suffix),
        vfs_config=LazyVFSConfig.from_config(vfs),
    )
    ensure_global_config_context(GlobalPipelineConfig, global_config(2))

    def submission(steps, num_workers: int, **extra):
        return OpenHCSExecutionSubmission(
            subject_id=plate,
            pipeline_document=PipelineDocumentCodec.from_values(
                pipeline_config=pipeline_config, pipeline_steps=steps
            ),
            global_config=global_config(num_workers),
            **extra,
        )

    port = 21000 + os.getpid() % 20000
    client = ZMQExecutionClient(port=port, persistent=False)

    def completed(job_id: str, job: str):
        return ExecutionWaitResult.from_wire(
            client.wait_for_completion(job_id)
        ).require_completed_execution(job, expected_execution_id=job_id)

    def worker_census(stage: str) -> None:
        """Which processes that ever ran a call are alive, and how large."""
        pids = {
            event["pid"]
            for event in map(
                json.loads, Path(os.environ[TRACE_VARIABLE]).read_text().splitlines()
            )
            if event["kind"] == "call"
        }
        alive = {}
        for pid in sorted(pids):
            try:
                process = psutil.Process(pid)
                if process.status() != psutil.STATUS_ZOMBIE:
                    alive[str(pid)] = process.memory_info().rss
            except psutil.NoSuchProcess:
                pass
        record("worker_census", stage, alive=alive)

    def run(stage: str, function: str, steps, num_workers: int, *, prepare: bool) -> None:
        """Compile, optionally "prepare this pipeline", execute: separate jobs."""
        record("stage", stage)
        client_started_at = time.time()
        compile_id = ExecutionSubmissionResponse.from_wire(
            client.submit_compile(submission(steps, num_workers))
        ).require_execution_id("compile")
        compile_record = completed(compile_id, "compile")
        outside_total = []
        if prepare:
            record("pipeline_preparation_start", stage)
            preparation_started_at = time.time()
            preparation_id = ExecutionSubmissionResponse.from_wire(
                client.submit_prepared_pipeline(
                    ZMQExecutionRequestBuilder.from_task(
                        submission(steps, num_workers)
                    ).with_worker_preparation(compile_id)
                )
            ).require_execution_id("prepare")
            ExecutionWaitResult.from_wire(
                client.wait_for_completion(preparation_id)
            ).require_complete("prepare")
            outside_total.append([preparation_started_at, time.time()])
            record("pipeline_preparation_end", stage)
        execution_id = ExecutionSubmissionResponse.from_wire(
            client.submit_pipeline(
                submission(steps, num_workers, compile_artifact_id=compile_id)
            )
        ).require_execution_id("execute")
        execution_record = completed(execution_id, "execute")
        load_phase = completed_server_load_phase(execution_record)
        record(
            "run_times",
            function,
            stage=stage,
            prepared=prepare,
            client_started_at=client_started_at,
            client_ended_at=time.time(),
            outside_total=outside_total,
            compile_started_at=compile_record.start_time,
            compile_ended_at=compile_record.end_time,
            execution_started_at=execution_record.start_time,
            execution_ended_at=execution_record.end_time,
            load_started_at=load_phase.started_at,
            load_ended_at=load_phase.ended_at,
            loads=load_phase.loads,
            job_seconds=completed_server_job_seconds(execution_record),
            execution_seconds=completed_server_execution_seconds(execution_record),
        )
        worker_census(stage)

    def selects_large(name: str):
        return [FunctionStep(name="probe", func=(functions[name], {"model": "large"}))]

    try:
        if not client.connect(timeout=1800):
            raise RuntimeError("The execution server did not become ready.")
        record("ready")
        run("prepared 1", "probe", selects_large("probe"), 2, prepare=True)
        run("prepared 2", "probe", selects_large("probe"), 2, prepare=True)
        unprepared = selects_large(UNPREPARED_PROBE)
        run("unprepared 1", UNPREPARED_PROBE, unprepared, 2, prepare=False)
        run("unprepared 2", UNPREPARED_PROBE, unprepared, 2, prepare=False)
        run("other worker count", UNPREPARED_PROBE, unprepared, 4, prepare=False)
        with_kernel = [
            *selects_large(KERNEL_PROBE),
            FunctionStep(name="composite", func=create_composite),
        ]
        run("kernel 1", KERNEL_PROBE, with_kernel, 2, prepare=True)
        run("kernel 2", KERNEL_PROBE, with_kernel, 2, prepare=True)
    finally:
        client.disconnect()


if __name__ == "__main__":
    main()
