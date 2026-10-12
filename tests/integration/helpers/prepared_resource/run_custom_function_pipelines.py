"""Run pipelines of two custom functions over a real execution server.

One function is stored before the server starts. The other is stored while the
server is ready, the way the editor does it (the client writes the source), and
the server is then asked to bring its catalogue up to date. Each pipeline is
compiled and executed twice with fork workers. Every preparation, load and call
is recorded by ``prepared_resource_trace``; this driver records the windows.

usage: run_custom_function_pipelines.py <work directory>
"""

from __future__ import annotations

import io
import os
import sys
import time
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

from prepared_resource_trace import record

# A resource that is loaded into memory: the preparation loads it, and the
# function loads it if no preparation did. LOADS is what this process sees.
SOURCE = '''
from prepared_resource_trace import record
from openhcs.core.memory import numpy as numpy_function

LOADED = []

def _resource():
    if not LOADED:
        record("load", "{name}")
        LOADED.append(object())
    return LOADED[0]

def _prepare() -> None:
    record("prepare", "{name}")
    _resource()

@numpy_function(prepare=_prepare)
def {name}(image, gain: float = 1.0):
    """Multiply the stack.

    Args:
        image: Image stack.
        gain: Factor.
    """
    _resource()
    record("call", "{name}", loads=len(LOADED))
    return image * gain
'''


# A function with both parts of a preparation: what it acquires (once per
# machine, for every value its hook declares) and what it loads (per process,
# for the value a pipeline selects). The function accepts a third value that
# the acquire hook does not declare.
PROBE_SOURCE = '''
from typing import Literal
from prepared_resource_trace import record
from openhcs.core.memory import numpy as numpy_function

HELD = set()

def _acquire(model: Literal["small", "large"]) -> None:
    record("acquire", "probe", model=model)

def _load(model: Literal["small", "large", "undeclared"]) -> None:
    record("load", "probe", model=model)
    HELD.add(model)

@numpy_function(prepare=_acquire, load=_load)
def probe(image, model: Literal["small", "large", "undeclared"] = "small"):
    """Return the stack.

    Args:
        image: Image stack.
        model: Which resource to use.
    """
    if model not in HELD:
        _load(model)
    record("call", "probe", model=model)
    return image
'''

# The same function under a second name, for pipelines that are executed
# without a "prepare this pipeline" request: no worker holds its loads yet.
UNPREPARED_PROBE = "probe_unprepared"
UNPREPARED_PROBE_SOURCE = PROBE_SOURCE.replace(
    '"probe"', f'"{UNPREPARED_PROBE}"'
).replace("def probe(", f"def {UNPREPARED_PROBE}(")


def main() -> None:
    work = Path(sys.argv[1]).resolve()
    import openhcs  # noqa: F401
    from objectstate.lazy_factory import ensure_global_config_context
    from openhcs.agent.dto.execution_connection import ExecutionConnectionSpec
    from openhcs.agent.dto.functions import (
        FunctionCatalogPreparationOutcome,
        FunctionCatalogPreparationStartRequest,
        FunctionCatalogPreparationStatusRequest,
    )
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
    from openhcs.processing.custom_functions import CustomFunctionManager
    from openhcs.runtime.zmq_execution_client import (
        FunctionCatalogEndpointUnavailableError,
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

    def store(name: str):
        [function] = manager.register_from_code(
            SOURCE.format(name=name), persist=True, emit_signal=False
        )
        return function

    stored_before_start = store("resource_stored_before_start")
    [probe] = manager.register_from_code(PROBE_SOURCE, persist=True, emit_signal=False)
    [probe_unprepared] = manager.register_from_code(
        UNPREPARED_PROBE_SOURCE, persist=True, emit_signal=False
    )

    suffix = "_prepared_resource"
    vfs = VFSConfig(materialization_backend=MaterializeToDisk)
    global_config = GlobalPipelineConfig(
        num_workers=2, dataset_source=ImageXpressHandler, use_threading=False,
        multiprocessing_start_method=MultiprocessingStartMethod.FORK,
        path_planning_config=PathPlanningConfig(output_dir_suffix=suffix),
        vfs_config=vfs,
    )
    pipeline_config = PipelineConfig(
        path_planning_config=LazyPathPlanningConfig(output_dir_suffix=suffix),
        vfs_config=LazyVFSConfig.from_config(vfs),
    )
    ensure_global_config_context(GlobalPipelineConfig, global_config)

    def submission(steps, **extra):
        return OpenHCSExecutionSubmission(
            subject_id=plate,
            pipeline_document=PipelineDocumentCodec.from_values(
                pipeline_config=pipeline_config, pipeline_steps=steps
            ),
            global_config=global_config,
            **extra,
        )

    port = 21000 + os.getpid() % 20000
    client = ZMQExecutionClient(port=port, persistent=False)

    def run(steps) -> None:
        record("compile_start")
        compile_id = ExecutionSubmissionResponse.from_wire(
            client.submit_compile(submission(steps))
        ).require_execution_id("compile")
        ExecutionWaitResult.from_wire(
            client.wait_for_completion(compile_id)
        ).require_complete("compile")
        record("compile_end")
        record("execute_start")
        execution_id = ExecutionSubmissionResponse.from_wire(
            client.submit_pipeline(submission(steps, compile_artifact_id=compile_id))
        ).require_execution_id("execute")
        ExecutionWaitResult.from_wire(
            client.wait_for_completion(execution_id)
        ).require_complete("execute")
        record("execute_end")

    def compile_pipeline(steps) -> str:
        compile_id = ExecutionSubmissionResponse.from_wire(
            client.submit_compile(submission(steps))
        ).require_execution_id("compile")
        ExecutionWaitResult.from_wire(
            client.wait_for_completion(compile_id)
        ).require_complete("compile")
        return compile_id

    def completed(job_id: str, job: str):
        return ExecutionWaitResult.from_wire(
            client.wait_for_completion(job_id)
        ).require_completed_execution(job, expected_execution_id=job_id)

    def record_run_times(
        function: str,
        *,
        prepared: bool,
        client_started_at: float,
        outside_total: list[list[float]],
        compile_record,
        execution_record,
    ) -> None:
        """What the records report, on the clock of the trace."""
        load_phase = completed_server_load_phase(execution_record)
        record(
            "run_times",
            function,
            prepared=prepared,
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

    def run_prepared(steps) -> None:
        """Compile, "prepare this pipeline", execute: three separate jobs."""
        client_started_at = time.time()
        record("compile_start")
        compile_id = ExecutionSubmissionResponse.from_wire(
            client.submit_compile(submission(steps))
        ).require_execution_id("compile")
        compile_record = completed(compile_id, "compile")
        record("compile_end")
        record("pipeline_preparation_start")
        preparation_started_at = time.time()
        preparation_id = ExecutionSubmissionResponse.from_wire(
            client.submit_prepared_pipeline(
                ZMQExecutionRequestBuilder.from_task(
                    submission(steps)
                ).with_worker_preparation(compile_id)
            )
        ).require_execution_id("prepare")
        ExecutionWaitResult.from_wire(
            client.wait_for_completion(preparation_id)
        ).require_complete("prepare")
        preparation_ended_at = time.time()
        record("pipeline_preparation_end")
        record("execute_start")
        execution_id = ExecutionSubmissionResponse.from_wire(
            client.submit_pipeline(submission(steps, compile_artifact_id=compile_id))
        ).require_execution_id("execute")
        execution_record = completed(execution_id, "execute")
        record("execute_end")
        record_run_times(
            "probe",
            prepared=True,
            client_started_at=client_started_at,
            outside_total=[[preparation_started_at, preparation_ended_at]],
            compile_record=compile_record,
            execution_record=execution_record,
        )

    def run_unprepared(steps) -> None:
        """Compile and execute, as the GUI does: the execution loads by itself.

        The client's wall clock around this run contains the load phase, so it
        is not marked as a timed window: the windows are the records' own.
        """
        client_started_at = time.time()
        compile_id = ExecutionSubmissionResponse.from_wire(
            client.submit_compile(submission(steps))
        ).require_execution_id("compile")
        compile_record = completed(compile_id, "compile")
        execution_id = ExecutionSubmissionResponse.from_wire(
            client.submit_pipeline(submission(steps, compile_artifact_id=compile_id))
        ).require_execution_id("execute")
        execution_record = completed(execution_id, "execute")
        record_run_times(
            UNPREPARED_PROBE,
            prepared=False,
            client_started_at=client_started_at,
            outside_total=[],
            compile_record=compile_record,
            execution_record=execution_record,
        )

    try:
        if not client.connect(timeout=1800):
            raise RuntimeError("The execution server did not become ready.")
        record("ready")
        first = [FunctionStep(name="before start", func=stored_before_start)]
        run(first)
        run(first)

        # Storing tells the connected server, so the moment is recorded first.
        record("stored_while_ready")
        stored_while_ready = store("resource_stored_while_ready")
        state = client.function_catalog_preparation(
            FunctionCatalogPreparationStartRequest(
                ExecutionConnectionSpec(port=port, persistent=False)
            )
        )
        while state.outcome is not FunctionCatalogPreparationOutcome.READY:
            if state.outcome not in (
                FunctionCatalogPreparationOutcome.PENDING,
                FunctionCatalogPreparationOutcome.NOT_STARTED,
            ):
                raise RuntimeError(f"Catalogue preparation is {state.outcome.value}.")
            time.sleep(0.05)
            try:
                state = client.function_catalog_preparation(
                    FunctionCatalogPreparationStatusRequest(state.handle)
                )
            except FunctionCatalogEndpointUnavailableError:
                # The server is forking its workers again; ask again.
                continue
        record("ready")
        both = [*first, FunctionStep(name="while ready", func=stored_while_ready)]
        run(both)
        run(both)

        selects_large = [FunctionStep(name="probe", func=(probe, {"model": "large"}))]
        run_prepared(selects_large)
        run_prepared(selects_large)
        try:
            compile_pipeline(
                [FunctionStep(name="probe", func=(probe, {"model": "undeclared"}))]
            )
        except Exception as error:
            record("refused", "probe", message=str(error))

        unprepared = [
            FunctionStep(name="probe", func=(probe_unprepared, {"model": "large"}))
        ]
        run_unprepared(unprepared)
        run_unprepared(unprepared)
    finally:
        client.disconnect()


if __name__ == "__main__":
    main()
