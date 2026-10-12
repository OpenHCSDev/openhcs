"""Create, edit, retry and delete custom functions while a real server is connected.

The driver is the session: it holds one connected client and calls the
manager's operations, nothing else. The manager tells the server. Every
acquisition and call is recorded by ``prepared_resource_trace``; this driver
records what the manager lists, what the server reports and the timed windows.

usage: run_custom_function_changes.py <work directory>
"""

from __future__ import annotations

import io
import os
import sys
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

from prepared_resource_trace import record

FOLLOWED = '''
from prepared_resource_trace import record
from openhcs.core.memory import numpy as numpy_function

def _acquire() -> None:
    record("acquire", "followed", revision="{revision}")

@numpy_function(prepare=_acquire)
def followed(image, gain: float = 1.0):
    """Multiply the stack.

    Args:
        image: Image stack.
        gain: Factor.
    """
    record("call", "followed", revision="{revision}")
    return image * gain
'''

# Acquisition runs in a server, not in the session that stores the source, so
# this source is valid where it is written and fails where it is acquired.
NOT_ACQUIRABLE = '''
from prepared_resource_trace import record
from openhcs.core.memory import numpy as numpy_function

def _acquire() -> None:
    record("acquire", "not_acquirable")
    raise ConnectionError("weights are unreachable")

@numpy_function(prepare=_acquire)
def not_acquirable(image):
    """Return the stack.

    Args:
        image: Image stack.
    """
    return image
'''

# One declared value cannot be acquired until a marker file exists (the network
# comes back). The function is published for the other value meanwhile.
VALUED = '''
from pathlib import Path
from typing import Literal
from prepared_resource_trace import record
from openhcs.core.memory import numpy as numpy_function

HELD = set()

def _acquire(model: Literal["small", "large"]) -> None:
    record("acquire", "valued", model=model)
    if model == "large" and not Path({marker!r}).exists():
        raise ConnectionError("weights are unreachable")

def _load(model: Literal["small", "large"]) -> None:
    record("load", "valued", model=model)
    HELD.add(model)

@numpy_function(prepare=_acquire, load=_load)
def valued(image, model: Literal["small", "large"] = "small"):
    """Return the stack.

    Args:
        image: Image stack.
        model: Which resource to use.
    """
    if model not in HELD:
        _load(model)
    record("call", "valued", model=model)
    return image
'''


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
    from openhcs.processing.custom_functions import CustomFunctionManager
    from openhcs.processing.custom_functions.connected_servers import (
        connected_servers,
    )
    from openhcs.runtime.zmq_execution_client import (
        OpenHCSExecutionSubmission,
        ZMQExecutionClient,
        ZMQExecutionRequestBuilder,
    )
    from zmqruntime.execution.responses import (
        ExecutionSubmissionResponse,
        ExecutionWaitResult,
    )

    plate = work / "plate"
    with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
        SyntheticMicroscopyGenerator(
            output_dir=str(plate), grid_size=(1, 1), tile_size=(64, 64),
            wavelengths=1, z_stack_levels=1, num_cells=5, cell_size_range=(4, 6),
            wells=["A01", "A02"], format="ImageXpress", random_seed=7,
        ).generate_dataset()

    suffix = "_followed"
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

    def submission(function, **extra):
        return OpenHCSExecutionSubmission(
            subject_id=plate,
            pipeline_document=PipelineDocumentCodec.from_values(
                pipeline_config=pipeline_config,
                pipeline_steps=[FunctionStep(name="followed", func=function)],
            ),
            global_config=global_config,
            **extra,
        )

    manager = CustomFunctionManager()
    client = ZMQExecutionClient(port=21000 + os.getpid() % 20000, persistent=False)

    def compiled(task) -> str:
        compile_id = ExecutionSubmissionResponse.from_wire(
            client.submit_compile(task)
        ).require_execution_id("compile")
        ExecutionWaitResult.from_wire(
            client.wait_for_completion(compile_id)
        ).require_complete("compile")
        return compile_id

    def run(function) -> None:
        record("compile_start")
        compile_id = compiled(submission(function))
        record("compile_end")
        record("execute_start")
        execution_id = ExecutionSubmissionResponse.from_wire(
            client.submit_pipeline(submission(function, compile_artifact_id=compile_id))
        ).require_execution_id("execute")
        ExecutionWaitResult.from_wire(
            client.wait_for_completion(execution_id)
        ).require_complete("execute")
        record("execute_end")

    def listed(moment: str) -> None:
        record(
            "listed",
            moment=moment,
            entries=[
                [entry.list_label, entry.status]
                for entry in manager.list_custom_functions()
            ],
        )

    def followed(moment: str) -> None:
        """The server has finished what the manager told it; record what it holds."""
        if not connected_servers.wait_until_followed(600):
            raise RuntimeError(f"The server did not finish following: {moment}.")
        state = client.custom_catalogue_state()
        record(
            "server_state",
            moment=moment,
            pending=state.pending,
            loaded=[[source.function_name, source.content_sha256] for source in state.loaded],
            failed=[[failure.name, failure.message] for failure in state.failed],
            unacquired=[
                [missing.name, list(missing.values)] for missing in state.unacquired
            ],
        )
        listed(moment)

    def prepared(task, compile_id: str) -> None:
        """The "prepare this pipeline" job of a compiled pipeline."""
        preparation_id = ExecutionSubmissionResponse.from_wire(
            client.submit_prepared_pipeline(
                ZMQExecutionRequestBuilder.from_task(task).with_worker_preparation(
                    compile_id
                )
            )
        ).require_execution_id("prepare")
        ExecutionWaitResult.from_wire(
            client.wait_for_completion(preparation_id)
        ).require_complete("prepare")

    try:
        if not client.connect(timeout=1800):
            raise RuntimeError("The execution server did not become ready.")
        record("ready")

        record("create")
        [function] = manager.register_from_code(FOLLOWED.format(revision="one"))
        listed("told")
        followed("created")
        run(function)
        run(function)

        record("edit")
        manager.update_custom_function("followed", FOLLOWED.format(revision="two"))
        followed("edited")
        from openhcs.processing import custom_functions

        function = custom_functions.followed
        run(function)

        record("create_not_acquirable")
        manager.register_from_code(NOT_ACQUIRABLE)
        followed("not_acquirable")

        naming_deleted = submission(function)
        record("delete")
        manager.delete_custom_function("followed")
        followed("deleted")
        try:
            compiled(naming_deleted)
        except Exception as error:
            record("refused", "followed", message=str(error))

        # A value that cannot be acquired yet: published without it, tried
        # again by "prepare this pipeline", never inside a compile or execute.
        marker = work / "weights-reachable"
        record("create_valued")
        [valued] = manager.register_from_code(VALUED.format(marker=str(marker)))
        followed("valued_created")
        selects_large = (valued, {"model": "large"})
        record("valued_compile_start")
        compile_id = compiled(submission(selects_large))
        record("valued_compile_end")
        record("valued_prepare_start", attempt="unreachable")
        try:
            prepared(submission(selects_large), compile_id)
        except Exception as error:
            record("prepare_failed", "valued", message=str(error))
        record("valued_prepare_end", attempt="unreachable")
        marker.touch()
        record("valued_prepare_start", attempt="reachable")
        prepared(submission(selects_large), compile_id)
        record("valued_prepare_end", attempt="reachable")
        record("valued_execute_start")
        execution_id = ExecutionSubmissionResponse.from_wire(
            client.submit_pipeline(
                submission(selects_large, compile_artifact_id=compile_id)
            )
        ).require_execution_id("execute")
        ExecutionWaitResult.from_wire(
            client.wait_for_completion(execution_id)
        ).require_complete("execute")
        record("valued_execute_end")
        state = client.custom_catalogue_state()
        record(
            "server_state",
            moment="valued_acquired",
            pending=state.pending,
            unacquired=[
                [missing.name, list(missing.values)] for missing in state.unacquired
            ],
        )
    finally:
        client.disconnect()


if __name__ == "__main__":
    main()
