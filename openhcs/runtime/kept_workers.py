"""The worker processes an execution server keeps between pipelines."""

from __future__ import annotations

import logging
import multiprocessing
import os
import queue
import sys
import threading
import time

from openhcs.core.compiled_execution import CompiledExecutionBundle
from openhcs.core.orchestrator.bundle_execution import actual_max_workers
from openhcs.core.orchestrator.cancellation import ExecutionCancellationSignal
from openhcs.core.orchestrator.worker_execution import (
    PreparedForkWorkerLaneRunner,
    PreparedWorkerExecutorResources,
    PreparedWorkerLaneRunner,
    SelfPreparedWorkerLaneRunner,
    WorkerExecutorFactory,
    WorkerExecutorResources,
    WorkerNeed,
    WorkerSupply,
)
from openhcs.processing.custom_functions.events import custom_function_changed

logger = logging.getLogger(__name__)


class KeptWorkers(WorkerSupply):
    """Own every worker process a server keeps, from preparation through execution.

    Lifetime rule. A pipeline runs in workers that hold what the server
    prepared, and the same workers serve "prepare this pipeline", the
    execution that follows, and every later execution of that pipeline, so a
    worker loads a resource once.

    - Forked workers inherit the server's prepared state. They are started
      before the server reports ready, serve every pipeline whose workers
      fork, and are kept until the server stops.
    - Workers that start on their own (spawn, forkserver: every pipeline with
      an accelerator step) inherit nothing: each prepares itself in its first
      command and holds its own copy of every load. They are started by the
      first load phase of a pipeline (its "prepare this pipeline" job, or the
      load phase of an execution nobody prepared), one per lane, and kept
      while the next pipeline on that start method has the same worker count.
      A kept worker never holds a load the pipeline it is leased to does not
      select: such a worker is ended and started again in that pipeline's
      load phase.

    Who releases. ``close`` (server stop) ends every worker. A pipeline with
    a different worker count ends the self-started workers kept before it; a
    pipeline that selects other loads ends the ones that hold a load it does
    not select. A custom-function change ends the self-started
    workers, and forks the forked workers again
    (``PreparedForkWorkerLaneRunner.replace_with_current_forks``). A worker
    that is leased when its runner is released ends when its execution
    returns it.
    """

    def __init__(self) -> None:
        self._runners: list[PreparedWorkerLaneRunner] = []
        self._lock = threading.RLock()

    def start_inheriting_workers(self) -> None:
        """Fork one idle worker per schedulable CPU, before the server reports ready."""
        if "fork" not in multiprocessing.get_all_start_methods():
            return
        capacity = (
            len(os.sched_getaffinity(0))
            if sys.platform.startswith("linux")
            else (os.cpu_count() or 1)
        )
        with self._lock:
            self._runners.append(
                PreparedForkWorkerLaneRunner.prepared(
                    multiprocessing.get_context("fork"), capacity
                )
            )
        custom_function_changed.subscribe(self.sources_changed)

    def sources_changed(self) -> None:
        """A custom function this server loads later is held by no worker yet."""
        with self._lock:
            for runner in self._runners:
                runner.sources_changed()
            self._drop_closed()

    def _drop_closed(self) -> None:
        self._runners = [runner for runner in self._runners if not runner.is_closed]

    def runner_for(self, need: WorkerNeed) -> PreparedWorkerLaneRunner:
        """The kept workers that serve the pipeline, or new ones in place of the old."""
        with self._lock:
            for runner in self._runners:
                if runner.serves(need):
                    return runner
            for runner in self._runners:
                if runner.starts_like(need):
                    runner.retire()
            self._drop_closed()
            runner = SelfPreparedWorkerLaneRunner(need)
            self._runners.append(runner)
            return runner

    def process_resources(
        self, need: WorkerNeed, factory: WorkerExecutorFactory
    ) -> WorkerExecutorResources:
        return PreparedWorkerExecutorResources.leasing_from(
            self.runner_for(need), need, factory
        )

    def prepare_pipeline(
        self, execution_id: str, execution_bundle: CompiledExecutionBundle
    ) -> dict[str, int]:
        """Load what the pipeline selects into the workers that will run it.

        Before any worker loads, this server tries again the acquisitions the
        pipeline's steps select that failed; one that fails again fails this
        job with the function, the value and the cause.

        The workers are returned to the front of their runner's idle set, so
        the execution of this pipeline is given the same processes.
        """
        worker_count = actual_max_workers(execution_bundle, None)
        resources = WorkerExecutorFactory(
            log_file_base=None,
            progress_queue=queue.SimpleQueue(),
            cancellation=ExecutionCancellationSignal(),
        ).create(
            runtime_environment=execution_bundle.runtime_environment,
            actual_max_workers=worker_count,
            workers=self,
        )
        started = time.perf_counter()
        with resources.execution_context():
            loads = resources.prepare_pipeline(execution_bundle, worker_count)
        logger.info(
            "[%s] Prepared pipeline: %d resource load(s) across %d worker(s) in %.3fs",
            execution_id,
            loads,
            worker_count,
            time.perf_counter() - started,
        )
        return {"resource_loads": loads, "workers": worker_count}

    def close(self) -> None:
        """End every worker process this server keeps."""
        with self._lock:
            runners, self._runners = self._runners, []
        for runner in runners:
            runner.close()
