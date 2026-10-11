"""Worker-lane execution runners for compiled bundle execution."""

from __future__ import annotations

import concurrent.futures
import contextlib
import logging
import multiprocessing
from multiprocessing.connection import wait as wait_for_worker_connections
import pickle
import signal
import threading
from abc import ABC, abstractmethod
from dataclasses import dataclass, field, replace
from typing import Any, Callable, Dict, Iterable, List, Mapping, Sequence

from openhcs.core.compiled_execution import (
    CompiledExecutionBundle,
    CompiledRuntimeEnvironmentPlan,
)
from openhcs.core.artifacts import ArtifactInputPlan
from openhcs.core.debug import NoOpDebugExecutionPolicy
from openhcs.core.compiled_step_plan import (
    FrameworkDeviceAssignment,
)
from openhcs.core.config import MultiprocessingStartMethod
from openhcs.core.callable_contract import FunctionStepExecutionScope
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.function_step_transport import FunctionStepTransportAuthority
from openhcs.core.native_threading import configure_native_thread_count
from openhcs.core.runtime_profile import RuntimeProfileLogger
from openhcs.core.orchestrator.execution_result import (
    ExecutionResult,
    RuntimeContextObservation,
    RuntimeExecutionObservation,
    MergeAllRuntimeRecords,
    RuntimeObservationMode,
)
from openhcs.core.orchestrator.cancellation import (
    ExecutionCancellationSignal,
    ExecutionCancelledError,
)
from openhcs.core.orchestrator.worker_lanes import (
    CompiledContextLanePlanner,
    ForkInheritedWorkerExecutionState,
    TransportAxisContexts,
    WorkerAssignmentPlan,
    WorkerLaneAxisContexts,
    WorkerLaneExecutionContext,
    WorkerLaneExecutionPlan,
)
from openhcs.core.orchestrator.worker_profiling import CProfileWorkerProfilingPolicy
from openhcs.core.progress import (
    ProgressContextPayload,
    ProgressEvent,
    ProgressQueue,
    set_progress_queue,
)
from openhcs.core.progress.live_measurements import LiveMeasurementProgressPayload
from openhcs.core.progress.runtime_artifacts import RuntimeArtifactProgressPayload
from openhcs.core.runtime_stores import (
    StoredRuntimeValue,
    RuntimeArtifactAddress,
    RuntimeArtifactLocation,
)
from openhcs.core.steps.abstract import AbstractStep, StepExecutionObservation
from openhcs.core.steps.function_artifact_materialization import (
    preview_reused_step_outputs,
)
from openhcs.utils.environment import OpenHCSProcessEnvironment
from openhcs.core.progress.types import (
    AxisCompletedProgressPhase,
    AxisErrorProgressPhase,
    AxisStartedProgressPhase,
    CancelledProgressPhase,
    CancelledProgressStatus,
    ErrorProgressStatus,
    StartedProgressStatus,
    StepCompletedProgressPhase,
    StepStartedProgressPhase,
    SuccessProgressStatus,
)

logger = logging.getLogger(__name__)
PIPELINE_PROGRESS_STEP_NAME = "pipeline"


def _runtime_observation_progress_context(
    records: tuple[StoredRuntimeValue, ...],
    *,
    materialized_locations_by_address: Mapping[
        RuntimeArtifactAddress, tuple[RuntimeArtifactLocation, ...]
    ],
) -> dict | None:
    """Project one RuntimeValueStore observation delta through owned payloads."""

    return ProgressContextPayload.context_of(
        RuntimeArtifactProgressPayload.from_records(records),
        LiveMeasurementProgressPayload.from_records(
            records,
            materialized_locations_by_address=materialized_locations_by_address,
        ),
    )


@dataclass(frozen=True, slots=True)
class WorkerExecutorResources(ABC):
    """Nominal worker execution resources for one execution mode."""

    multiprocessing_context: Any
    use_multiprocessing: bool

    @staticmethod
    def initialize_process_signals() -> None:
        """Give child termination its own process lifetime, not a parent's cleanup."""

        signal.signal(signal.SIGTERM, signal.SIG_DFL)
        signal.signal(signal.SIGINT, signal.SIG_DFL)

    @property
    def executor(self) -> concurrent.futures.Executor | None:
        return None

    def execution_context(self):
        return contextlib.nullcontext()

    def install_execution_bundle(
        self, execution_bundle: CompiledExecutionBundle
    ) -> None:
        """Install any mode-specific inherited runtime state."""

    def clear_execution_bundle(self) -> None:
        """Clear mode-specific inherited runtime state."""

    def plan_worker_lanes(
        self,
        *,
        actual_max_workers: int,
        execution_bundle: CompiledExecutionBundle,
        worker_assignments: Mapping[str, Sequence[str]],
    ) -> WorkerAssignmentPlan:
        contexts_snapshot = self.contexts_snapshot(execution_bundle)
        return CompiledContextLanePlanner(
            actual_max_workers=actual_max_workers,
            fork_inherited_execution=self.uses_fork_inherited_contexts,
        ).plan(contexts_snapshot, worker_assignments)

    @property
    @abstractmethod
    def uses_fork_inherited_contexts(self) -> bool:
        """Whether lane planning receives fork-inherited runtime context keys."""

    @abstractmethod
    def contexts_snapshot(
        self,
        execution_bundle: CompiledExecutionBundle,
    ) -> Dict[str, ProcessingContext]:
        """Return the context map consumed by lane planning for this mode."""

    @abstractmethod
    def run_worker_lanes(
        self,
        *,
        pipeline_definition: List[AbstractStep],
        worker_lane_execution_plan: WorkerLaneExecutionPlan,
        parent_contexts: Mapping[str, ProcessingContext],
    ) -> Dict[str, ExecutionResult]:
        """Execute all lane work for this mode."""

    def shutdown_executor(self) -> None:
        """Shutdown owned executor resources."""

    def cancel_execution(self) -> int:
        """Cancel the executor owned by this execution."""
        executor = self.executor
        if executor is not None:
            executor.shutdown(wait=False, cancel_futures=True)
        return 0

    def map_partition_invocations(
        self, func: Callable[[object], object], requests: Sequence[object]
    ) -> tuple[object, ...]:
        """Prepare dataset-scoped partitions using this execution's existing resources."""
        return tuple(func(request) for request in requests)

    def release_parent_runtime_resources(
        self,
        execution_bundle: CompiledExecutionBundle,
    ) -> None:
        """Release resources owned by the orchestrator process for this mode."""


@dataclass(frozen=True, slots=True)
class InlineWorkerExecutorResources(WorkerExecutorResources):
    """In-process single-lane execution resources."""

    cancellation: ExecutionCancellationSignal

    @property
    def uses_fork_inherited_contexts(self) -> bool:
        return False

    def contexts_snapshot(
        self,
        execution_bundle: CompiledExecutionBundle,
    ) -> Dict[str, ProcessingContext]:
        return dict(execution_bundle.runtime_contexts)

    def run_worker_lanes(
        self,
        *,
        pipeline_definition: List[AbstractStep],
        worker_lane_execution_plan: WorkerLaneExecutionPlan,
        parent_contexts: Mapping[str, ProcessingContext],
    ) -> Dict[str, ExecutionResult]:
        lane_results = InlineWorkerLaneRunner(self.cancellation).run(
            pipeline_definition,
            worker_lane_execution_plan,
        )
        for result in lane_results.values():
            result.runtime_observation.merge_into(parent_contexts)
        return lane_results


@dataclass(frozen=True, slots=True)
class ForkInheritedWorkerExecutorResources(WorkerExecutorResources):
    """Fork-inherited runtime context execution resources."""

    _runner: ForkInheritedWorkerLaneRunner = field(repr=False, compare=False)

    @contextlib.contextmanager
    def execution_context(self):
        try:
            yield
        except BaseException:
            try:
                self.shutdown_executor()
            except Exception:
                logger.exception(
                    "Fork worker shutdown failed while handling execution failure"
                )
            raise
        else:
            self.shutdown_executor()

    def shutdown_executor(self) -> None:
        self._runner.shutdown()

    def cancel_execution(self) -> int:
        return self._runner.cancel()

    @property
    def worker_processes(self) -> list[WorkerProcess]:
        """The worker processes this execution may hand partition work to."""

        return self._runner.workers

    def collect_results(self, workers: Sequence[WorkerProcess]) -> Iterable[Any]:
        """Read each worker's result in turn; raise the first failure after all."""

        errors: list[Exception] = []
        for worker in workers:
            try:
                yield worker.result()
            except Exception as exc:
                errors.append(exc)
        if errors:
            raise errors[0]

    def map_partition_invocations(
        self, func: Callable[[object], object], requests: Sequence[object]
    ) -> tuple[object, ...]:
        workers = self.worker_processes[: len(requests)]
        if not workers or len(requests) <= 1:
            return tuple(func(request) for request in requests)
        indexed = tuple(enumerate(requests))
        submitted: list[WorkerProcess] = []
        errors: list[Exception] = []
        for offset, worker in enumerate(workers):
            try:
                worker.send(MapPartitions(func, indexed[offset :: len(workers)]))
                submitted.append(worker)
            except Exception as exc:
                errors.append(exc)
        results: dict[int, object] = {}
        for batch_results in self.collect_results(submitted):
            results.update(batch_results)
        if errors:
            raise errors[0]
        return tuple(results[index] for index in range(len(requests)))

    @property
    def uses_fork_inherited_contexts(self) -> bool:
        return True

    def contexts_snapshot(
        self,
        execution_bundle: CompiledExecutionBundle,
    ) -> Dict[str, ProcessingContext]:
        return dict(execution_bundle.runtime_contexts)

    def install_execution_bundle(
        self, execution_bundle: CompiledExecutionBundle
    ) -> None:
        ForkInheritedWorkerExecutionState.install(execution_bundle)

    def clear_execution_bundle(self) -> None:
        ForkInheritedWorkerExecutionState.clear()

    def run_worker_lanes(
        self,
        *,
        pipeline_definition: List[AbstractStep],
        worker_lane_execution_plan: WorkerLaneExecutionPlan,
        parent_contexts: Mapping[str, ProcessingContext],
    ) -> Dict[str, ExecutionResult]:
        return self._runner.run(worker_lane_execution_plan)


@dataclass(frozen=True, slots=True)
class PooledWorkerExecutorResources(WorkerExecutorResources):
    """Thread/process pool execution resources."""

    _executor: concurrent.futures.Executor
    cancellation: ExecutionCancellationSignal | None

    @property
    def executor(self) -> concurrent.futures.Executor:
        return self._executor

    @property
    def uses_fork_inherited_contexts(self) -> bool:
        return False

    def execution_context(self):
        return self._executor

    def map_partition_invocations(
        self, func: Callable[[object], object], requests: Sequence[object]
    ) -> tuple[object, ...]:
        return tuple(self._executor.map(func, requests))

    def contexts_snapshot(
        self,
        execution_bundle: CompiledExecutionBundle,
    ) -> Dict[str, ProcessingContext]:
        return dict(execution_bundle.transport_contexts)

    def run_worker_lanes(
        self,
        *,
        pipeline_definition: List[AbstractStep],
        worker_lane_execution_plan: WorkerLaneExecutionPlan,
        parent_contexts: Mapping[str, ProcessingContext],
    ) -> Dict[str, ExecutionResult]:
        return PooledWorkerLaneRunner(
            self._executor,
            cancellation=self.cancellation,
            release_axis_resources=self.use_multiprocessing,
        ).run(
            pipeline_definition,
            worker_lane_execution_plan,
            parent_contexts,
        )

    def release_parent_runtime_resources(
        self,
        execution_bundle: CompiledExecutionBundle,
    ) -> None:
        """Release shared state only after every thread-backed lane has joined."""

        if self.use_multiprocessing:
            return
        _release_runtime_resources(
            execution_bundle.transport_contexts.values(),
            owner="threaded execution",
        )

    def shutdown_executor(self) -> None:
        try:
            self._executor.shutdown(wait=True, cancel_futures=False)
        except concurrent.futures.process.BrokenProcessPool as exc:
            logger.warning(
                "ORCHESTRATOR: Executor shutdown failed due to broken process "
                f"pool (workers were killed externally): {exc}"
            )

        except Exception as exc:
            logger.warning(f"ORCHESTRATOR: Executor shutdown failed: {exc}")

    def cancel_execution(self) -> int:
        if self.cancellation is not None:
            self.cancellation.request()
        self._executor.shutdown(wait=False, cancel_futures=True)
        return 0


@dataclass(frozen=True, slots=True)
class ProcessWorkerExecutorResources(PooledWorkerExecutorResources):
    """Process-pool resources with exact ownership of child cancellation."""

    _executor: concurrent.futures.ProcessPoolExecutor

    def cancel_execution(self) -> int:
        processes = self._executor._processes
        owned_processes = tuple(processes.values()) if processes is not None else ()
        terminated = 0
        for process in owned_processes:
            if process.is_alive():
                process.terminate()
                terminated += 1
        PooledWorkerExecutorResources.cancel_execution(self)
        return terminated


@dataclass(frozen=True, slots=True)
class ThreadedWorkerExecutorResources(PooledWorkerExecutorResources):
    """Thread workers share the prepared in-process execution graph."""

    def contexts_snapshot(
        self,
        execution_bundle: CompiledExecutionBundle,
    ) -> Dict[str, ProcessingContext]:
        return dict(execution_bundle.runtime_contexts)


class WorkerExecutorFactory:
    """Create the worker resources matching the effective runtime config."""

    def __init__(
        self,
        *,
        log_file_base: str | None,
        progress_queue: ProgressQueue,
        cancellation: ExecutionCancellationSignal,
    ) -> None:
        self._log_file_base = log_file_base
        self._progress_queue = progress_queue
        self._cancellation = cancellation

    def create(
        self,
        *,
        runtime_environment: CompiledRuntimeEnvironmentPlan,
        actual_max_workers: int,
        prepared_worker_runner: PreparedForkWorkerLaneRunner | None = None,
    ) -> WorkerExecutorResources:
        multiprocessing_context = multiprocessing.get_context(
            runtime_environment.multiprocessing_start_method.value
        )
        if actual_max_workers == 1:
            configure_native_thread_count(1)
            return InlineWorkerExecutorResources(
                multiprocessing_context=multiprocessing_context,
                use_multiprocessing=not runtime_environment.use_threading,
                cancellation=self._cancellation,
            )
        if (
            not runtime_environment.use_threading
            and runtime_environment.multiprocessing_start_method
            is MultiprocessingStartMethod.FORK
        ):
            if prepared_worker_runner is not None:
                return PreparedForkWorkerExecutorResources(
                    multiprocessing_context=multiprocessing_context,
                    use_multiprocessing=True,
                    _runner=prepared_worker_runner,
                    cancellation=self._cancellation,
                    log_file_base=self._log_file_base,
                    progress_queue=self._progress_queue,
                )
            return ForkInheritedWorkerExecutorResources(
                multiprocessing_context=multiprocessing_context,
                use_multiprocessing=True,
                _runner=ForkInheritedWorkerLaneRunner(multiprocessing_context),
            )
        if runtime_environment.use_threading:
            executor = concurrent.futures.ThreadPoolExecutor(
                max_workers=actual_max_workers
            )
            return ThreadedWorkerExecutorResources(
                multiprocessing_context=multiprocessing_context,
                use_multiprocessing=False,
                _executor=executor,
                cancellation=self._cancellation,
            )
        executor = self._process_pool_executor(
            multiprocessing_context,
            actual_max_workers,
        )
        return ProcessWorkerExecutorResources(
            multiprocessing_context=multiprocessing_context,
            use_multiprocessing=True,
            _executor=executor,
            cancellation=None,
        )

    def _process_pool_executor(
        self,
        multiprocessing_context: Any,
        actual_max_workers: int,
    ) -> concurrent.futures.ProcessPoolExecutor:
        return concurrent.futures.ProcessPoolExecutor(
            max_workers=actual_max_workers,
            mp_context=multiprocessing_context,
            initializer=_configure_worker_process,
            initargs=(
                self._log_file_base,
                self._progress_queue,
            ),
        )


def _configure_worker_logging(log_file_base: str) -> None:
    """Configure worker-process logging under the parent execution log prefix."""

    import logging
    import os
    import time

    worker_pid = os.getpid()
    worker_timestamp = int(time.time() * 1000000)
    worker_id = f"{worker_pid}_{worker_timestamp}"
    worker_log_file = f"{log_file_base}_worker_{worker_id}.log"

    root_logger = logging.getLogger()
    for handler in tuple(root_logger.handlers):
        root_logger.removeHandler(handler)
        handler.close()

    file_handler = logging.FileHandler(worker_log_file, encoding="utf-8")
    file_handler.setFormatter(
        logging.Formatter("%(asctime)s - %(name)s - %(levelname)s - %(message)s")
    )
    root_logger.addHandler(file_handler)
    root_logger.setLevel(logging.INFO)

    logging.getLogger("openhcs").setLevel(logging.INFO)


def _configure_worker_process(
    log_file_base: str | None,
    progress_queue: ProgressQueue | None = None,
) -> None:
    """Prepare process-local registries, logging, and progress transport."""

    import logging
    import os

    WorkerExecutorResources.initialize_process_signals()

    worker_log_level_name = os.environ.get("OPENHCS_LOG_LEVEL", "INFO").upper()
    worker_log_levels = logging.getLevelNamesMapping()
    if worker_log_level_name not in worker_log_levels:
        raise ValueError(f"Unknown OPENHCS_LOG_LEVEL: {worker_log_level_name!r}")
    worker_log_level = worker_log_levels[worker_log_level_name]
    if not isinstance(worker_log_level, int):
        raise ValueError(f"Unknown OPENHCS_LOG_LEVEL: {worker_log_level_name!r}")

    if not OpenHCSProcessEnvironment.cpu_only_mode():
        os.environ.pop("OPENHCS_SUBPROCESS_NO_GPU", None)
        os.environ.pop("POLYSTORE_SUBPROCESS_NO_GPU", None)

    if log_file_base is not None:
        _configure_worker_logging(log_file_base)
    else:
        logging.basicConfig(level=worker_log_level)
    logging.getLogger().setLevel(worker_log_level)
    logging.getLogger("openhcs").setLevel(worker_log_level)

    configure_native_thread_count(1)

    if progress_queue is not None:
        set_progress_queue(progress_queue)


# =============================================================================
# Worker protocol: the commands a parent sends and the replies a worker answers
# =============================================================================


class WorkerReply(ABC):
    """One message a worker process sends to its parent."""

    @abstractmethod
    def settle(
        self,
        worker: WorkerProcess,
        progress_queue: ProgressQueue | None,
    ) -> WorkerResult | None:
        """Act on this reply in the parent; return the result it completes."""


@dataclass(frozen=True)
class WorkerResult(WorkerReply):
    """The result of the command the worker was serving."""

    payload: Any

    def settle(
        self,
        worker: WorkerProcess,
        progress_queue: ProgressQueue | None,
    ) -> WorkerResult:
        return self


@dataclass(frozen=True)
class WorkerFailure(WorkerReply):
    """The command the worker was serving raised."""

    error: str
    traceback: str

    @classmethod
    def from_exception(cls, exc: BaseException) -> WorkerFailure:
        import traceback

        return cls(error=str(exc), traceback=traceback.format_exc())

    def settle(
        self,
        worker: WorkerProcess,
        progress_queue: ProgressQueue | None,
    ) -> WorkerResult | None:
        raise RuntimeError(
            f"Worker lane {worker.slot} failed: {self.error}\n{self.traceback}"
        )


@dataclass(frozen=True)
class WorkerProgress(WorkerReply):
    """A progress event emitted while the worker serves a command."""

    event: ProgressEvent

    def settle(
        self,
        worker: WorkerProcess,
        progress_queue: ProgressQueue | None,
    ) -> WorkerResult | None:
        progress_queue.put(self.event)
        return None


class WorkerConnectionProgressQueue(ProgressQueue):
    """Write progress in the same ordered stream as this worker's result."""

    def __init__(self, connection: Any):
        self.connection = connection

    def put(self, event: ProgressEvent) -> None:
        self.connection.send(WorkerProgress(event))


class WorkerCommand(ABC):
    """One request a worker process serves."""

    @abstractmethod
    def serve(self, connection: Any) -> bool:
        """Carry out this request; return False to end the worker process."""


class AnsweredWorkerCommand(WorkerCommand):
    """A command the worker answers with exactly one result or failure."""

    def serve(self, connection: Any) -> bool:
        try:
            reply: WorkerReply = WorkerResult(self.run(connection))
        except Exception as exc:
            reply = WorkerFailure.from_exception(exc)
        connection.send(reply)
        return True

    @abstractmethod
    def run(self, connection: Any) -> object:
        """Carry out the command and return its result."""


@dataclass(frozen=True)
class PrepareWorker(AnsweredWorkerCommand):
    """Route this worker's progress through its connection, then report ready."""

    def run(self, connection: Any) -> None:
        set_progress_queue(WorkerConnectionProgressQueue(connection))


@dataclass(frozen=True)
class ExecuteInheritedLane(AnsweredWorkerCommand):
    """Execute one lane against the execution bundle this process holds."""

    lane_axis_context_keys: list[tuple[str, list[str]]]
    lane_context: WorkerLaneExecutionContext
    runtime_observation_mode: type[RuntimeObservationMode]

    def run(self, connection: Any) -> Dict[str, ExecutionResult]:
        execution_bundle = ForkInheritedWorkerExecutionState.require_current()
        return execute_worker_lane(
            pipeline_definition=list(execution_bundle.pipeline_definition),
            lane_axis_contexts=ForkInheritedWorkerExecutionState.resolve_lane_contexts(
                self.lane_axis_context_keys
            ),
            lane_context=self.lane_context,
            runtime_observation_mode=self.runtime_observation_mode,
        )


@dataclass(frozen=True)
class ExecuteShippedLane(ExecuteInheritedLane):
    """Install a pickled execution bundle, then execute one lane against it."""

    bundle_payload: bytes
    log_file_base: str | None

    def run(self, connection: Any) -> Dict[str, ExecutionResult]:
        if self.log_file_base is not None:
            _configure_worker_logging(self.log_file_base)
        ForkInheritedWorkerExecutionState.install(pickle.loads(self.bundle_payload))
        return ExecuteInheritedLane.run(self, connection)


@dataclass(frozen=True)
class MapPartitions(AnsweredWorkerCommand):
    """Apply one function to this worker's share of a partitioned request list."""

    func: Callable[[object], object]
    indexed_requests: tuple[tuple[int, object], ...]

    def run(self, connection: Any) -> tuple[tuple[int, object], ...]:
        return tuple(
            (index, self.func(request)) for index, request in self.indexed_requests
        )


@dataclass(frozen=True)
class FinishExecution(AnsweredWorkerCommand):
    """Drop the execution bundle so the process can serve the next execution."""

    def run(self, connection: Any) -> None:
        ForkInheritedWorkerExecutionState.clear()


@dataclass(frozen=True)
class StopWorker(WorkerCommand):
    """End the worker process."""

    def serve(self, connection: Any) -> bool:
        return False


def _serve_worker(
    connection: Any,
    inherited_parent_connections: tuple[Any, ...],
    first_command: WorkerCommand,
) -> None:
    """Worker process entrypoint: serve commands until stopped or orphaned."""

    WorkerExecutorResources.initialize_process_signals()
    for inherited_connection in inherited_parent_connections:
        inherited_connection.close()
    command = first_command
    try:
        while command.serve(connection):
            try:
                command = connection.recv()
            except EOFError:
                break
    finally:
        ForkInheritedWorkerExecutionState.clear()
        set_progress_queue(None)
        connection.close()


@dataclass(frozen=True)
class WorkerProcess:
    """One worker process a parent owns: its slot, process and connection."""

    slot: str
    process: Any
    connection: Any

    def send(self, command: WorkerCommand) -> None:
        self.connection.send(command)

    def receive(self, progress_queue: ProgressQueue | None = None) -> WorkerResult | None:
        """Read one reply; return the result it completes, if any."""

        try:
            reply = self.connection.recv()
        except EOFError as exc:
            self.process.join()
            raise RuntimeError(
                f"Worker lane {self.slot} exited without a result; "
                f"exitcode={self.process.exitcode}."
            ) from exc
        return reply.settle(self, progress_queue)

    def result(self, progress_queue: ProgressQueue | None = None) -> Any:
        """Read replies until the result of the command being served."""

        while (result := self.receive(progress_queue)) is None:
            pass
        return result.payload


class ForkInheritedWorkerLaneRunner:
    """Runs fork-inherited worker lanes without executor serialization overhead."""

    def __init__(self, multiprocessing_context: Any) -> None:
        self._multiprocessing_context = multiprocessing_context
        self.workers: list[WorkerProcess] = []

    def start_worker(self, slot: str, first_command: WorkerCommand) -> WorkerProcess:
        parent_connection, child_connection = self._multiprocessing_context.Pipe()
        process = self._multiprocessing_context.Process(
            target=_serve_worker,
            args=(
                child_connection,
                (parent_connection, *(worker.connection for worker in self.workers)),
                first_command,
            ),
        )
        try:
            process.start()
        except BaseException:
            parent_connection.close()
            child_connection.close()
            raise
        child_connection.close()
        worker = WorkerProcess(slot, process, parent_connection)
        self.workers.append(worker)
        return worker

    def run(
        self,
        execution_plan: WorkerLaneExecutionPlan,
    ) -> Dict[str, ExecutionResult]:
        active_lanes = execution_plan.active_lane_items()
        if len(active_lanes) == 1:
            worker_slot, lane_contexts = active_lanes[0]
            return self.run_inline_single_lane(
                worker_slot,
                lane_contexts,
                execution_plan,
            )

        for worker_slot, lane_contexts in active_lanes:
            self.start_worker(
                worker_slot,
                ExecuteInheritedLane(
                    lane_axis_context_keys=lane_contexts,
                    lane_context=execution_plan.lane_context(worker_slot),
                    runtime_observation_mode=execution_plan.runtime_observation_mode,
                ),
            )

        execution_results: Dict[str, ExecutionResult] = {}
        lane_errors: list[Exception] = []
        for worker in self.workers:
            try:
                lane_results = worker.result()
                execution_results.update(lane_results)
                for result in lane_results.values():
                    result.runtime_observation.merge_into(
                        ForkInheritedWorkerExecutionState.require_current().runtime_contexts
                    )
            except Exception as exc:
                lane_errors.append(exc)
        if lane_errors:
            raise lane_errors[0]

        return execution_results

    def cancel(self) -> int:
        """Terminate only processes owned by this runner's active execution."""
        terminated = 0
        for worker in self.workers:
            if worker.process.is_alive():
                worker.process.terminate()
                terminated += 1
        return terminated

    def shutdown(self) -> None:
        """Close every owned channel and join every lane, including failed lanes."""
        workers, self.workers = self.workers, []
        errors: list[Exception] = []
        for worker in workers:
            try:
                if worker.process.is_alive():
                    worker.send(StopWorker())
            except (BrokenPipeError, EOFError, OSError):
                # The failed lane has already closed its channel.
                pass
            except Exception as exc:
                errors.append(exc)
            finally:
                try:
                    worker.connection.close()
                except Exception as exc:
                    errors.append(exc)
        for worker in workers:
            try:
                worker.process.join()
                if worker.process.exitcode != 0:
                    raise RuntimeError(
                        f"Worker lane {worker.slot} exited with "
                        f"exitcode={worker.process.exitcode}."
                    )
            except Exception as exc:
                errors.append(exc)
        if errors:
            raise errors[0]

    def run_inline_single_lane(
        self,
        worker_slot: str,
        lane_axis_context_keys: List[tuple[str, List[str]]],
        execution_plan: WorkerLaneExecutionPlan,
    ) -> Dict[str, ExecutionResult]:
        """Run a single fork-inherited lane without launching a child process."""

        return ExecuteInheritedLane(
            lane_axis_context_keys=lane_axis_context_keys,
            lane_context=execution_plan.lane_context(worker_slot),
            runtime_observation_mode=execution_plan.runtime_observation_mode,
        ).run(None)


class PreparedForkWorkerLaneRunner(ForkInheritedWorkerLaneRunner):
    """Own reusable physical processes independently of individual lane jobs."""

    def __init__(self, multiprocessing_context: Any, capacity: int):
        super().__init__(multiprocessing_context)
        if capacity < 1:
            raise ValueError("Prepared worker capacity must be positive.")
        self._capacity = capacity
        self._available: list[WorkerProcess] = []
        self._ownership_lock = threading.RLock()
        self._closed = False
        self._next_worker_id = 0

    def _start_prepared_worker(self) -> WorkerProcess:
        worker = self.start_worker(f"prepared_{self._next_worker_id}", PrepareWorker())
        self._next_worker_id += 1
        try:
            worker.result()
        except BaseException:
            self.release([worker], retire=True)
            raise
        return worker

    def prepare(self) -> None:
        """Start idle processes before endpoint readiness, with no job payload."""
        configure_native_thread_count(1)
        with self._ownership_lock:
            if self._closed:
                raise RuntimeError("Prepared worker resources are closed.")
            while len(self.workers) < self._capacity:
                self._available.append(self._start_prepared_worker())

    def acquire(self, worker_count: int) -> list[WorkerProcess]:
        """Transfer process ownership without locking any execution work."""
        with self._ownership_lock:
            if self._closed:
                raise RuntimeError("Prepared worker resources are closed.")
            dead_workers = [
                worker for worker in self._available if not worker.process.is_alive()
            ]
            if dead_workers:
                self._available = [
                    worker for worker in self._available if worker.process.is_alive()
                ]
                self.release(dead_workers, retire=True)
            while len(self._available) < worker_count:
                # Larger or concurrent jobs preserve their requested worker count.
                # Any extra creation is paid inside that job's execution clock.
                self._available.append(self._start_prepared_worker())
            workers = self._available[:worker_count]
            del self._available[:worker_count]
            return workers

    def release(self, workers: list[WorkerProcess], *, retire: bool) -> None:
        """Return clean processes or retire the exact failed/cancelled lease."""
        with self._ownership_lock:
            for worker in workers:
                if not retire and not self._closed and worker.process.is_alive():
                    self._available.append(worker)
                    continue
                if worker.process.is_alive():
                    worker.process.terminate()
                worker.process.join()
                worker.connection.close()
                self.workers = [
                    owned for owned in self.workers if owned.process is not worker.process
                ]

    def close(self) -> None:
        """Close every process owned by this server preparation."""
        with self._ownership_lock:
            self._closed = True
            self._available.clear()
            self.cancel()
            workers, self.workers = self.workers, []
            for worker in workers:
                worker.process.join()
                worker.connection.close()


@dataclass(frozen=True, slots=True)
class PreparedForkWorkerExecutorResources(ForkInheritedWorkerExecutorResources):
    """Prepared process resources with isolated ownership for each execution."""

    _runner: PreparedForkWorkerLaneRunner = field(repr=False, compare=False)
    cancellation: ExecutionCancellationSignal
    progress_queue: ProgressQueue
    log_file_base: str | None = None
    _execution_bundle: CompiledExecutionBundle | None = field(
        default=None, init=False, repr=False, compare=False
    )
    _leased: list[WorkerProcess] = field(
        default_factory=list, init=False, repr=False, compare=False
    )
    _retire_workers: bool = field(default=False, init=False, repr=False, compare=False)

    def install_execution_bundle(
        self, execution_bundle: CompiledExecutionBundle
    ) -> None:
        object.__setattr__(self, "_execution_bundle", execution_bundle)

    def clear_execution_bundle(self) -> None:
        object.__setattr__(self, "_execution_bundle", None)

    @contextlib.contextmanager
    def execution_context(self):
        try:
            yield
        except BaseException:
            object.__setattr__(self, "_retire_workers", True)
            raise
        finally:
            self.shutdown_executor()

    def run_worker_lanes(
        self,
        *,
        pipeline_definition: List[AbstractStep],
        worker_lane_execution_plan: WorkerLaneExecutionPlan,
        parent_contexts: Mapping[str, ProcessingContext],
    ) -> Dict[str, ExecutionResult]:
        execution_bundle = self._execution_bundle
        if execution_bundle is None:
            raise RuntimeError(
                "Prepared workers require an installed execution bundle and cancellation scope."
            )
        self.cancellation.raise_if_requested("before prepared worker checkout")
        lane_items = list(worker_lane_execution_plan.active_lane_items())
        self._leased.extend(self._runner.acquire(len(lane_items)))
        submitted: list[WorkerProcess] = []
        for (worker_slot, lane_keys), worker in zip(
            lane_items, self._leased, strict=True
        ):
            self.cancellation.raise_if_requested("before prepared worker submission")
            payload = pickle.dumps(
                execution_bundle.for_transport_serialization(
                    context_keys=[
                        context_key
                        for _axis_id, context_keys in lane_keys
                        for context_key in context_keys
                    ],
                ),
                protocol=pickle.HIGHEST_PROTOCOL,
            )
            worker.send(
                ExecuteShippedLane(
                    lane_axis_context_keys=lane_keys,
                    lane_context=worker_lane_execution_plan.lane_context(worker_slot),
                    runtime_observation_mode=worker_lane_execution_plan.runtime_observation_mode,
                    bundle_payload=payload,
                    log_file_base=self.log_file_base,
                )
            )
            submitted.append(worker)
        results: Dict[str, ExecutionResult] = {}
        for lane_results in self.collect_results(submitted):
            results.update(lane_results)
            for result in lane_results.values():
                if not result.is_success():
                    object.__setattr__(self, "_retire_workers", True)
                result.runtime_observation.merge_into(parent_contexts)
        self.cancellation.raise_if_requested("after prepared worker execution")
        return results

    @property
    def worker_processes(self) -> list[WorkerProcess]:
        return self._leased

    def collect_results(self, workers: Sequence[WorkerProcess]) -> Iterable[Any]:
        """Read results as workers finish, forwarding their progress meanwhile."""

        pending = {worker.connection: worker for worker in workers}
        while pending:
            for connection in wait_for_worker_connections(tuple(pending)):
                result = pending[connection].receive(self.progress_queue)
                if result is not None:
                    del pending[connection]
                    yield result.payload

    def cancel_execution(self) -> int:
        object.__setattr__(self, "_retire_workers", True)
        self.cancellation.request()
        terminated = 0
        for worker in self._leased:
            if worker.process.is_alive():
                worker.process.terminate()
                terminated += 1
        return terminated

    def shutdown_executor(self) -> None:
        if not self._leased:
            return
        workers = list(self._leased)
        self._leased.clear()
        retire = self._retire_workers
        if not retire:
            try:
                for worker in workers:
                    worker.send(FinishExecution())
                for _ in self.collect_results(workers):
                    pass
            except BaseException:
                self._runner.release(workers, retire=True)
                raise
        self._runner.release(workers, retire=retire)


class InlineWorkerLaneRunner:
    """Runs a single deterministic worker lane in the orchestrator process."""

    def __init__(self, cancellation: ExecutionCancellationSignal) -> None:
        self._cancellation = cancellation

    def run(
        self,
        pipeline_definition: List[AbstractStep],
        execution_plan: WorkerLaneExecutionPlan,
    ) -> Dict[str, ExecutionResult]:
        active_lanes = execution_plan.active_lane_items()
        if len(active_lanes) != 1:
            raise RuntimeError(
                "Inline worker lane execution requires exactly one active lane, "
                f"got {len(active_lanes)}."
            )

        worker_slot, lane_contexts = active_lanes[0]
        return execute_worker_lane(
            pipeline_definition=pipeline_definition,
            lane_axis_contexts=lane_contexts,
            lane_context=execution_plan.lane_context(worker_slot),
            runtime_observation_mode=execution_plan.runtime_observation_mode,
            cancellation=self._cancellation,
        )


class PooledWorkerLaneRunner:
    """Runs deterministic worker lanes through a thread or process executor."""

    def __init__(
        self,
        executor: concurrent.futures.Executor,
        *,
        cancellation: ExecutionCancellationSignal | None,
        release_axis_resources: bool = True,
    ) -> None:
        self._executor = executor
        self._cancellation = cancellation
        self._release_axis_resources = release_axis_resources

    def run(
        self,
        pipeline_definition: List[AbstractStep],
        execution_plan: WorkerLaneExecutionPlan,
        parent_contexts: Mapping[str, ProcessingContext],
    ) -> Dict[str, ExecutionResult]:
        future_to_worker_slot = self._submit_lanes(
            pipeline_definition,
            execution_plan,
        )
        return self._collect_results(
            future_to_worker_slot,
            pipeline_definition,
            execution_plan,
            parent_contexts,
        )

    def _submit_lanes(
        self,
        pipeline_definition: List[AbstractStep],
        execution_plan: WorkerLaneExecutionPlan,
    ) -> Dict[concurrent.futures.Future, str]:
        pipeline_definition = FunctionStepTransportAuthority.normalize_pipeline(
            pipeline_definition
        )
        future_to_worker_slot: Dict[concurrent.futures.Future, str] = {}
        for worker_slot, lane_contexts in execution_plan.active_lane_items():
            try:
                future = self._executor.submit(
                    execute_worker_lane,
                    pipeline_definition,
                    lane_contexts,
                    execution_plan.lane_context(worker_slot),
                    execution_plan.runtime_observation_mode,
                    self._cancellation,
                    self._release_axis_resources,
                )
                future_to_worker_slot[future] = worker_slot
            except Exception as submit_error:
                logger.error(
                    f"🔥 ORCHESTRATOR ERROR: Failed to submit lane {worker_slot}: {submit_error}",
                    exc_info=True,
                )
                raise
        return future_to_worker_slot

    def _collect_results(
        self,
        future_to_worker_slot: Mapping[concurrent.futures.Future, str],
        pipeline_definition: List[AbstractStep],
        execution_plan: WorkerLaneExecutionPlan,
        parent_contexts: Mapping[str, ProcessingContext],
    ) -> Dict[str, ExecutionResult]:
        execution_results: Dict[str, ExecutionResult] = {}
        lane_errors: list[Exception] = []
        for future in concurrent.futures.as_completed(future_to_worker_slot):
            worker_slot = future_to_worker_slot[future]

            try:
                lane_results = future.result()
                execution_results.update(lane_results)
                for result in lane_results.values():
                    result.runtime_observation.merge_into(parent_contexts)
            except Exception as exc:
                self._emit_lane_error(
                    exc,
                    lane_context=execution_plan.lane_context(worker_slot),
                    pipeline_definition=pipeline_definition,
                )
                lane_errors.append(exc)
        if lane_errors:
            if self._cancellation is not None:
                self._cancellation.raise_if_requested("after collecting worker lanes")
            raise lane_errors[0]
        return execution_results

    def _emit_lane_error(
        self,
        exc: Exception,
        *,
        lane_context: WorkerLaneExecutionContext,
        pipeline_definition: List[AbstractStep],
    ) -> None:
        import traceback

        full_traceback = traceback.format_exc()
        error_msg = (
            f"Worker lane {lane_context.worker_slot} generated an exception during "
            f"execution: {exc}"
        )
        logger.error(f"🔥 ORCHESTRATOR ERROR: {error_msg}", exc_info=True)
        logger.error(
            f"🔥 ORCHESTRATOR FULL TRACEBACK for worker lane "
            f"{lane_context.worker_slot}:\n{full_traceback}"
        )
        lane_context.emit(
            axis_id=lane_context.owned_partition_values[0],
            step_name=PIPELINE_PROGRESS_STEP_NAME,
            phase=AxisErrorProgressPhase,
            status=ErrorProgressStatus,
            completed=0,
            total=len(pipeline_definition),
            percent=0.0,
            error=str(exc),
            traceback=full_traceback,
        )


def _execute_axis_with_sequential_combinations(
    pipeline_definition: List[AbstractStep],
    axis_contexts: TransportAxisContexts,
    lane_context: WorkerLaneExecutionContext,
    runtime_observation_mode: type[RuntimeObservationMode],
    cancellation: ExecutionCancellationSignal | None = None,
    release_axis_resources: bool = True,
) -> ExecutionResult:
    """Execute all sequential combinations for a single axis in order."""

    if not axis_contexts:
        raise ValueError(
            "axis_contexts cannot be empty - this indicates a bug in the caller"
        )

    _, first_context = axis_contexts[0]
    axis_id = first_context.axis_id
    total_steps = len(pipeline_definition)
    completed_axis_steps = _completed_axis_step_count(first_context, total_steps)

    lane_context.emit(
        axis_id=axis_id,
        step_name=PIPELINE_PROGRESS_STEP_NAME,
        phase=AxisStartedProgressPhase,
        status=StartedProgressStatus,
        completed=0,
        total=total_steps,
        percent=0.0,
    )

    runtime_observations: list[RuntimeContextObservation] = []
    for context_key, frozen_context in axis_contexts:
        if cancellation is not None:
            try:
                cancellation.raise_if_requested(f"before context {context_key}")
            except ExecutionCancelledError as exc:
                return ExecutionResult.cancelled(
                    axis_id=axis_id,
                    error_message=str(exc),
                    runtime_observation=RuntimeExecutionObservation(
                        contexts=tuple(runtime_observations),
                    ),
                )
        runtime_store = frozen_context.runtime_value_store
        execution_observation_cursor = runtime_store.observation_cursor()
        try:
            result = _execute_single_axis_static(
                pipeline_definition,
                frozen_context,
                lane_context,
                context_key=context_key,
                cancellation=cancellation,
                runtime_observation_mode=runtime_observation_mode,
            )
            observed_records = runtime_store.observed_values_after(
                execution_observation_cursor
            )
            observation = RuntimeContextObservation.from_context(
                context_key=context_key,
                context=frozen_context,
                records=observed_records,
                runtime_observation_mode=runtime_observation_mode,
                outputs=StepExecutionObservation.combine(
                    item.outputs for item in result.runtime_observation.contexts
                ),
            )
        finally:
            # This cache is context-local even when lanes share a process.
            # Required records and table projections now belong to the observation.
            frozen_context.release_execution_image_cache()
            if release_axis_resources:
                _release_runtime_resources((frozen_context,), owner=f"axis {axis_id}")
            frozen_context.runtime_value_store.clear()
        if observation.records or not observation.outputs.is_empty:
            runtime_observations.append(observation)
        del observed_records

        if not result.is_success():
            logger.error(
                f"🔄 WORKER: Combination {context_key} failed for axis {axis_id}"
            )
            lane_context.emit(
                axis_id=axis_id,
                step_name=PIPELINE_PROGRESS_STEP_NAME,
                phase=(
                    CancelledProgressPhase
                    if result.is_cancelled()
                    else AxisErrorProgressPhase
                ),
                status=(
                    CancelledProgressStatus
                    if result.is_cancelled()
                    else ErrorProgressStatus
                ),
                completed=0,
                total=total_steps,
                percent=0.0,
                message=result.error_message,
            )
            return replace(
                result,
                failed_combination=context_key,
                runtime_observation=RuntimeExecutionObservation(
                    contexts=tuple(runtime_observations),
                ),
            )

    lane_context.emit(
        axis_id=axis_id,
        step_name=PIPELINE_PROGRESS_STEP_NAME,
        phase=AxisCompletedProgressPhase,
        status=SuccessProgressStatus,
        completed=completed_axis_steps,
        total=total_steps,
        percent=(completed_axis_steps / total_steps) * 100.0,
    )
    return ExecutionResult.success(
        axis_id=axis_id,
        runtime_observation=RuntimeExecutionObservation(
            contexts=tuple(runtime_observations),
        ),
    )


def _release_runtime_resources(
    contexts: Iterable[ProcessingContext],
    *,
    owner: str,
) -> None:
    """Attempt every independent teardown stage at its process ownership boundary."""

    from polystore.base import reset_memory_backend

    context_values = tuple(contexts)
    try:
        reset_memory_backend()
    except Exception as cleanup_error:
        logger.warning(
            "Failed to reset the memory backend after %s: %s",
            owner,
            cleanup_error,
        )
    try:
        FrameworkDeviceAssignment.merge(
            tuple(
                step_plan.device_assignment
                for context in context_values
                for step_plan in context.step_plans.values()
            )
        ).cleanup_loaded()
    except Exception as cleanup_error:
        logger.warning(
            "Failed to cleanup the compiled GPU footprint after %s: %s",
            owner,
            cleanup_error,
        )


def _completed_axis_step_count(
    context: ProcessingContext,
    total_steps: int,
) -> int:
    """Return the pipeline position where terminal dataset-scoped processing begins."""

    return min(
        (
            step_index
            for step_index, step_plan in context.step_plans.items()
            if step_plan.execution_scope is FunctionStepExecutionScope.PLATE
        ),
        default=total_steps,
    )


def _execute_single_axis_static(
    pipeline_definition: List[AbstractStep],
    frozen_context: ProcessingContext,
    lane_context: WorkerLaneExecutionContext,
    *,
    context_key: str,
    cancellation: ExecutionCancellationSignal | None = None,
    runtime_observation_mode: type[RuntimeObservationMode] = MergeAllRuntimeRecords,
) -> ExecutionResult:
    """Execute one frozen axis context against the compiled pipeline."""

    axis_id = frozen_context.axis_id
    total_steps = len(pipeline_definition)

    if not frozen_context.is_frozen():
        error_msg = f"Context for axis {axis_id} is not frozen before execution"
        logger.error(error_msg)
        raise RuntimeError(error_msg)

    if not pipeline_definition:
        error_msg = f"Empty pipeline_definition for axis {axis_id}"
        logger.error(error_msg)
        raise RuntimeError(error_msg)

    frozen_context.bind_execution_runtime(lane_context)
    lane_context.install_debug_sink(frozen_context)
    runtime_value_store = frozen_context.runtime_value_store
    # Full-value observations, debug replay and viewer histories own their
    # original retention contract. Ordinary execution can retire dead inputs
    # only after the step's output/progress consumers have completed.
    release_consumed = (
        runtime_observation_mode is not MergeAllRuntimeRecords
        and isinstance(lane_context.debug_execution_policy, NoOpDebugExecutionPolicy)
        and not any(
            plan.visualize or plan.streaming_configs
            for plan in frozen_context.step_plans.values()
        )
    )
    checkpoint_refs = (
        frozenset(
            output.ref().for_plan_type(ArtifactInputPlan)
            for plan in frozen_context.step_plans.values()
            if plan.requires_main_flow_checkpoint(frozen_context.step_plans)
            for output in plan.artifact_outputs.values()
        )
        if release_consumed
        else frozenset()
    )

    try:
        for step_index, step in enumerate(pipeline_definition):
            if cancellation is not None:
                cancellation.raise_if_requested(f"before step {step_index + 1}")
            step_plan = frozen_context.step_plans[step_index]
            compiled_pattern = step_plan.compiled_function_pattern
            if (
                compiled_pattern is not None
                and compiled_pattern.execution_scope is FunctionStepExecutionScope.PLATE
            ):
                continue
            step_name = step_plan.step_name
            if not lane_context.debug_execution_policy.should_execute_step(step_index):
                if lane_context.debug_execution_policy.should_reuse_step_outputs(
                    step_index
                ):
                    observation_cursor = runtime_value_store.observation_cursor()
                    lane_context.debug_execution_policy.prepare_reused_step_outputs(
                        step_index=step_index,
                        step_name=step_name,
                        step_scope_id=step_plan.step_scope_id,
                        context=frozen_context,
                        artifact_outputs=step_plan.artifact_outputs,
                    )
                    observed_records = runtime_value_store.observed_values_after(
                        observation_cursor
                    )
                    reused_outputs = preview_reused_step_outputs(
                        step_plan,
                        frozen_context,
                        observed_records,
                    )
                    runtime_progress_context = _runtime_observation_progress_context(
                        observed_records,
                        materialized_locations_by_address=reused_outputs.materialized_locations_by_address,
                    )
                    frozen_context.record_completed_step_outputs(reused_outputs)
                    lane_context.emit(
                        axis_id=axis_id,
                        step_name=step_name,
                        phase=StepCompletedProgressPhase,
                        status=SuccessProgressStatus,
                        completed=step_index + 1,
                        total=total_steps,
                        percent=((step_index + 1) / total_steps) * 100.0,
                        message="Reused warm debug artifacts",
                        context=runtime_progress_context,
                    )
                continue

            lane_context.emit(
                axis_id=axis_id,
                step_name=step_name,
                phase=StepStartedProgressPhase,
                status=StartedProgressStatus,
                completed=step_index,
                total=total_steps,
                percent=(step_index / total_steps) * 100.0,
            )

            observation_cursor = runtime_value_store.observation_cursor()
            step_observation = step.process(frozen_context, step_index)
            frozen_context.record_completed_step_outputs(step_observation)
            observed_records = runtime_value_store.observed_values_after(
                observation_cursor
            )
            runtime_progress_context = _runtime_observation_progress_context(
                observed_records,
                materialized_locations_by_address=step_observation.materialized_locations_by_address,
            )

            lane_context.emit(
                axis_id=axis_id,
                step_name=step_name,
                phase=StepCompletedProgressPhase,
                status=SuccessProgressStatus,
                completed=step_index + 1,
                total=total_steps,
                percent=((step_index + 1) / total_steps) * 100.0,
                context=runtime_progress_context,
            )
            if lane_context.debug_execution_policy.step_stop_strategy().should_stop_after_step(
                step_index=step_index,
                step_name=step_name,
            ):
                break
            del observed_records
            if release_consumed and step_plan.future_artifact_inputs is not None:
                runtime_value_store.release_unconsumed(
                    step_plan.future_artifact_inputs | checkpoint_refs,
                    runtime_observation_mode.retain_records(
                        runtime_value_store.observed_values,
                        frozen_context,
                    ),
                    filemanager=frozen_context.filemanager,
                )

    except ExecutionCancelledError as exc:
        return ExecutionResult.cancelled(
            axis_id=axis_id,
            error_message=str(exc),
            runtime_observation=RuntimeExecutionObservation.from_completed_outputs(
                {context_key: frozen_context}
            ),
        )
    except Exception as exc:
        logger.exception(
            "Axis %s failed while retaining completed output facts", axis_id
        )
        return ExecutionResult.error(
            axis_id=axis_id,
            failed_combination=context_key,
            error_message=str(exc),
            runtime_observation=RuntimeExecutionObservation.from_completed_outputs(
                {context_key: frozen_context}
            ),
        )

    return ExecutionResult.success(
        axis_id=axis_id,
        runtime_observation=RuntimeExecutionObservation.from_completed_outputs(
            {context_key: frozen_context}
        ),
    )


def execute_worker_lane(
    pipeline_definition: List[AbstractStep],
    lane_axis_contexts: WorkerLaneAxisContexts,
    lane_context: WorkerLaneExecutionContext,
    runtime_observation_mode: type[RuntimeObservationMode],
    cancellation: ExecutionCancellationSignal | None = None,
    release_axis_resources: bool = True,
) -> Dict[str, ExecutionResult]:
    """Execute a deterministic worker lane: its partitions in order, in one slot."""

    with CProfileWorkerProfilingPolicy.from_environment().profile(
        lane_context
    ), RuntimeProfileLogger.run(
        execution_id=lane_context.execution_id,
        worker_slot=lane_context.worker_slot,
        owned_partition_values=tuple(lane_context.owned_partition_values),
    ):
        lane_results: Dict[str, ExecutionResult] = {}
        for axis_id, axis_contexts in lane_axis_contexts:
            if cancellation is not None:
                try:
                    cancellation.raise_if_requested(f"before axis {axis_id}")
                except ExecutionCancelledError as exc:
                    lane_results[axis_id] = ExecutionResult.cancelled(
                        axis_id=axis_id,
                        error_message=str(exc),
                    )
                    break
            lane_results[axis_id] = _execute_axis_with_sequential_combinations(
                pipeline_definition=pipeline_definition,
                axis_contexts=axis_contexts,
                lane_context=lane_context,
                runtime_observation_mode=runtime_observation_mode,
                cancellation=cancellation,
                release_axis_resources=release_axis_resources,
            )
            if lane_results[axis_id].is_cancelled():
                break
        return lane_results
