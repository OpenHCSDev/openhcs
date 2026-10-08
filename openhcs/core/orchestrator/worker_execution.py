"""Worker-lane execution runners for compiled plate execution."""

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
    CompiledStepPlan,
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
from openhcs.core.progress import emit, ProgressPhase, ProgressStatus
from openhcs.core.progress import ProgressQueue
from openhcs.core.progress.live_measurements import (
    live_measurement_context_for_records,
)
from openhcs.core.progress.runtime_artifacts import (
    runtime_artifact_context_for_records,
)
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

    runtime_artifacts = runtime_artifact_context_for_records(records)
    live_measurements = live_measurement_context_for_records(
        records,
        materialized_locations_by_address=materialized_locations_by_address,
    )
    if runtime_artifacts is None:
        return live_measurements
    if live_measurements is None:
        return runtime_artifacts
    return {**runtime_artifacts, **live_measurements}


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
        worker_assignments: Dict[str, List[str]] | None,
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
        """Prepare plate partitions using this execution's existing resources."""
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
    def partition_worker_processes(self) -> list[tuple[str, Any, Any]]:
        return self._runner._processes

    def partition_command(
        self, func: Callable[[object], object], requests: tuple[tuple[int, object], ...]
    ) -> tuple[object, ...]:
        return func, requests

    def _collect_results(self, workers: list[tuple[str, Any, Any]]) -> Iterable[Any]:
        errors: list[Exception] = []
        for worker in workers:
            try:
                yield self._runner._receive_result(*worker)
            except Exception as exc:
                errors.append(exc)
        if errors:
            raise errors[0]

    def map_partition_invocations(
        self, func: Callable[[object], object], requests: Sequence[object]
    ) -> tuple[object, ...]:
        workers = self.partition_worker_processes[: len(requests)]
        if not workers or len(requests) <= 1:
            return tuple(func(request) for request in requests)
        indexed = tuple(enumerate(requests))
        submitted = []
        errors: list[Exception] = []
        for offset, worker in enumerate(workers):
            try:
                worker[2].send(
                    self.partition_command(func, indexed[offset :: len(workers)])
                )
                submitted.append(worker)
            except Exception as exc:
                errors.append(exc)
        results: dict[int, object] = {}
        for batch_results in self._collect_results(submitted):
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
        from openhcs.core.progress import set_progress_queue

        set_progress_queue(progress_queue)


def _execute_fork_inherited_worker_lane_process(
    result_connection: Any,
    lane_axis_context_keys: List[tuple[str, List[str]]],
    lane_context: WorkerLaneExecutionContext,
    runtime_observation_mode: RuntimeObservationMode,
    inherited_parent_connections: tuple[Any, ...],
) -> None:
    """Process entrypoint for fork-inherited worker lane execution."""

    WorkerExecutorResources.initialize_process_signals()
    for connection in inherited_parent_connections:
        connection.close()
    profiling_policy = CProfileWorkerProfilingPolicy.from_environment()
    try:
        with profiling_policy.profile(
            execution_id=lane_context.execution_id,
            plate_id=lane_context.plate_id,
            worker_slot=lane_context.worker_slot,
            owned_wells=list(lane_context.owned_wells),
        ):
            result_connection.send(
                (
                    "result",
                    _execute_fork_inherited_worker_lane_static(
                        lane_axis_context_keys,
                        lane_context,
                        runtime_observation_mode,
                    ),
                )
            )
        while True:
            invocation = result_connection.recv()
            if invocation is None:
                break
            func, indexed_requests = invocation
            try:
                result_connection.send(
                    (
                        "result",
                        tuple(
                            (index, func(request))
                            for index, request in indexed_requests
                        ),
                    )
                )
            except Exception as exc:
                import traceback

                result_connection.send(("error", exc, traceback.format_exc()))
    except BaseException as exc:
        import traceback

        result_connection.send(("error", exc, traceback.format_exc()))
    finally:
        result_connection.close()


class ForkInheritedWorkerLaneRunner:
    """Runs fork-inherited worker lanes without executor serialization overhead."""

    def __init__(self, multiprocessing_context: Any) -> None:
        self._multiprocessing_context = multiprocessing_context
        self._processes: list[tuple[str, Any, Any]] = []

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

        execution_results: Dict[str, ExecutionResult] = {}

        for worker_slot, lane_contexts in active_lanes:
            worker_lane_context = execution_plan.lane_context(worker_slot)
            result_reader, result_writer = self._multiprocessing_context.Pipe(
                duplex=True
            )
            process = self._multiprocessing_context.Process(
                target=_execute_fork_inherited_worker_lane_process,
                args=(
                    result_writer,
                    lane_contexts,
                    worker_lane_context,
                    execution_plan.runtime_observation_mode,
                    (
                        result_reader,
                        *(connection for _, _, connection in self._processes),
                    ),
                ),
            )
            try:
                process.start()
            except BaseException:
                result_reader.close()
                result_writer.close()
                raise
            result_writer.close()
            self._processes.append((worker_slot, process, result_reader))

        lane_errors: list[Exception] = []
        for worker_slot, process, result_reader in self._processes:
            try:
                lane_results = self._receive_result(worker_slot, process, result_reader)
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

    @staticmethod
    def _receive_result(worker_slot: str, process: Any, connection: Any) -> Any:
        try:
            message_kind, payload, *rest = connection.recv()
        except EOFError as exc:
            process.join()
            raise RuntimeError(
                f"Fork worker lane {worker_slot} exited without returning "
                f"a result; exitcode={process.exitcode}."
            ) from exc
        if message_kind == "error":
            if not rest:
                raise RuntimeError(
                    f"Fork worker lane {worker_slot} returned an error without traceback."
                )
            raise RuntimeError(
                f"Fork worker lane {worker_slot} generated an exception: "
                f"{payload}\n{rest[0]}"
            )
        if message_kind != "result":
            raise RuntimeError(
                f"Fork worker lane {worker_slot} returned unknown message {message_kind!r}."
            )
        return payload

    def cancel(self) -> int:
        """Terminate only processes owned by this runner's active execution."""
        terminated = 0
        for _worker_slot, process, _connection in self._processes:
            if process.is_alive():
                process.terminate()
                terminated += 1
        return terminated

    def shutdown(self) -> None:
        """Close every owned channel and join every lane, including failed lanes."""
        processes, self._processes = self._processes, []
        errors: list[Exception] = []
        for _worker_slot, process, connection in processes:
            try:
                if process.is_alive():
                    connection.send(None)
            except (BrokenPipeError, EOFError, OSError):
                # The failed lane has already closed its channel.
                pass
            except Exception as exc:
                errors.append(exc)
            finally:
                try:
                    connection.close()
                except Exception as exc:
                    errors.append(exc)
        for worker_slot, process, _connection in processes:
            try:
                process.join()
                if process.exitcode != 0:
                    raise RuntimeError(
                        f"Fork worker lane {worker_slot} exited with exitcode={process.exitcode}."
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

        execution_state = ForkInheritedWorkerExecutionState.require_current()
        lane_axis_contexts = ForkInheritedWorkerExecutionState.resolve_lane_contexts(
            lane_axis_context_keys
        )
        lane_results = execute_worker_lane(
            pipeline_definition=list(execution_state.pipeline_definition),
            lane_axis_contexts=lane_axis_contexts,
            lane_context=execution_plan.lane_context(worker_slot),
            runtime_observation_mode=execution_plan.runtime_observation_mode,
        )
        return lane_results


class WorkerConnectionProgressQueue(ProgressQueue):
    """Write progress in the same ordered stream as this worker's result."""

    def __init__(self, connection: Any):
        self.connection = connection

    def put(self, progress_update: dict) -> None:
        self.connection.send(("progress", progress_update))


def _execute_prepared_fork_worker_process(
    connection: Any,
    inherited_parent_connections: tuple[Any, ...],
) -> None:
    """Serve isolated compiled jobs in a process prepared with the server."""
    WorkerExecutorResources.initialize_process_signals()
    for inherited_connection in inherited_parent_connections:
        inherited_connection.close()
    from openhcs.core.progress import set_progress_queue

    set_progress_queue(WorkerConnectionProgressQueue(connection))
    connection.send(("result", None))
    try:
        while True:
            command = connection.recv()
            if command is None:
                break
            operation, *arguments = command
            try:
                if operation == "execute":
                    (
                        payload,
                        lane_keys,
                        lane_context,
                        observation_mode,
                        log_file_base,
                    ) = arguments
                    if log_file_base is not None:
                        _configure_worker_logging(log_file_base)
                    execution_bundle = pickle.loads(payload)
                    ForkInheritedWorkerExecutionState.install(execution_bundle)
                    profiling_policy = CProfileWorkerProfilingPolicy.from_environment()
                    with profiling_policy.profile(
                        execution_id=lane_context.execution_id,
                        plate_id=lane_context.plate_id,
                        worker_slot=lane_context.worker_slot,
                        owned_wells=list(lane_context.owned_wells),
                    ):
                        result = _execute_fork_inherited_worker_lane_static(
                            lane_keys, lane_context, observation_mode
                        )
                    connection.send(("result", result))
                    del result
                elif operation == "finish":
                    ForkInheritedWorkerExecutionState.clear()
                    del execution_bundle
                    connection.send(("result", None))
                elif operation == "partition":
                    func, indexed_requests = arguments
                    connection.send(
                        (
                            "result",
                            tuple(
                                (index, func(request))
                                for index, request in indexed_requests
                            ),
                        )
                    )
                else:
                    raise ValueError(f"Unknown prepared worker command {operation!r}.")
            except Exception as exc:
                import traceback

                connection.send(("error", exc, traceback.format_exc()))
    except EOFError:
        pass
    finally:
        ForkInheritedWorkerExecutionState.clear()
        set_progress_queue(None)
        connection.close()


class PreparedForkWorkerLaneRunner(ForkInheritedWorkerLaneRunner):
    """Own reusable physical processes independently of individual lane jobs."""

    def __init__(self, multiprocessing_context: Any, capacity: int):
        super().__init__(multiprocessing_context)
        if capacity < 1:
            raise ValueError("Prepared worker capacity must be positive.")
        self._capacity = capacity
        self._available: list[tuple[str, Any, Any]] = []
        self._ownership_lock = threading.RLock()
        self._closed = False
        self._next_worker_id = 0

    def _start_worker(self) -> tuple[str, Any, Any]:
        parent, child = self._multiprocessing_context.Pipe()
        worker_slot = f"prepared_{self._next_worker_id}"
        self._next_worker_id += 1
        process = self._multiprocessing_context.Process(
            target=_execute_prepared_fork_worker_process,
            args=(
                child,
                (parent, *(connection for _, _, connection in self._processes)),
            ),
        )
        try:
            process.start()
        except BaseException:
            parent.close()
            child.close()
            raise
        child.close()
        worker = (worker_slot, process, parent)
        self._processes.append(worker)
        try:
            self._receive_result(*worker)
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
            while len(self._processes) < self._capacity:
                self._available.append(self._start_worker())

    def acquire(self, worker_count: int) -> list[tuple[str, Any, Any]]:
        """Transfer process ownership without locking any execution work."""
        with self._ownership_lock:
            if self._closed:
                raise RuntimeError("Prepared worker resources are closed.")
            dead_workers = [
                worker for worker in self._available if not worker[1].is_alive()
            ]
            if dead_workers:
                self._available = [
                    worker for worker in self._available if worker[1].is_alive()
                ]
                self.release(dead_workers, retire=True)
            while len(self._available) < worker_count:
                # Larger or concurrent jobs preserve their requested worker count.
                # Any extra creation is paid inside that job's execution clock.
                self._available.append(self._start_worker())
            workers = self._available[:worker_count]
            del self._available[:worker_count]
            return workers

    def release(self, workers: list[tuple[str, Any, Any]], *, retire: bool) -> None:
        """Return clean processes or retire the exact failed/cancelled lease."""
        with self._ownership_lock:
            for worker in workers:
                _, process, connection = worker
                if not retire and not self._closed and process.is_alive():
                    self._available.append(worker)
                    continue
                if process.is_alive():
                    process.terminate()
                process.join()
                connection.close()
                self._processes = [
                    entry for entry in self._processes if entry[1] is not process
                ]

    def close(self) -> None:
        """Close every process owned by this server preparation."""
        with self._ownership_lock:
            self._closed = True
            self._available.clear()
            self.cancel()
            processes, self._processes = self._processes, []
            for _, process, connection in processes:
                process.join()
                connection.close()


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
    _processes: list[tuple[str, Any, Any]] = field(
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
        self._processes.extend(self._runner.acquire(len(lane_items)))
        payload = pickle.dumps(
            execution_bundle.for_transport_serialization(),
            protocol=pickle.HIGHEST_PROTOCOL,
        )
        submitted: list[tuple[str, Any, Any]] = []
        for (worker_slot, lane_keys), (_, process, connection) in zip(
            lane_items, self._processes, strict=True
        ):
            self.cancellation.raise_if_requested("before prepared worker submission")
            connection.send(
                (
                    "execute",
                    payload,
                    lane_keys,
                    worker_lane_execution_plan.lane_context(worker_slot),
                    worker_lane_execution_plan.runtime_observation_mode,
                    self.log_file_base,
                )
            )
            submitted.append((worker_slot, process, connection))
        results: Dict[str, ExecutionResult] = {}
        for lane_results in self._collect_results(submitted):
            results.update(lane_results)
            for result in lane_results.values():
                if not result.is_success():
                    object.__setattr__(self, "_retire_workers", True)
                result.runtime_observation.merge_into(parent_contexts)
        self.cancellation.raise_if_requested("after prepared worker execution")
        return results

    @property
    def partition_worker_processes(self) -> list[tuple[str, Any, Any]]:
        return self._processes

    def partition_command(
        self, func: Callable[[object], object], requests: tuple[tuple[int, object], ...]
    ) -> tuple[object, ...]:
        return "partition", func, requests

    def _collect_results(self, workers: list[tuple[str, Any, Any]]) -> Iterable[Any]:
        pending = {
            connection: (worker_slot, process)
            for worker_slot, process, connection in workers
        }
        while pending:
            for connection in wait_for_worker_connections(tuple(pending)):
                worker_slot, process = pending[connection]
                try:
                    kind, payload, *rest = connection.recv()
                except EOFError as exc:
                    process.join()
                    raise RuntimeError(
                        f"Prepared worker lane {worker_slot} exited without a result; exitcode={process.exitcode}."
                    ) from exc
                if kind == "progress":
                    self.progress_queue.put(payload)
                elif kind == "result":
                    del pending[connection]
                    yield payload
                elif kind == "error":
                    raise RuntimeError(
                        f"Prepared worker lane {worker_slot} failed: {payload}\n{rest[0]}"
                    )
                else:
                    raise RuntimeError(
                        f"Prepared worker lane {worker_slot} returned unknown message {kind!r}."
                    )

    def cancel_execution(self) -> int:
        object.__setattr__(self, "_retire_workers", True)
        self.cancellation.request()
        terminated = 0
        for _, process, _ in self._processes:
            if process.is_alive():
                process.terminate()
                terminated += 1
        return terminated

    def shutdown_executor(self) -> None:
        if not self._processes:
            return
        workers = list(self._processes)
        self._processes.clear()
        retire = self._retire_workers
        if not retire:
            try:
                for _, _, connection in workers:
                    connection.send(("finish",))
                for _ in self._collect_results(workers):
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
        lane_context = execution_plan.lane_context(worker_slot)
        profiling_policy = CProfileWorkerProfilingPolicy.from_environment()
        with profiling_policy.profile(
            execution_id=lane_context.execution_id,
            plate_id=lane_context.plate_id,
            worker_slot=lane_context.worker_slot,
            owned_wells=list(lane_context.owned_wells),
        ):
            return execute_worker_lane(
                pipeline_definition=pipeline_definition,
                lane_axis_contexts=lane_contexts,
                lane_context=lane_context,
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
    ) -> Dict[concurrent.futures.Future, tuple[str, List[str]]]:
        pipeline_definition = FunctionStepTransportAuthority.normalize_pipeline(
            pipeline_definition
        )
        future_to_worker_slot: Dict[
            concurrent.futures.Future, tuple[str, List[str]]
        ] = {}
        for (
            worker_slot,
            lane_contexts,
        ) in execution_plan.assignments.lane_axis_contexts.items():
            if not lane_contexts:
                continue
            owned_wells = list(execution_plan.assignments.owned_wells(worker_slot))
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
                future_to_worker_slot[future] = (worker_slot, owned_wells)
            except Exception as submit_error:
                logger.error(
                    f"🔥 ORCHESTRATOR ERROR: Failed to submit lane {worker_slot}: {submit_error}",
                    exc_info=True,
                )
                raise
        return future_to_worker_slot

    def _collect_results(
        self,
        future_to_worker_slot: Mapping[
            concurrent.futures.Future, tuple[str, List[str]]
        ],
        pipeline_definition: List[AbstractStep],
        execution_plan: WorkerLaneExecutionPlan,
        parent_contexts: Mapping[str, ProcessingContext],
    ) -> Dict[str, ExecutionResult]:
        execution_results: Dict[str, ExecutionResult] = {}
        lane_errors: list[Exception] = []
        for future in concurrent.futures.as_completed(future_to_worker_slot):
            worker_slot, owned_wells = future_to_worker_slot[future]

            try:
                lane_results = future.result()
                execution_results.update(lane_results)
                for result in lane_results.values():
                    result.runtime_observation.merge_into(parent_contexts)
            except Exception as exc:
                self._emit_lane_error(
                    exc,
                    worker_slot=worker_slot,
                    owned_wells=owned_wells,
                    pipeline_definition=pipeline_definition,
                    execution_plan=execution_plan,
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
        worker_slot: str,
        owned_wells: List[str],
        pipeline_definition: List[AbstractStep],
        execution_plan: WorkerLaneExecutionPlan,
    ) -> None:
        import traceback

        if not owned_wells:
            raise RuntimeError(
                f"Worker lane {worker_slot} cannot emit an axis error without owned wells."
            ) from exc

        full_traceback = traceback.format_exc()
        error_msg = (
            f"Worker lane {worker_slot} generated an exception during execution: {exc}"
        )
        logger.error(f"🔥 ORCHESTRATOR ERROR: {error_msg}", exc_info=True)
        logger.error(
            f"🔥 ORCHESTRATOR FULL TRACEBACK for worker lane {worker_slot}:\n{full_traceback}"
        )
        emit(
            execution_id=execution_plan.execution_id,
            plate_id=execution_plan.plate_id,
            axis_id=owned_wells[0],
            step_name=PIPELINE_PROGRESS_STEP_NAME,
            phase=ProgressPhase.AXIS_ERROR,
            status=ProgressStatus.ERROR,
            completed=0,
            total=len(pipeline_definition),
            percent=0.0,
            error=str(exc),
            traceback=full_traceback,
            worker_slot=worker_slot,
            owned_wells=owned_wells,
        )


def _execute_axis_with_sequential_combinations(
    pipeline_definition: List[AbstractStep],
    axis_contexts: TransportAxisContexts,
    lane_context: WorkerLaneExecutionContext,
    runtime_observation_mode: RuntimeObservationMode,
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

    emit(
        execution_id=lane_context.execution_id,
        plate_id=lane_context.plate_id,
        axis_id=axis_id,
        step_name=PIPELINE_PROGRESS_STEP_NAME,
        phase=ProgressPhase.AXIS_STARTED,
        status=ProgressStatus.STARTED,
        completed=0,
        total=total_steps,
        percent=0.0,
        worker_slot=lane_context.worker_slot,
        owned_wells=list(lane_context.owned_wells),
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
            emit(
                execution_id=lane_context.execution_id,
                plate_id=lane_context.plate_id,
                axis_id=axis_id,
                step_name=PIPELINE_PROGRESS_STEP_NAME,
                phase=(
                    ProgressPhase.CANCELLED
                    if result.is_cancelled()
                    else ProgressPhase.AXIS_ERROR
                ),
                status=(
                    ProgressStatus.CANCELLED
                    if result.is_cancelled()
                    else ProgressStatus.ERROR
                ),
                completed=0,
                total=total_steps,
                percent=0.0,
                message=result.error_message,
                worker_slot=lane_context.worker_slot,
                owned_wells=list(lane_context.owned_wells),
            )
            return replace(
                result,
                failed_combination=context_key,
                runtime_observation=RuntimeExecutionObservation(
                    contexts=tuple(runtime_observations),
                ),
            )

    emit(
        execution_id=lane_context.execution_id,
        plate_id=lane_context.plate_id,
        axis_id=axis_id,
        step_name=PIPELINE_PROGRESS_STEP_NAME,
        phase=ProgressPhase.AXIS_COMPLETED,
        status=ProgressStatus.SUCCESS,
        completed=completed_axis_steps,
        total=total_steps,
        percent=(completed_axis_steps / total_steps) * 100.0,
        worker_slot=lane_context.worker_slot,
        owned_wells=list(lane_context.owned_wells),
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
    """Return the pipeline position where terminal plate processing begins."""

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
    runtime_observation_mode: RuntimeObservationMode = RuntimeObservationMode.MERGE_INTO_PARENT,
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
        runtime_observation_mode is not RuntimeObservationMode.MERGE_INTO_PARENT
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
                    emit(
                        execution_id=lane_context.execution_id,
                        plate_id=lane_context.plate_id,
                        axis_id=axis_id,
                        step_name=step_name,
                        phase=ProgressPhase.STEP_COMPLETED,
                        status=ProgressStatus.SUCCESS,
                        completed=step_index + 1,
                        total=total_steps,
                        percent=((step_index + 1) / total_steps) * 100.0,
                        worker_slot=lane_context.worker_slot,
                        owned_wells=list(lane_context.owned_wells),
                        message="Reused warm debug artifacts",
                        context=runtime_progress_context,
                    )
                continue

            emit(
                execution_id=lane_context.execution_id,
                plate_id=lane_context.plate_id,
                axis_id=axis_id,
                step_name=step_name,
                phase=ProgressPhase.STEP_STARTED,
                status=ProgressStatus.STARTED,
                completed=step_index,
                total=total_steps,
                percent=(step_index / total_steps) * 100.0,
                worker_slot=lane_context.worker_slot,
                owned_wells=list(lane_context.owned_wells),
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

            emit(
                execution_id=lane_context.execution_id,
                plate_id=lane_context.plate_id,
                axis_id=axis_id,
                step_name=step_name,
                phase=ProgressPhase.STEP_COMPLETED,
                status=ProgressStatus.SUCCESS,
                completed=step_index + 1,
                total=total_steps,
                percent=((step_index + 1) / total_steps) * 100.0,
                worker_slot=lane_context.worker_slot,
                owned_wells=list(lane_context.owned_wells),
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
    runtime_observation_mode: RuntimeObservationMode,
    cancellation: ExecutionCancellationSignal | None = None,
    release_axis_resources: bool = True,
) -> Dict[str, ExecutionResult]:
    """Execute a deterministic worker lane: wells sequentially within one slot."""

    with RuntimeProfileLogger.run(
        execution_id=lane_context.execution_id,
        worker_slot=lane_context.worker_slot,
        owned_wells=tuple(lane_context.owned_wells),
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


def _execute_fork_inherited_worker_lane_static(
    lane_axis_context_keys: List[tuple[str, List[str]]],
    lane_context: WorkerLaneExecutionContext,
    runtime_observation_mode: RuntimeObservationMode,
) -> Dict[str, ExecutionResult]:
    """Execute a worker lane using fork-inherited compiled contexts."""

    execution_bundle = ForkInheritedWorkerExecutionState.require_current()
    return execute_worker_lane(
        pipeline_definition=list(execution_bundle.pipeline_definition),
        lane_axis_contexts=ForkInheritedWorkerExecutionState.resolve_lane_contexts(
            lane_axis_context_keys
        ),
        lane_context=lane_context,
        runtime_observation_mode=runtime_observation_mode,
    )
