"""Worker-side profiling policies for orchestrator execution."""

from __future__ import annotations

import cProfile
import sys
import threading
from abc import ABC, abstractmethod
from collections.abc import Callable, Iterator
from contextlib import contextmanager, nullcontext
from dataclasses import dataclass
from pathlib import Path

from openhcs.utils.environment import OpenHCSProcessEnvironment


class WorkerProfilingPolicy(ABC):
    """Policy boundary for optional worker-side execution profiling."""

    @contextmanager
    @abstractmethod
    def profile(
        self,
        *,
        execution_id: str,
        plate_id: str,
        worker_slot: str,
        owned_wells: list[str],
    ) -> Iterator[None]:
        """Profile a worker execution region when the policy is active."""
        yield


@dataclass(frozen=True)
class DisabledWorkerProfilingPolicy(WorkerProfilingPolicy):
    """No-op worker profiling policy."""

    @contextmanager
    def profile(
        self,
        *,
        execution_id: str,
        plate_id: str,
        worker_slot: str,
        owned_wells: list[str],
    ) -> Iterator[None]:
        with nullcontext():
            yield


@dataclass(frozen=True)
class CProfileWorkerProfilingPolicy(WorkerProfilingPolicy):
    """Dump cProfile stats for worker execution regions."""

    output_dir: Path

    @classmethod
    def from_environment(cls) -> WorkerProfilingPolicy:
        profile_dir = OpenHCSProcessEnvironment.worker_profile_directory()
        if profile_dir is None:
            return DisabledWorkerProfilingPolicy()
        if hasattr(sys, "monitoring"):
            return MonitoringCProfileWorkerProfilingPolicy(profile_dir)
        return ThreadLocalCProfileWorkerProfilingPolicy(profile_dir)

    @contextmanager
    def profile(
        self,
        *,
        execution_id: str,
        plate_id: str,
        worker_slot: str,
        owned_wells: list[str],
    ) -> Iterator[None]:
        self.output_dir.mkdir(parents=True, exist_ok=True)
        profiler = cProfile.Profile()
        profiler.enable()
        try:
            self.configure_profile_event_scope()
            yield
        finally:
            profiler.disable()
            profiler.dump_stats(
                str(
                    self.output_dir
                    / self.profile_filename(
                        execution_id=execution_id,
                        plate_id=plate_id,
                        worker_slot=worker_slot,
                        owned_wells=owned_wells,
                    )
                )
            )

    @abstractmethod
    def configure_profile_event_scope(self) -> None:
        """Bind profiler events to the concrete runtime's execution thread."""

    def profile_filename(
        self,
        *,
        execution_id: str,
        plate_id: str,
        worker_slot: str,
        owned_wells: list[str],
    ) -> str:
        well_token = "all" if not owned_wells else "-".join(sorted(owned_wells))
        fields = (execution_id, plate_id, worker_slot, well_token)
        return "__".join(self.filename_component(field) for field in fields) + ".prof"

    @staticmethod
    def filename_component(value: str) -> str:
        return "".join(
            character if character.isalnum() or character in {"-", "_"} else "_"
            for character in value
        )


@dataclass(frozen=True, slots=True)
class ThreadOwnedProfilerCallback:
    """Admit a profiling event only from its owning execution thread."""

    thread_id: int
    callback: Callable[..., object]

    def __call__(self, *event_arguments: object) -> object:
        if threading.get_ident() == self.thread_id:
            return self.callback(*event_arguments)
        return None


class ThreadLocalCProfileWorkerProfilingPolicy(CProfileWorkerProfilingPolicy):
    """Use cProfile's native thread-local scope on pre-monitoring runtimes."""

    def configure_profile_event_scope(self) -> None:
        """The native thread-local profiler needs no monitoring callback binding."""


class MonitoringCProfileWorkerProfilingPolicy(CProfileWorkerProfilingPolicy):
    """Scope interpreter-wide cProfile callbacks to the worker thread."""

    def configure_profile_event_scope(self) -> None:
        monitoring = sys.monitoring
        thread_id = threading.get_ident()
        event_ids = {
            value
            for value in vars(monitoring.events).values()
            if isinstance(value, int) and value > 0 and value & (value - 1) == 0
        }
        for event_id in sorted(event_ids):
            callback = monitoring.register_callback(
                monitoring.PROFILER_ID, event_id, None
            )
            if callback is not None:
                monitoring.register_callback(
                    monitoring.PROFILER_ID,
                    event_id,
                    ThreadOwnedProfilerCallback(thread_id, callback),
                )
