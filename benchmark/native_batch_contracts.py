"""Native batch measurement records shared without importing OpenHCS.

The native worker imports this adjacent module directly under Python 3.9;
OpenHCS consumers import the same owners through the benchmark package.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Mapping, Optional


@dataclass(frozen=True)
class NativeBatchRequest:
    pipeline_path: str
    input_dir: str
    output_root: str
    expected_image_sets: Optional[int]
    repetitions: int
    file_list_path: Optional[str] = None
    first_image_set: int = 1
    last_image_set: Optional[int] = None
    report_path: Optional[str] = None
    start_barrier_root: Optional[str] = None
    start_barrier_job_count: int = 1
    start_barrier_job_index: int = 0
    assignment_output_subdirectories: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        assignments = tuple(self.assignment_output_subdirectories)
        if len(assignments) != len({Path(assignment) for assignment in assignments}):
            raise ValueError("Native assignment output directories must be unique")
        for assignment in assignments:
            path = Path(assignment)
            if not path.parts or path.is_absolute() or ".." in path.parts:
                raise ValueError(
                    "Native assignments require relative output directories"
                )
        object.__setattr__(self, "assignment_output_subdirectories", assignments)

    @property
    def temporary_root(self) -> Path:
        output_root = Path(self.output_root)
        return output_root.with_name(output_root.name + "_tmp")

    def worker_environment(self) -> dict[str, str]:
        """Producer and probe inherit the same output-prefix-derived scratch scope."""
        import os

        environment = os.environ.copy()
        environment.update(
            {name: str(self.temporary_root) for name in ("TMPDIR", "TMP", "TEMP")}
        )
        return environment

    def output_device(self) -> int:
        output_root = Path(self.output_root).absolute()
        existing = next(
            path for path in (output_root, *output_root.parents) if path.exists()
        )
        return existing.stat().st_dev

    def require_same_workload(self, current: NativeBatchRequest) -> None:
        """Compare every workload field; driver validates the physical path roles."""
        if self.output_device() != current.output_device():
            raise RuntimeError("Retained native output filesystem differs.")
        same_roles = replace(
            current,
            pipeline_path=self.pipeline_path,
            input_dir=self.input_dir,
            output_root=self.output_root,
            file_list_path=self.file_list_path,
            report_path=self.report_path,
        )
        if same_roles != self:
            raise RuntimeError("Retained native request workload differs.")


@dataclass(frozen=True)
class NativeBatchObservation:
    """Continuous pipeline-call through cleanup clocks, including preparation."""

    repetition: int
    output_root: str
    image_set_count: int
    invocation_seconds: float
    pre_pipeline_seconds: float
    pipeline_execution_seconds: float
    invocation_started_monotonic_seconds: float
    pipeline_started_monotonic_seconds: float
    completed_monotonic_seconds: float
    assignment_image_set_counts: tuple[tuple[str, int], ...]


@dataclass(frozen=True)
class NativeBatchEnvironment:
    python_executable: str
    python_version: str
    cellprofiler_version: str
    cellprofiler_core_version: str
    numpy_version: str
    scipy_version: str
    temporary_root: str
    temporary_device: int
    host_machine_id: str
    host_node: str
    host_platform: str
    cpu_info_sha256: str
    cpu_affinity: tuple[int, ...]

    def __post_init__(self) -> None:
        affinity = tuple(sorted(self.cpu_affinity))
        if (
            not affinity
            or len(affinity) != len(set(affinity))
            or any(cpu < 0 for cpu in affinity)
        ):
            raise ValueError(
                "Native benchmark CPU affinity must be a nonempty unique CPU set."
            )
        object.__setattr__(self, "cpu_affinity", affinity)
        if (
            not self.host_machine_id
            or not self.host_node
            or not self.host_platform
            or not self.cpu_info_sha256
        ):
            raise ValueError(
                "Native benchmark physical environment identity is incomplete."
            )

    @classmethod
    def capture(cls) -> NativeBatchEnvironment:
        """Capture the declared native environment for both producer and probe."""
        import hashlib
        import os
        import platform
        import sys
        import tempfile
        import cellprofiler
        import cellprofiler_core
        import numpy
        import scipy

        # Linux CPU identity includes topology, model, flags and microcode. These
        # two calibration readings vary within one benchmark and are not identity.
        cpu_identity = "\n".join(
            line
            for line in Path("/proc/cpuinfo").read_text().splitlines()
            if line.partition(":")[0].strip() not in ("cpu MHz", "bogomips")
        )
        if not cpu_identity.strip():
            raise ValueError("Native benchmark Linux CPU identity is empty.")
        return cls(
            python_executable=sys.executable,
            python_version=platform.python_version(),
            cellprofiler_version=cellprofiler.__version__,
            cellprofiler_core_version=cellprofiler_core.__version__,
            numpy_version=numpy.__version__,
            scipy_version=scipy.__version__,
            temporary_root=tempfile.gettempdir(),
            temporary_device=Path(tempfile.gettempdir()).stat().st_dev,
            host_machine_id=Path("/etc/machine-id").read_text().strip(),
            host_node=platform.node(),
            host_platform=platform.platform(),
            cpu_info_sha256=hashlib.sha256(cpu_identity.encode()).hexdigest(),
            cpu_affinity=tuple(sorted(os.sched_getaffinity(0))),
        )

    def require_equivalent(self, current: NativeBatchEnvironment) -> None:
        """Per-case temporary scratch paths are outside the declared benchmark scope."""
        if replace(current, temporary_root=self.temporary_root) != self:
            raise RuntimeError("Retained native declared environment differs.")


@dataclass(frozen=True)
class NativeBatchReport:
    startup_seconds: float
    environment: NativeBatchEnvironment
    request: NativeBatchRequest
    observations: tuple[NativeBatchObservation, ...]

    @classmethod
    def from_payload(cls, payload: Mapping[str, object]) -> NativeBatchReport:
        return cls(
            startup_seconds=payload["startup_seconds"],
            environment=NativeBatchEnvironment(**payload["environment"]),
            request=NativeBatchRequest(**payload["request"]),
            observations=tuple(
                NativeBatchObservation(**row) for row in payload["observations"]
            ),
        )

    def require_complete(self, repetitions: int) -> None:
        """Require whole original runs with actual additive monotonic clocks."""
        if repetitions < 1 or self.request.repetitions != repetitions:
            raise RuntimeError("Retained native request repetition count differs.")
        if tuple(row.repetition for row in self.observations) != tuple(
            range(-1, repetitions)
        ):
            raise RuntimeError(
                "Retained native repetitions are incomplete or reordered."
            )
        output_root = Path(self.request.output_root)
        previous_completed = None
        for row in self.observations:
            invocation = row.invocation_started_monotonic_seconds
            pipeline_start = row.pipeline_started_monotonic_seconds
            completed = row.completed_monotonic_seconds
            if (
                not all(
                    math.isfinite(value)
                    for value in (invocation, pipeline_start, completed)
                )
                or not invocation <= pipeline_start < completed
                or (previous_completed is not None and invocation < previous_completed)
            ):
                raise RuntimeError("Retained native clock boundaries are invalid.")
            for value, expected in (
                (row.invocation_seconds, completed - invocation),
                (row.pre_pipeline_seconds, pipeline_start - invocation),
                (row.pipeline_execution_seconds, completed - pipeline_start),
            ):
                if not math.isclose(value, expected, rel_tol=0.0, abs_tol=1e-9):
                    raise RuntimeError(
                        "Retained native duration disagrees with its clock."
                    )
            run_root = Path(row.output_root)
            if run_root != output_root / str(row.repetition):
                raise RuntimeError(
                    "Retained native output root differs from its request."
                )
            if not any(path.is_file() for path in run_root.rglob("*")):
                raise RuntimeError(
                    "Retained native observation has no physical outputs."
                )
            assignments = row.assignment_image_set_counts
            if (
                row.image_set_count < 1
                or tuple(item[0] for item in assignments)
                != (self.request.assignment_output_subdirectories or ("",))
                or any(item[1] < 1 for item in assignments)
                or sum(item[1] for item in assignments) != row.image_set_count
            ):
                raise RuntimeError("Retained native assignment coverage is invalid.")
            previous_completed = completed
