"""Native-environment entry point for warm, batched CellProfiler observations.

Run this file with the native CellProfiler interpreter, not the OpenHCS one.
The request is a JSON object matching NativeBatchRequest. Imports, Java startup,
pipeline loading and the first complete warm-up batch precede timed repeats.
"""

from __future__ import annotations

import json
import logging
import platform
import sys
import tempfile
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Optional

import cellprofiler
import cellprofiler_core
import numpy
import scipy
from cellprofiler_core.constants.pipeline import EXIT_STATUS
from cellprofiler_core.measurement import Measurements
from cellprofiler_core.pipeline import Pipeline
from cellprofiler_core.preferences import (
    set_awt_headless,
    set_default_image_directory,
    set_default_output_directory,
    set_headless,
)
from cellprofiler_core.utilities.java import start_java, stop_java

from native_batch_barrier import NativeBatchStartBarrier


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


@dataclass
class NativeBatchClock:
    invocation_started: float
    first_module_started: Optional[float] = None
    image_set_count: int = 0

    def before_module(self, module, module_count, image_set_index, image_set_count):
        if self.first_module_started is None:
            self.first_module_started = time.perf_counter()
        self.image_set_count = image_set_count


@dataclass(frozen=True)
class NativeBatchObservation:
    repetition: int
    output_root: str
    image_set_count: int
    invocation_seconds: float
    pre_first_module_seconds: float
    first_module_through_post_run_seconds: float
    invocation_started_monotonic_seconds: float
    first_module_started_monotonic_seconds: float
    completed_monotonic_seconds: float


@dataclass(frozen=True)
class NativeBatchEnvironment:
    python_executable: str
    python_version: str
    cellprofiler_version: str
    cellprofiler_core_version: str
    numpy_version: str
    scipy_version: str
    temporary_root: str


@dataclass(frozen=True)
class NativeBatchReport:
    startup_seconds: float
    environment: NativeBatchEnvironment
    request: NativeBatchRequest
    observations: tuple[NativeBatchObservation, ...]


def main() -> None:
    request = NativeBatchRequest(**json.loads(Path(sys.argv[1]).read_text()))
    if (
        request.expected_image_sets is not None and request.expected_image_sets < 1
    ) or request.repetitions < 1:
        raise ValueError("Batch count and repetitions must be positive")
    if request.first_image_set < 1 or (
        request.last_image_set is not None
        and request.last_image_set < request.first_image_set
    ):
        raise ValueError("Native image-set range must be positive and ordered")
    if request.start_barrier_root is None:
        if request.start_barrier_job_count != 1 or request.start_barrier_job_index != 0:
            raise ValueError("Native batch barrier membership requires a root.")
        start_barrier = None
    else:
        start_barrier = NativeBatchStartBarrier(
            Path(request.start_barrier_root),
            request.start_barrier_job_count,
            request.start_barrier_job_index,
        )
    logging.basicConfig(level=logging.WARNING)
    set_headless()
    set_awt_headless(True)
    set_default_image_directory(request.input_dir)
    startup_started = time.perf_counter()
    start_java()
    try:
        pipeline = Pipeline()
        pipeline.load(request.pipeline_path)
        if request.file_list_path is not None:
            pipeline.read_file_list(request.file_list_path)
        else:
            pipeline.add_pathnames_to_file_list(
                [
                    str(path)
                    for path in Path(request.input_dir).rglob("*")
                    if path.is_file()
                ]
            )
        startup_seconds = time.perf_counter() - startup_started
        observations = []
        for repetition in range(-1, request.repetitions):
            if repetition >= 0 and start_barrier is not None:
                start_barrier.wait(repetition)
            invocation_started = time.perf_counter()
            output_root = Path(request.output_root) / str(repetition)
            output_root.mkdir(parents=True, exist_ok=False)
            set_default_output_directory(str(output_root))
            measurements = Measurements(image_set_start=request.first_image_set)
            measurements.is_first_image = True
            clock = NativeBatchClock(invocation_started)
            try:
                for measurements in pipeline.run_with_yield(
                    image_set_start=request.first_image_set,
                    image_set_end=request.last_image_set,
                    run_in_background=False,
                    status_callback=clock.before_module,
                    initial_measurements=measurements,
                ):
                    pass
                status = measurements.get_experiment_measurement(EXIT_STATUS)
                if status != "Complete":
                    raise RuntimeError(
                        "Native CellProfiler batch did not complete: " + str(status)
                    )
                if clock.image_set_count < 1 or (
                    request.expected_image_sets is not None
                    and clock.image_set_count != request.expected_image_sets
                ):
                    raise RuntimeError(
                        "Native image-set count differs from requested workload"
                    )
                if clock.first_module_started is None:
                    raise RuntimeError("Native batch executed no analysis modules")
            finally:
                measurements.close()
            completed = time.perf_counter()
            observations.append(
                NativeBatchObservation(
                    repetition=repetition,
                    output_root=str(output_root),
                    image_set_count=clock.image_set_count,
                    invocation_seconds=completed - clock.invocation_started,
                    pre_first_module_seconds=clock.first_module_started
                    - clock.invocation_started,
                    first_module_through_post_run_seconds=completed
                    - clock.first_module_started,
                    invocation_started_monotonic_seconds=clock.invocation_started,
                    first_module_started_monotonic_seconds=clock.first_module_started,
                    completed_monotonic_seconds=completed,
                )
            )
        report = asdict(
            NativeBatchReport(
                startup_seconds=startup_seconds,
                environment=NativeBatchEnvironment(
                    python_executable=sys.executable,
                    python_version=platform.python_version(),
                    cellprofiler_version=cellprofiler.__version__,
                    cellprofiler_core_version=cellprofiler_core.__version__,
                    numpy_version=numpy.__version__,
                    scipy_version=scipy.__version__,
                    temporary_root=tempfile.gettempdir(),
                ),
                request=request,
                observations=tuple(observations),
            )
        )
        if request.report_path is not None:
            report_path = Path(request.report_path)
            report_path.parent.mkdir(parents=True, exist_ok=True)
            report_path.write_text(json.dumps(report, indent=2))
        print(json.dumps(report))
    finally:
        stop_java()


if __name__ == "__main__":
    main()
