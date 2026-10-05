"""Native-environment entry point for warm, batched CellProfiler observations.

Run this file with the native CellProfiler interpreter, not the OpenHCS one.
The request is a JSON object matching NativeBatchRequest. Imports, Java startup,
pipeline loading and the first complete warm-up batch precede timed repeats.
"""

from __future__ import annotations

import json
import logging
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Optional

from native_batch_barrier import NativeBatchStartBarrier
from native_batch_contracts import (
    NativeBatchRequest,
    NativeBatchObservation,
    NativeBatchEnvironment,
    NativeBatchReport,
)


@dataclass
class NativeBatchClock:
    invocation_started: float
    pipeline_started: Optional[float] = None
    image_set_count: int = 0

    def before_module(self, module, module_count, image_set_index, image_set_count):
        self.image_set_count = image_set_count


def main() -> None:
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
            clock = NativeBatchClock(invocation_started)
            image_set_count = 0
            assignment_counts = []
            for assignment in request.assignment_output_subdirectories or ("",):
                assignment_root = output_root / assignment
                assignment_root.mkdir(parents=True, exist_ok=True)
                set_default_output_directory(str(assignment_root))
                measurements = Measurements(image_set_start=request.first_image_set)
                measurements.is_first_image = True
                clock.image_set_count = 0
                try:
                    # Group preparation can load and process every source image.
                    # Keep one continuous execution interval for the whole batch.
                    if clock.pipeline_started is None:
                        clock.pipeline_started = time.perf_counter()
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
                            "Native CellProfiler assignment did not complete: "
                            + str(status)
                        )
                    if clock.image_set_count < 1 or clock.pipeline_started is None:
                        raise RuntimeError(
                            "Native assignment executed no analysis modules"
                        )
                    image_set_count += clock.image_set_count
                    assignment_counts.append((assignment, clock.image_set_count))
                finally:
                    measurements.close()
            if (
                request.expected_image_sets is not None
                and image_set_count != request.expected_image_sets
            ):
                raise RuntimeError(
                    "Native image-set count differs from requested workload"
                )
            completed = time.perf_counter()
            observations.append(
                NativeBatchObservation(
                    repetition=repetition,
                    output_root=str(output_root),
                    image_set_count=image_set_count,
                    invocation_seconds=completed - clock.invocation_started,
                    pre_pipeline_seconds=clock.pipeline_started
                    - clock.invocation_started,
                    pipeline_execution_seconds=completed
                    - clock.pipeline_started,
                    invocation_started_monotonic_seconds=clock.invocation_started,
                    pipeline_started_monotonic_seconds=clock.pipeline_started,
                    completed_monotonic_seconds=completed,
                    assignment_image_set_counts=tuple(assignment_counts),
                )
            )
        report = asdict(
            NativeBatchReport(
                startup_seconds=startup_seconds,
                environment=NativeBatchEnvironment.capture(),
                request=request,
                observations=tuple(observations),
            )
        )
        if request.report_path is not None:
            report_path = Path(request.report_path)
            report_path.parent.mkdir(parents=True, exist_ok=True)
            report_path.write_text(json.dumps(report, indent=2))
        else:
            print(json.dumps(report))
    finally:
        stop_java()


if __name__ == "__main__":
    if sys.argv[1:] == ["--environment"]:
        print(json.dumps(asdict(NativeBatchEnvironment.capture())))
    else:
        main()
