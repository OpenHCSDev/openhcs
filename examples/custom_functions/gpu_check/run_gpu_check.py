"""GPU check: CuPy preprocessing -> Cellpose (torch) -> scikit-image measurement in one pipeline.

What it does, in order:

1. Reports the GPU, torch, CuPy and Cellpose it found.
2. Converts one array CuPy -> torch -> NumPy with arraybridge directly and reports
   whether each hop shared the buffer (zero-copy) or copied.
3. Measures the host copy Cellpose's own ``eval`` forces (GPU tensor -> NumPy
   before the network runs).
4. Registers the custom functions next to this directory the way the GUI and MCP
   do, compiles and runs the three-step pipeline through the OpenHCS execution
   server on a small synthetic plate, twice, and times each phase.
5. Prints every conversion arraybridge performed during those runs, grouped by
   library pair, device and route, and the peak GPU memory seen by ``nvidia-smi``.

Run it with the Python that has OpenHCS, torch (CUDA), CuPy and Cellpose 3.x:

    python examples/custom_functions/gpu_check/run_gpu_check.py --work-dir /tmp/openhcs-gpu-check

Nothing is written outside ``--work-dir`` except Cellpose's weight cache
(``~/.cellpose`` or ``CELLPOSE_LOCAL_MODELS_PATH``).
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import threading
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCES = HERE.parent
CUSTOM_SOURCES = ("cellpose_segment", "measure_labelled_objects")


def report_environment() -> dict:
    import torch

    facts = {"python": sys.version.split()[0], "torch": torch.__version__,
             "cuda_available": torch.cuda.is_available()}
    if torch.cuda.is_available():
        facts["gpu"] = torch.cuda.get_device_name(0)
        facts["gpu_memory_gb"] = round(torch.cuda.get_device_properties(0).total_memory / 1e9, 1)
    for package in ("cupy", "cellpose", "numpy"):
        try:
            module = __import__(package)
            facts[package] = getattr(module, "__version__", None) or getattr(module, "version", "?")
        except ImportError:
            facts[package] = "NOT INSTALLED"
    return facts


def direct_conversions() -> list[dict]:
    """One array through arraybridge: CuPy -> torch -> NumPy, with buffer addresses."""
    import cupy
    from arraybridge import MemoryType

    from conversion_trace import _buffer_address

    rows = []
    source = cupy.random.random((4, 1024, 1024), dtype=cupy.float32)
    hops = ((MemoryType.CUPY, MemoryType.TORCH), (MemoryType.TORCH, MemoryType.CUPY),
            (MemoryType.TORCH, MemoryType.NUMPY))
    current = source
    for origin, target in hops:
        if origin is MemoryType.TORCH and not hasattr(current, "data_ptr"):
            current = MemoryType.CUPY.convert_to(current, MemoryType.TORCH, 0)
        started = time.perf_counter()
        converted = origin.convert_to(current, target, 0)
        if target is not MemoryType.NUMPY:
            cupy.cuda.Stream.null.synchronize()
        rows.append({
            "hop": f"{origin.value} -> {target.value}",
            "megabytes": round(source.nbytes / 1e6, 1),
            "shares_buffer": _buffer_address(current) == _buffer_address(converted),
            "milliseconds": round((time.perf_counter() - started) * 1e3, 3),
        })
        current = converted if target is not MemoryType.NUMPY else current
    return rows


def cellpose_host_round_trip() -> list[dict]:
    """The copy Cellpose's NumPy-in, NumPy-out ``eval`` forces on a torch-declared caller."""
    import torch

    rows = []
    for shape in ((1, 520, 696), (1, 2048, 2048), (8, 2048, 2048)):
        image = torch.rand(shape, device="cuda", dtype=torch.float32)
        torch.cuda.synchronize()
        started = time.perf_counter()
        host = image.detach().cpu().numpy()
        to_host = time.perf_counter() - started
        rows.append({"shape": list(shape), "megabytes": round(host.nbytes / 1e6, 1),
                     "to_host_ms": round(to_host * 1e3, 2)})
    return rows


class GpuMemorySampler(threading.Thread):
    """Peak ``memory.used`` over the run, from nvidia-smi (covers every process)."""

    def __init__(self) -> None:
        super().__init__(daemon=True)
        self.peak_mib = 0
        self.baseline_mib = self._read()
        self._stop_requested = threading.Event()

    @staticmethod
    def _read() -> int:
        try:
            out = subprocess.run(
                ["nvidia-smi", "--query-gpu=memory.used", "--format=csv,noheader,nounits", "-i", "0"],
                capture_output=True, text=True, timeout=5, check=True,
            ).stdout
            return int(out.strip().splitlines()[0])
        except Exception:
            return 0

    def run(self) -> None:
        while not self._stop_requested.wait(0.25):
            self.peak_mib = max(self.peak_mib, self._read())

    def stop(self) -> None:
        self._stop_requested.set()


def run_pipeline(work_dir: Path, fields: int, tile: int, runs: int) -> dict:
    import io
    from contextlib import redirect_stderr, redirect_stdout

    import openhcs  # noqa: F401
    from objectstate.lazy_factory import ensure_global_config_context
    from openhcs.core.config import (
        GlobalPipelineConfig, LazyPathPlanningConfig, LazyVFSConfig, MaterializeToDisk,
        PathPlanningConfig, PipelineConfig, VFSConfig,
    )
    from openhcs.core.callable_contract import CallableContract
    from openhcs.core.pipeline_document import PipelineDocumentCodec
    from openhcs.core.steps import FunctionStep
    from openhcs.demo.synthetic_data import SyntheticMicroscopyGenerator
    from openhcs.microscopes.imagexpress import ImageXpressHandler
    from openhcs.processing.backends.processors.cupy_processor import percentile_normalize
    from openhcs.processing import custom_functions
    from openhcs.processing.custom_functions import CustomFunctionManager
    from openhcs.runtime.zmq_execution_client import OpenHCSExecutionSubmission, ZMQExecutionClient
    from zmqruntime.execution.responses import ExecutionSubmissionResponse, ExecutionWaitResult

    plate_dir = work_dir / "plate"
    if not plate_dir.exists():
        wells = [f"{row}{column:02d}" for row in "AB" for column in range(1, fields // 2 + 2)][:fields]
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            SyntheticMicroscopyGenerator(
                output_dir=str(plate_dir), grid_size=(1, 1), tile_size=(tile, tile),
                wavelengths=1, z_stack_levels=1, num_cells=max(20, tile * tile // 6000),
                cell_size_range=(8, 14), wells=wells, format="ImageXpress", random_seed=7,
            ).generate_dataset()

    timings: dict[str, float] = {}
    manager = CustomFunctionManager()
    registered = {}
    for name in CUSTOM_SOURCES:
        code = (SOURCES / f"{name}.py").read_text()
        started = time.perf_counter()
        if manager.source_path_for_name(manager.storage_dir, name).exists():
            # A rerun in the same work directory: replace the stored source if it changed.
            if manager.get_function_code(name) != code:
                manager.update_custom_function(name, code)
            manager.load_all_custom_functions()
            registered[name] = getattr(custom_functions, name)
        else:
            [registered[name]] = manager.register_from_code(code, persist=True, emit_signal=False)
        timings[f"register_{name}"] = time.perf_counter() - started

    steps = [
        FunctionStep(name="Normalise (CuPy)", func=(percentile_normalize, {"low_percentile": 0.5})),
        FunctionStep(name="Cellpose nuclei (torch)", func=registered["cellpose_segment"]),
        FunctionStep(name="Measure nuclei (NumPy, scikit-image)",
                     func=(registered["measure_labelled_objects"], {"min_area_px": 20})),
    ]
    declared = [
        {"step": step.name,
         "input": CallableContract.from_callable(function).input_memory_type,
         "output": CallableContract.from_callable(function).output_memory_type}
        for step, function in zip(steps, (percentile_normalize, *registered.values()))
    ]

    suffix = "_gpu_check"
    vfs = VFSConfig(materialization_backend=MaterializeToDisk)
    global_config = GlobalPipelineConfig(
        num_workers=1, dataset_source=ImageXpressHandler, use_threading=False,
        path_planning_config=PathPlanningConfig(output_dir_suffix=suffix), vfs_config=vfs,
    )
    pipeline_config = PipelineConfig(
        path_planning_config=LazyPathPlanningConfig(output_dir_suffix=suffix),
        vfs_config=LazyVFSConfig.from_config(vfs),
    )
    ensure_global_config_context(GlobalPipelineConfig, global_config)

    def submission(**extra):
        return OpenHCSExecutionSubmission(
            subject_id=plate_dir,
            pipeline_document=PipelineDocumentCodec.from_values(
                pipeline_config=pipeline_config, pipeline_steps=steps),
            global_config=global_config, **extra,
        )

    (work_dir / "pipeline.py").write_text(submission().pipeline_code())
    sampler = GpuMemorySampler()
    sampler.start()
    client = ZMQExecutionClient(port=21000 + os.getpid() % 20000, persistent=False)
    try:
        started = time.perf_counter()
        if not client.connect(timeout=1800):
            raise RuntimeError(
                "The execution server did not become ready; read its log under "
                f"{os.environ['XDG_DATA_HOME']}/openhcs/logs."
            )
        timings["server_start_until_ready"] = time.perf_counter() - started
        for run in range(1, runs + 1):
            started = time.perf_counter()
            compile_id = ExecutionSubmissionResponse.from_wire(
                client.submit_compile(submission())).require_execution_id("compile")
            ExecutionWaitResult.from_wire(client.wait_for_completion(compile_id)).require_complete("compile")
            timings[f"compile_run{run}"] = time.perf_counter() - started
            started = time.perf_counter()
            execution_id = ExecutionSubmissionResponse.from_wire(
                client.submit_pipeline(submission(compile_artifact_id=compile_id))
            ).require_execution_id("execute")
            ExecutionWaitResult.from_wire(client.wait_for_completion(execution_id)).require_complete("execute")
            timings[f"execute_run{run}"] = time.perf_counter() - started
    finally:
        sampler.stop()
        client.disconnect()

    results = plate_dir.parent / f"{plate_dir.name}{suffix}" / "results"
    return {
        "declared_memory_types": declared,
        "timings_seconds": {name: round(value, 2) for name, value in timings.items()},
        "fields": fields,
        "gpu_memory_mib": {"before": sampler.baseline_mib, "peak": sampler.peak_mib},
        "result_files": {
            "label_tiffs": len(list(results.glob("*.labels.tif"))),
            "count_tables": len(list(results.glob("*cellpose_counts*.csv"))),
            "object_tables": len(list(results.glob("*object_measurements*.csv"))),
        },
        "pipeline_code": str(work_dir / "pipeline.py"),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--fields", type=int, default=4)
    parser.add_argument("--tile", type=int, default=512, help="synthetic image side in pixels")
    parser.add_argument("--runs", type=int, default=2)
    arguments = parser.parse_args()
    work_dir = arguments.work_dir.resolve()
    work_dir.mkdir(parents=True, exist_ok=True)

    trace = work_dir / "conversions.jsonl"
    trace.unlink(missing_ok=True)
    # Inherited by the execution server and its workers, which are separate processes.
    os.environ["PYTHONPATH"] = os.pathsep.join(
        filter(None, (str(HERE), os.environ.get("PYTHONPATH")))
    )
    os.environ.setdefault("XDG_DATA_HOME", str(work_dir / "data-home"))
    os.environ.setdefault("QT_QPA_PLATFORM", "offscreen")
    sys.path.insert(0, str(HERE))

    report = {"environment": report_environment()}
    print(json.dumps(report["environment"], indent=1), flush=True)
    if not report["environment"]["cuda_available"]:
        raise SystemExit("torch reports no CUDA device; this check needs one.")
    report["direct_conversions"] = direct_conversions()
    report["cellpose_host_round_trip"] = cellpose_host_round_trip()

    os.environ["OPENHCS_CONVERSION_TRACE"] = str(trace)
    report["pipeline"] = run_pipeline(work_dir, arguments.fields, arguments.tile, arguments.runs)
    os.environ.pop("OPENHCS_CONVERSION_TRACE")

    from conversion_trace import summarise

    report["pipeline_conversions"] = summarise(str(trace)) if trace.exists() else []
    (work_dir / "gpu_check_report.json").write_text(json.dumps(report, indent=1))
    for section in ("direct_conversions", "cellpose_host_round_trip", "pipeline", "pipeline_conversions"):
        print(f"\n== {section}")
        print(json.dumps(report[section], indent=1))
    print(f"\nreport: {work_dir / 'gpu_check_report.json'}")


if __name__ == "__main__":
    main()
