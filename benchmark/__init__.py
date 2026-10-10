"""Public API for the benchmark platform."""

from __future__ import annotations

import openhcs as _openhcs_dependency_bootstrap  # noqa: F401
from python_introspect import lazy_exports

__all__ = lazy_exports(
    globals(),
    {
        "benchmark.contracts.dataset": (
            "DatasetSpec",
            "AcquiredDataset",
        ),
        "benchmark.contracts.metric": (
            "MetricCollector",
        ),
        "benchmark.contracts.tool_adapter": (
            "BenchmarkResult",
            "ToolAdapter",
            "ToolAdapterError",
            "ToolExecutionError",
            "ToolNotInstalledError",
            "ToolVersionError",
        ),
        "benchmark.datasets.acquire": (
            "DatasetAcquisitionError",
            "acquire_dataset",
        ),
        "benchmark.datasets": (
            "BBBC021_SINGLE_PLATE",
            "DATASET_REGISTRY",
        ),
        "benchmark.datasets.registry": (
            "get_dataset_spec",
        ),
        "benchmark.contracts.pipeline": (
            "PipelineSpec",
        ),
        "benchmark.pipelines": (
            "NUCLEI_SEGMENTATION",
        ),
        "benchmark.pipelines.registry": (
            "PIPELINE_REGISTRY",
            "get_pipeline_spec",
        ),
        "benchmark.metrics.time": (
            "TimeMetric",
        ),
        "benchmark.metrics.memory": (
            "MemoryMetric",
        ),
        "benchmark.progress": (
            "BenchmarkCaseProgress",
            "BenchmarkProgressEvent",
            "BenchmarkProgressEventKind",
            "BenchmarkProgressSnapshot",
            "iter_progress_events",
            "summarize_progress",
        ),
        "benchmark.adapters.cellprofiler": (
            "CellProfilerAdapter",
        ),
        "benchmark.adapters.openhcs": (
            "OpenHCSAdapter",
        ),
        "benchmark.runner": (
            "CellProfilerCompatibilityResult",
            "run_benchmark",
            "run_cellprofiler_compatibility_benchmark",
        ),
    },
)
