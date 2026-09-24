"""Benchmark scenario lookup stays derived from its declarations."""

from typing import ClassVar

from benchmark.contracts.values import BenchmarkParameterMap
from benchmark.pipelines.registry import (
    PIPELINE_REGISTRY,
    BenchmarkPipelineDeclaration,
    get_pipeline_spec,
    pipeline_specs,
)


def test_public_pipeline_view_follows_registered_declarations() -> None:
    name = "test_live_pipeline_view"

    class AdditionalPipeline(BenchmarkPipelineDeclaration):
        name = "test_live_pipeline_view"
        description = "A test-only benchmark scenario"
        parameters: ClassVar[BenchmarkParameterMap] = {"cppipe_reference_index": 2}

    try:
        declared = AdditionalPipeline.to_spec()
        assert name in PIPELINE_REGISTRY
        assert PIPELINE_REGISTRY[name] == declared
        assert get_pipeline_spec(name) == declared
        assert declared in pipeline_specs()
    finally:
        BenchmarkPipelineDeclaration.__registry__.pop(name)

    assert name not in PIPELINE_REGISTRY
