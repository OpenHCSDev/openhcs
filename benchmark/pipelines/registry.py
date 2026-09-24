"""Registry of benchmark pipelines."""

from __future__ import annotations

from abc import ABC
from collections.abc import Iterator, Mapping
from typing import ClassVar

from metaclass_registry import AutoRegisterMeta

from benchmark.contracts.pipeline import PipelineSpec
from benchmark.contracts.values import BenchmarkParameterMap


class BenchmarkPipelineDeclaration(ABC, metaclass=AutoRegisterMeta):
    """Registered declaration for one benchmark pipeline."""

    __registry__: ClassVar[dict[str, type[BenchmarkPipelineDeclaration]]] = {}
    __registry_key__ = "name"
    __skip_if_no_key__ = True

    name: ClassVar[str | None] = None
    description: ClassVar[str]
    parameters: ClassVar[BenchmarkParameterMap] = {}

    @classmethod
    def to_spec(cls) -> PipelineSpec:
        """Materialize this declaration as a public pipeline spec."""
        if cls.name is None:
            raise ValueError(f"{cls.__name__} must declare a pipeline name.")
        return PipelineSpec(
            name=cls.name,
            description=cls.description,
            parameters=cls.parameters,
        )


class NucleiSegmentationPipeline(BenchmarkPipelineDeclaration):
    """BBBC021 nuclei segmentation benchmark pipeline."""

    name = "nuclei_segmentation"
    description = "BBBC021 nuclei segmentation (CellProfiler-equivalent)"
    parameters: ClassVar[BenchmarkParameterMap] = {"cppipe_reference_index": 0}


def pipeline_specs() -> tuple[PipelineSpec, ...]:
    """Return materialized benchmark pipeline specs."""
    return tuple(
        declaration.to_spec()
        for declaration in BenchmarkPipelineDeclaration.__registry__.values()
    )


class _PipelineSpecView(Mapping[str, PipelineSpec]):
    """Compatibility mapping projected from registered declarations on access."""

    def __getitem__(self, name: str) -> PipelineSpec:
        return BenchmarkPipelineDeclaration.__registry__[name].to_spec()

    def __iter__(self) -> Iterator[str]:
        return iter(BenchmarkPipelineDeclaration.__registry__)

    def __len__(self) -> int:
        return len(BenchmarkPipelineDeclaration.__registry__)


PIPELINE_REGISTRY: Mapping[str, PipelineSpec] = _PipelineSpecView()
NUCLEI_SEGMENTATION = NucleiSegmentationPipeline.to_spec()


def get_pipeline_spec(name: str) -> PipelineSpec:
    """
    Retrieve pipeline specification by name.

    Raises:
        KeyError: if pipeline name is unknown.
    """
    try:
        return PIPELINE_REGISTRY[name]
    except KeyError as exc:
        raise KeyError(
            f"Unknown pipeline '{name}'. Available: {list(PIPELINE_REGISTRY)}"
        ) from exc
