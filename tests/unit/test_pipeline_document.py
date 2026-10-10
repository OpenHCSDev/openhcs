"""Canonical pipeline Python document contracts."""

from __future__ import annotations

import pytest

from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
from openhcs.core.function_step_transport import FunctionStepTransportAuthority
from openhcs.core.pipeline_document import (
    PipelineDocument,
    PipelineDocumentCodec,
    PipelineDocumentField,
)
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends import cellprofiler as cellprofiler_backend
from openhcs.processing.backends.lib_registry.registry_service import RegistryService


def _step() -> FunctionStep:
    return FunctionStep(func=cellprofiler_backend.crop, name="Crop")


def test_pipeline_document_fields_own_exact_public_names() -> None:
    assert tuple(field.value for field in PipelineDocumentField) == (
        "pipeline_config",
        "pipeline_steps",
    )


def test_pipeline_document_round_trip_renders_config_and_normalized_steps() -> None:
    document = PipelineDocumentCodec.from_values(
        pipeline_config=PipelineConfig(),
        pipeline_steps=[_step()],
    )

    source = PipelineDocumentCodec.render(document)
    restored = PipelineDocumentCodec.from_source(source)

    assert "pipeline_config = PipelineConfig(" in source
    assert "pipeline_steps = [" in source
    assert isinstance(restored.pipeline_config, PipelineConfig)
    assert type(restored.pipeline_steps) is list
    assert len(restored.pipeline_steps) == 1
    assert restored.pipeline_steps[0].func is RegistryService.registered_callable(
        cellprofiler_backend.crop
    )
    assert PipelineDocumentCodec.render(restored) == source
    assert restored.original_source == source
    assert PipelineDocumentCodec.execution_source(restored) == source


def test_from_values_copies_the_step_sequence_and_delegates_normalization(
    monkeypatch,
) -> None:
    step = _step()
    source_steps = [step]
    calls: list[list[FunctionStep]] = []

    def normalize_pipeline(steps):
        calls.append(steps)
        return list(steps)

    monkeypatch.setattr(
        FunctionStepTransportAuthority,
        "normalize_pipeline",
        normalize_pipeline,
    )

    document = PipelineDocumentCodec.from_values(
        pipeline_config=PipelineConfig(),
        pipeline_steps=source_steps,
    )

    assert calls == [[step]]
    assert document.pipeline_steps == source_steps
    assert document.pipeline_steps is not source_steps


def test_execution_source_preserves_reviewed_source_without_parallel_state() -> None:
    canonical = PipelineDocumentCodec.render(
        PipelineDocumentCodec.from_values(
            pipeline_config=PipelineConfig(),
            pipeline_steps=[],
        )
    )
    reviewed_source = f"{canonical}\n# reviewed source marker\n"

    document = PipelineDocumentCodec.from_source(reviewed_source)

    assert document.original_source == reviewed_source
    assert PipelineDocumentCodec.execution_source(document) == reviewed_source


@pytest.mark.parametrize(
    ("namespace", "error_type", "message"),
    (
        (
            {"pipeline_config": PipelineConfig()},
            ValueError,
            "pipeline_steps",
        ),
        (
            {
                "pipeline_config": GlobalPipelineConfig(),
                "pipeline_steps": [],
            },
            TypeError,
            "PipelineConfig",
        ),
        (
            {
                "pipeline_config": PipelineConfig(),
                "pipeline_steps": (),
            },
            TypeError,
            "list",
        ),
        (
            {
                "pipeline_config": PipelineConfig(),
                "pipeline_steps": [object()],
            },
            TypeError,
            "FunctionStep",
        ),
    ),
)
def test_from_namespace_requires_steps_and_validates_explicit_types(
    namespace: dict[str, object],
    error_type: type[Exception],
    message: str,
) -> None:
    with pytest.raises(error_type, match=message):
        PipelineDocumentCodec.from_namespace(namespace)


def test_from_namespace_defaults_missing_pipeline_config() -> None:
    document = PipelineDocumentCodec.from_namespace({"pipeline_steps": [_step()]})

    assert document.pipeline_config == PipelineConfig()


def test_from_namespace_does_not_accept_aliases() -> None:
    with pytest.raises(ValueError, match="pipeline_steps"):
        PipelineDocumentCodec.from_namespace(
            {
                "config": PipelineConfig(),
                "steps": [_step()],
            }
        )


def test_render_revalidates_direct_pipeline_document_instances() -> None:
    invalid = PipelineDocument(  # type: ignore[arg-type]
        pipeline_config=GlobalPipelineConfig(),
        pipeline_steps=[],
    )

    with pytest.raises(TypeError, match="PipelineConfig"):
        PipelineDocumentCodec.render(invalid)


def test_pipeline_document_preserves_intrinsic_volume_source_declaration():
    import pickle
    from openhcs.core.config import LazySourceBindingsConfig
    from openhcs.core.source_bindings import (
        CompiledSourceBindingPlan,
        StepSourceBindingsConfig,
    )
    from openhcs.core.source_spatial_domain import VolumeSourceSpatialDomain

    domain = VolumeSourceSpatialDomain()
    document = PipelineDocumentCodec.from_values(
        pipeline_config=PipelineConfig(
            source_bindings_config=LazySourceBindingsConfig(
                source_spatial_domain=domain
            )
        ),
        pipeline_steps=[],
    )
    source = PipelineDocumentCodec.render(document)
    restored = PipelineDocumentCodec.from_source(source)
    assert (
        restored.pipeline_config.source_bindings_config.source_spatial_domain == domain
    )
    plan = CompiledSourceBindingPlan.from_config(
        StepSourceBindingsConfig(source_spatial_domain=domain)
    )
    assert pickle.loads(pickle.dumps(plan)).source_spatial_domain == domain
