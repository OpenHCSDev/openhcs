"""Every saved Python document assigns its dataclass fields and loads them back."""

from __future__ import annotations

import ast

import pytest
from pycodify import SourceDocument

import openhcs.serialization.pycodify_formatters  # noqa: F401
from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
from openhcs.core.config_document import ConfigDocument
from openhcs.core.function_step_document import FunctionStepDocumentCodec
from openhcs.core.function_step_transport import (
    FunctionStepTransportAuthority,
    PipelineStepsDocument,
)
from openhcs.core.pipeline_document import PipelineDocument, PipelineDocumentCodec
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends import cellprofiler as cellprofiler_backend


def _steps() -> list[FunctionStep]:
    return FunctionStepTransportAuthority.normalize_pipeline(
        [FunctionStep(func=cellprofiler_backend.crop, name="Crop")]
    )


def _document_types(root: type = SourceDocument) -> list[type[SourceDocument]]:
    found: list[type[SourceDocument]] = []
    for subclass in root.__subclasses__():
        if subclass.__module__.startswith("openhcs."):
            found.append(subclass)
        found.extend(_document_types(subclass))
    return found


# The names inside saved files. They are durable: a user's saved pipeline,
# step or config must keep loading, so a field rename has to fail here.
SAVED_NAMES = {
    "ConfigDocument": ("config",),
    "PipelineStepsDocument": ("pipeline_steps",),
    "PipelineDocument": ("pipeline_steps", "pipeline_config"),
    "FunctionStepDocument": ("step",),
}


def _sample(document_type: type[SourceDocument]) -> SourceDocument:
    samples = {
        "ConfigDocument": lambda: ConfigDocument(config=GlobalPipelineConfig(num_workers=3)),
        "PipelineStepsDocument": lambda: PipelineStepsDocument(pipeline_steps=_steps()),
        "PipelineDocument": lambda: PipelineDocumentCodec.from_values(
            pipeline_config=PipelineConfig(), pipeline_steps=_steps()
        ),
        "FunctionStepDocument": lambda: FunctionStepDocumentCodec.from_value(_steps()[0]),
    }
    return samples[document_type.__name__]()


def _assigned_names(source: str) -> tuple[str, ...]:
    return tuple(
        target.id
        for statement in ast.parse(source).body
        if isinstance(statement, ast.Assign)
        for target in statement.targets
        if isinstance(target, ast.Name)
    )


def test_every_document_kind_is_covered() -> None:
    assert {kind.__name__ for kind in _document_types()} == set(SAVED_NAMES)


@pytest.mark.parametrize("document_type", _document_types(), ids=lambda kind: kind.__name__)
@pytest.mark.parametrize("clean_mode", (True, False))
def test_document_round_trips_under_its_field_names(
    document_type: type[SourceDocument], clean_mode: bool
) -> None:
    document = _sample(document_type)

    source = document.to_source(clean_mode=clean_mode)
    restored = document_type.from_source(source)

    assert document_type.assignment_names() == SAVED_NAMES[document_type.__name__]
    assert _assigned_names(source) == SAVED_NAMES[document_type.__name__]
    assert type(restored) is document_type
    assert restored.to_source(clean_mode=clean_mode) == source


def test_config_document_restores_an_equal_config() -> None:
    document = _sample(ConfigDocument)

    assert ConfigDocument.from_source(document.to_source(clean_mode=True)) == document


def test_steps_only_file_is_a_pipeline_with_the_default_config() -> None:
    steps_source = _sample(PipelineStepsDocument).to_source(clean_mode=True)

    pipeline = PipelineDocumentCodec.from_source(steps_source)

    assert isinstance(pipeline.pipeline_config, PipelineConfig)
    assert len(pipeline.pipeline_steps) == 1
    assert pipeline.source_text == steps_source


def test_pipeline_file_gives_its_steps_to_the_steps_only_reader() -> None:
    namespace: dict[str, object] = {}
    exec(PipelineDocumentCodec.render(_sample(PipelineDocument)), namespace)

    (step,) = FunctionStepTransportAuthority.pipeline_steps_from_namespace(namespace)

    assert step.name == "Crop"
