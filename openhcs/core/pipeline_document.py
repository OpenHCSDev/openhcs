"""Python document for one OpenHCS pipeline: its config and steps."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field, replace

from openhcs.core.config import PipelineConfig
from openhcs.core.function_step_transport import (
    FunctionStepTransportAuthority,
    PipelineStepsDocument,
)
from openhcs.core.steps.function_step import FunctionStep


@dataclass(frozen=True, slots=True, kw_only=True)
class PipelineDocument(PipelineStepsDocument):
    """Normalized public configuration and steps for one pipeline.

    A file that assigns only the steps is a pipeline with the default config.
    """

    pipeline_config: PipelineConfig = field(default_factory=PipelineConfig)
    source_text: str | None = field(default=None, init=False)

    def read_from(self, source_text: str | None) -> PipelineDocument:
        """Return this document carrying the source text it was read from."""

        document = replace(self)
        object.__setattr__(document, "source_text", source_text)
        return document


class PipelineDocumentCodec:
    """Validate, parse, and render the pipeline Python document."""

    HEADER = "# OpenHCS pipeline"

    @classmethod
    def from_values(
        cls,
        *,
        pipeline_config: PipelineConfig,
        pipeline_steps: Sequence[FunctionStep],
    ) -> PipelineDocument:
        """Build a document from typed values and normalize its steps."""

        if not isinstance(pipeline_config, PipelineConfig):
            raise TypeError(
                "pipeline_config must be a PipelineConfig, "
                f"got {type(pipeline_config).__name__}."
            )
        return PipelineDocument(
            pipeline_config=pipeline_config,
            pipeline_steps=FunctionStepTransportAuthority.normalized_steps(
                list(pipeline_steps)
            ),
        )

    @classmethod
    def from_namespace(
        cls,
        namespace: Mapping[str, object],
    ) -> PipelineDocument:
        """Read the public assignments from an executed namespace."""

        document = PipelineDocument.from_namespace(namespace)
        if type(document.pipeline_steps) is not list:
            raise TypeError(
                "pipeline_steps must be a list[FunctionStep], "
                f"got {type(document.pipeline_steps).__name__}."
            )
        return cls.from_values(
            pipeline_config=document.pipeline_config,
            pipeline_steps=document.pipeline_steps,
        )

    @classmethod
    def from_source(cls, source: str) -> PipelineDocument:
        """Execute Python source and read its pipeline assignments."""

        namespace: dict[str, object] = {}
        code = compile(source, "<openhcs-pipeline-document>", "exec")
        exec(code, namespace)
        return cls.from_namespace(namespace).read_from(source)

    @classmethod
    def execution_source(cls, document: PipelineDocument) -> str:
        """Return the source it was read from, otherwise freshly rendered source."""

        if document.source_text is not None:
            return document.source_text
        return cls.render(document)

    @classmethod
    def render(
        cls,
        document: PipelineDocument,
        *,
        clean_mode: bool = True,
    ) -> str:
        """Render a validated pipeline document as reviewable Python source."""

        import openhcs.serialization.pycodify_formatters  # noqa: F401

        return cls.from_values(
            pipeline_config=document.pipeline_config,
            pipeline_steps=document.pipeline_steps,
        ).to_source(header=cls.HEADER, clean_mode=clean_mode)
