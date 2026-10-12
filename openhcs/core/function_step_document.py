"""Python document for one OpenHCS FunctionStep."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass

from openhcs.core.function_step_transport import FunctionStepTransportAuthority
from openhcs.core.steps.function_step import FunctionStep
from pycodify import SourceDocument


@dataclass(frozen=True, slots=True)
class FunctionStepDocument(SourceDocument):
    """Normalized public declaration for one FunctionStep."""

    step: FunctionStep


class FunctionStepDocumentCodec:
    """Validate, parse, and render the FunctionStep Python document."""

    HEADER = "# Function Step"

    @classmethod
    def from_value(cls, step: FunctionStep) -> FunctionStepDocument:
        """Build a document from one typed and transport-normalized step."""

        cls._require_step(step)
        normalized_step = FunctionStepTransportAuthority.normalize_step(step)
        cls._require_step(normalized_step)
        return FunctionStepDocument(step=normalized_step)

    @classmethod
    def from_namespace(
        cls,
        namespace: Mapping[str, object],
    ) -> FunctionStepDocument:
        """Read the public step assignment from an executed namespace."""

        return cls.from_value(FunctionStepDocument.from_namespace(namespace).step)

    @classmethod
    def from_source(cls, source: str) -> FunctionStepDocument:
        """Execute Python source and read its FunctionStep assignment."""

        return cls.from_value(FunctionStepDocument.from_source(source).step)

    @classmethod
    def render(
        cls,
        document: FunctionStepDocument,
        *,
        clean_mode: bool = True,
    ) -> str:
        """Render a validated FunctionStep document as reviewable Python source."""

        import openhcs.serialization.pycodify_formatters  # noqa: F401

        return cls.from_value(document.step).to_source(
            header=cls.HEADER,
            clean_mode=clean_mode,
        )

    @staticmethod
    def _require_step(value: object) -> None:
        if not isinstance(value, FunctionStep):
            raise TypeError(f"step must be a FunctionStep, got {type(value).__name__}.")
