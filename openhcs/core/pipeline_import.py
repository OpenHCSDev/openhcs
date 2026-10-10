"""Pipeline file formats a dataset's pipeline can be loaded from, keyed by suffix.

OpenHCS reads its own pipeline documents (``.py``); a domain registers other
formats from its extension modules (CellProfiler registers ``.cppipe``).
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from pathlib import Path
from typing import ClassVar

from metaclass_registry import AutoRegisterMeta

from openhcs.core.dataset_sources.discovery import domain_registry_config
from openhcs.core.pipeline_document import PipelineDocument, PipelineDocumentCodec


class PipelineImporter(ABC, metaclass=AutoRegisterMeta):
    """Reads one pipeline file format into a PipelineDocument."""

    __registry_config__ = domain_registry_config(
        key_attribute="suffix",
        registry_name="pipeline importer",
    )
    suffix: ClassVar[str | None] = None
    title: ClassVar[str]

    @classmethod
    @abstractmethod
    def read(cls, path: Path) -> PipelineDocument: ...

    @staticmethod
    def for_path(path: Path) -> type["PipelineImporter"]:
        try:
            return PipelineImporter.__registry__[path.suffix]
        except KeyError:
            suffixes = ", ".join(sorted(PipelineImporter.__registry__))
            raise ValueError(
                f"Pipeline files are {suffixes}; got {path.name}."
            ) from None

    @staticmethod
    def file_filter() -> str:
        """A file-dialog filter derived from the registered importers."""

        return ";;".join(
            f"{importer.title} (*{suffix})"
            for suffix, importer in PipelineImporter.__registry__.items()
        )


class PipelineDocumentImporter(PipelineImporter):
    """OpenHCS's own pycodified pipeline document."""

    suffix = ".py"
    title = "OpenHCS Pipelines"

    @classmethod
    def read(cls, path: Path) -> PipelineDocument:
        return PipelineDocumentCodec.from_source(path.read_text(encoding="utf-8"))
