"""Which dataset source opens a dataset: one registered source, or detection.

A config field holds a :class:`DatasetSourceChoice` class. Every registered
:class:`~openhcs.core.dataset_sources.source.DatasetSource` is a choice, and
:class:`AutoDetectedSource` chooses by detection. Boundaries (forms, MCP, saved
configs) spell a choice by its ``source_name``; this module stays light so
configuration can import it.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from pathlib import Path
from typing import TYPE_CHECKING, ClassVar

from python_introspect import AnnotationChoices

if TYPE_CHECKING:
    from polystore.filemanager import FileManager

    from openhcs.core.dataset_sources.source import DatasetSource
    from openhcs.core.source_bindings import SourceBindingsConfig


class DatasetSourceChoice(ABC):
    """A class that selects the dataset source for one dataset root."""

    source_name: ClassVar[str]

    @staticmethod
    def choices() -> tuple[type["DatasetSourceChoice"], ...]:
        """Detection first, then every registered source in registry order."""

        from openhcs.core.dataset_sources.source import DatasetSource

        return (AutoDetectedSource, *DatasetSource.__registry__.values())

    @staticmethod
    def named(name: str) -> type["DatasetSourceChoice"]:
        """Decode one boundary spelling."""

        for choice in DatasetSourceChoice.choices():
            if choice.source_name == name:
                return choice
        raise ValueError(
            f"Unknown dataset source {name!r}; available: "
            f"{[choice.source_name for choice in DatasetSourceChoice.choices()]}."
        )

    @classmethod
    def coerce(cls, value: object) -> type["DatasetSourceChoice"]:
        """Accept a choice class or its boundary spelling."""

        if isinstance(value, str):
            return cls.named(value)
        if isinstance(value, type) and issubclass(value, DatasetSourceChoice):
            return value
        raise TypeError(f"Expected a dataset source choice, got {value!r}.")

    @classmethod
    @abstractmethod
    def source_type_for(
        cls,
        root: Path,
        filemanager: "FileManager",
        source_bindings: "SourceBindingsConfig | None",
    ) -> "type[DatasetSource]":
        """Return the source class that opens ``root``."""

    @classmethod
    def open(
        cls,
        root: str | Path,
        *,
        filemanager: "FileManager",
        pattern_format: str | None = None,
        source_bindings_config: "SourceBindingsConfig | None" = None,
    ) -> "DatasetSource":
        """Construct the selected source bound to ``root``."""

        from openhcs.core.dataset_sources.source import DeclaredFileSource
        from openhcs.core.source_bindings import source_bindings_defaults_to_base

        root = Path(root)
        source_bindings = (
            None
            if source_bindings_config is None
            else source_bindings_defaults_to_base(source_bindings_config)
        )
        source_type = cls.source_type_for(root, filemanager, source_bindings)
        if (
            source_bindings is not None
            and not source_bindings.is_empty
            and source_type.source_selection_role().bindings_may_select_source(
                projects_bindings=source_type.projects_declared_source_bindings()
            )
        ):
            source_type = DeclaredFileSource.require_registered_source()
        source = source_type.create(
            filemanager=filemanager,
            pattern_format=pattern_format,
            source_bindings_config=source_bindings_config,
        )
        source.plate_folder = root
        return source


class AutoDetectedSource(DatasetSourceChoice):
    """Select the first registered source whose detection claims the root."""

    source_name = "auto"

    @classmethod
    def source_type_for(
        cls,
        root: Path,
        filemanager: "FileManager",
        source_bindings: "SourceBindingsConfig | None",
    ) -> "type[DatasetSource]":
        from openhcs.core.dataset_sources.source import DatasetSource, DeclaredFileSource

        detected = DatasetSource.detect_source_type(root, filemanager, source_bindings)
        if detected is not None:
            return detected
        if source_bindings is None or source_bindings.is_empty:
            raise ValueError(f"Could not detect a dataset source in {root}.")
        return DeclaredFileSource.require_registered_source()


class DatasetSourceChoices(AnnotationChoices):
    """A field holding a dataset source choice."""

    def choices(self) -> tuple[object, ...]:
        return DatasetSourceChoice.choices()

    def label(self, choice: object) -> str:
        return choice.source_name  # type: ignore[attr-defined]

    def __eq__(self, other: object) -> bool:
        return type(self) is type(other)

    def __hash__(self) -> int:
        return hash(type(self))

    def __repr__(self) -> str:
        return f"{type(self).__name__}()"


__all__ = ["AutoDetectedSource", "DatasetSourceChoice", "DatasetSourceChoices"]
