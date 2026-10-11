"""Kinds of files a plate's result directories hold.

Each kind is a class: it declares the suffixes that identify it, picks the
preview a reader builds for it, and picks what a browser does when the file is
opened. The registry key (``name``) is the spelling used in metadata tables and
agent DTOs.
"""

from __future__ import annotations

from abc import ABC
from pathlib import Path
from typing import ClassVar, Protocol

from metaclass_registry import AutoRegisterMeta

class ResultFilePreviewReader(Protocol):
    """The previews a reader can build; each kind picks one."""

    def text_preview(self, record, *, max_lines: int, max_bytes: int): ...

    def csv_preview(self, record, *, max_lines: int, max_bytes: int): ...

    def roi_preview(self, record, *, max_examples: int, max_bytes: int): ...


class ResultFileOpener(Protocol):
    """What a file browser can do with a result file."""

    def open_in_default_app(self, file_path: Path) -> None:
        """Hand the file to the desktop's default application."""

    def stream_rois(self, file_path: Path) -> None:
        """Send the file's ROIs to the enabled viewers."""


class ResultFileFormat(ABC, metaclass=AutoRegisterMeta):
    """One kind of result file."""

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    name: ClassVar[str | None] = None
    suffixes: ClassVar[tuple[str, ...]] = ()
    streams_rois: ClassVar[bool] = False

    @classmethod
    def names_path(cls, file_path: Path) -> bool:
        """Whether this kind's suffixes identify the path."""
        return file_path.suffix.lower() in cls.suffixes

    @classmethod
    def for_suffix_of(cls, file_path: Path) -> type[ResultFileFormat] | None:
        """Return the kind whose suffixes identify the path, if any."""
        for member in cls.__registry__.values():
            if member.names_path(file_path):
                return member
        return None

    @classmethod
    def preview(
        cls,
        reader: ResultFilePreviewReader,
        record,
        *,
        max_lines: int,
        max_bytes: int,
    ):
        """Build this kind's bounded preview; kinds without one return None."""
        return None

    @classmethod
    def open_with(cls, opener: ResultFileOpener, file_path: Path) -> None:
        """Open the file the way this kind is opened."""
        opener.open_in_default_app(file_path)


class TiffResultFile(ResultFileFormat):
    """An image file; identified by its image format, not by suffix here."""

    name = "TIFF"


class NumpyResultFile(ResultFileFormat):
    """A NumPy array file; identified by its image format, not by suffix here."""

    name = "NUMPY"


class TextResultFile(ResultFileFormat):
    """A file previewed as text lines."""

    name = "TEXT"
    suffixes = (".txt", ".py", ".md", ".swc")

    @classmethod
    def preview(cls, reader, record, *, max_lines, max_bytes):
        return reader.text_preview(record, max_lines=max_lines, max_bytes=max_bytes)


class JsonResultFile(TextResultFile):
    name = "JSON"
    suffixes = (".json",)


class CsvResultFile(TextResultFile):
    """A table: previewed as text lines plus parsed columns and rows."""

    name = "CSV"
    suffixes = (".csv",)

    @classmethod
    def preview(cls, reader, record, *, max_lines, max_bytes):
        return reader.csv_preview(record, max_lines=max_lines, max_bytes=max_bytes)


class RoiArchiveResultFile(ResultFileFormat):
    """A ``.roi.zip`` archive of ROIs."""

    name = "ROI"
    suffixes = (".roi.zip",)
    streams_rois = True

    @classmethod
    def names_path(cls, file_path: Path) -> bool:
        return file_path.name.endswith(cls.suffixes)

    @classmethod
    def preview(cls, reader, record, *, max_lines, max_bytes):
        return reader.roi_preview(record, max_examples=max_lines, max_bytes=max_bytes)

    @classmethod
    def open_with(cls, opener: ResultFileOpener, file_path: Path) -> None:
        opener.stream_rois(file_path)
