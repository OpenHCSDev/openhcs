"""Nominal contract for OpenHCS virtual file-system operations."""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType
from typing import Annotated, Any, ClassVar, get_args, get_origin

from polystore.file_content import FileContent, UnhashedFileContent


class FileManagerLike(ABC):
    """Minimal FileManager surface required by backend-explicit callers."""

    @property
    def registry(self) -> Mapping[str, object]:
        """Return backend registry metadata when the filemanager exposes it."""
        return MappingProxyType({})

    @abstractmethod
    def list_files(
        self,
        directory: str | Path,
        backend: str,
        **kwargs: object,
    ) -> list[str]:
        """List files from the selected backend."""

    @abstractmethod
    def exists(self, path: str | Path, backend: str) -> bool:
        """Return whether a path exists in the selected backend."""

    @abstractmethod
    def is_dir(self, path: str | Path, backend: str) -> bool:
        """Return whether a path is a directory in the selected backend."""

    @abstractmethod
    def file_content(self, file_path: str | Path, backend: str) -> FileContent:
        """Say what bytes a file holds, or why the backend cannot hash it."""

    @abstractmethod
    def load(self, file_path: str | Path, backend: str, **kwargs: object) -> object:
        """Load an object from the selected backend."""

    @abstractmethod
    def load_batch(
        self,
        file_paths: Sequence[str | Path],
        backend: str,
        **kwargs: object,
    ) -> Sequence[object]:
        """Load several objects from the selected backend."""

    @abstractmethod
    def resolve_address(
        self,
        backend_address: str | Path,
        backend: str,
        *,
        base_path: str | Path,
    ) -> str | Path:
        """Resolve one backend-owned source address."""

    def source_path(
        self,
        backend_address: str | Path,
        backend: str,
        *,
        base_path: str | Path,
    ) -> str | Path:
        """Return the physical source path represented by a backend address."""

        return self.resolve_address(
            backend_address,
            backend,
            base_path=base_path,
        )

    @abstractmethod
    def physical_source_path(
        self,
        backend_address: str | Path,
        backend: str,
        *,
        base_path: str | Path,
    ) -> str | Path | None:
        """Return a physical source path when the backend declares one."""

        raise NotImplementedError

    @abstractmethod
    def save(
        self,
        data: object,
        output_path: str | Path,
        backend: str,
        **kwargs: object,
    ) -> None:
        """Save an object through the selected backend."""

    @abstractmethod
    def ensure_directory(self, directory: str | Path, backend: str) -> str:
        """Ensure a directory exists in the selected backend."""


class DatasetPathDeclaration(ABC):
    """Nominal declaration for a path resolved against one compilation plate."""

    plain_name: ClassVar[str]
    """What this kind of path is, for a reader of a run's record."""

    @abstractmethod
    def validate_target(
        self,
        target: Path,
        *,
        filemanager: FileManagerLike,
        backend: str,
    ) -> None:
        """Validate the resolved target without creating it."""

    @abstractmethod
    def content_at_run_start(
        self,
        target: Path,
        *,
        filemanager: FileManagerLike,
        backend: str,
    ) -> FileContent:
        """Identify the bytes a run will read here, or say why there are none to hash."""

    @classmethod
    def from_annotation(cls, annotation: Any) -> "DatasetPathDeclaration | None":
        """Return the sole declaration carried by one structured annotation."""

        declarations = cls._from_annotation(annotation)
        unique = tuple(dict.fromkeys(declarations))
        if len(unique) > 1:
            raise TypeError(
                "Path annotation declares conflicting plate path policies: "
                f"{unique!r}."
            )
        return unique[0] if unique else None

    @classmethod
    def _from_annotation(cls, annotation: Any) -> tuple["DatasetPathDeclaration", ...]:
        args = get_args(annotation)
        if get_origin(annotation) is Annotated:
            base, *metadata = args
            return (
                *(item for item in metadata if isinstance(item, cls)),
                *cls._from_annotation(base),
            )
        return tuple(
            declaration
            for member in args
            for declaration in cls._from_annotation(member)
        )


@dataclass(frozen=True, slots=True)
class PlateInputFileDeclaration(DatasetPathDeclaration):
    """Existing plate-relative input file."""

    plain_name: ClassVar[str] = "input file"

    def content_at_run_start(
        self,
        target: Path,
        *,
        filemanager: FileManagerLike,
        backend: str,
    ) -> FileContent:
        return filemanager.file_content(target, backend)

    def validate_target(
        self,
        target: Path,
        *,
        filemanager: FileManagerLike,
        backend: str,
    ) -> None:
        if not filemanager.exists(target, backend):
            raise FileNotFoundError(f"Declared input file does not exist: {target}")
        if filemanager.is_dir(target, backend):
            raise IsADirectoryError(f"Declared input file is a directory: {target}")


@dataclass(frozen=True, slots=True)
class PlateInputDirectoryDeclaration(DatasetPathDeclaration):
    """Existing plate-relative input directory."""

    plain_name: ClassVar[str] = "input directory"

    def content_at_run_start(
        self,
        target: Path,
        *,
        filemanager: FileManagerLike,
        backend: str,
    ) -> FileContent:
        del target, filemanager, backend
        return UnhashedFileContent(
            "A declared input directory is recorded by path; its files are not hashed."
        )

    def validate_target(
        self,
        target: Path,
        *,
        filemanager: FileManagerLike,
        backend: str,
    ) -> None:
        if not filemanager.exists(target, backend):
            raise FileNotFoundError(
                f"Declared input directory does not exist: {target}"
            )
        if not filemanager.is_dir(target, backend):
            raise NotADirectoryError(
                f"Declared input directory is not a directory: {target}"
            )


@dataclass(frozen=True, slots=True)
class PlateOutputFileDeclaration(DatasetPathDeclaration):
    """Plate-relative output file whose writer owns creation."""

    plain_name: ClassVar[str] = "output file"

    def content_at_run_start(
        self,
        target: Path,
        *,
        filemanager: FileManagerLike,
        backend: str,
    ) -> FileContent:
        del target, filemanager, backend
        return UnhashedFileContent(
            "This run writes the file; it has no content when the run starts."
        )

    def validate_target(
        self,
        target: Path,
        *,
        filemanager: FileManagerLike,
        backend: str,
    ) -> None:
        del target, filemanager, backend


@dataclass(frozen=True, slots=True)
class PlateOutputDirectoryDeclaration(DatasetPathDeclaration):
    """Plate-relative output directory whose writer owns creation."""

    plain_name: ClassVar[str] = "output directory"

    def content_at_run_start(
        self,
        target: Path,
        *,
        filemanager: FileManagerLike,
        backend: str,
    ) -> FileContent:
        del target, filemanager, backend
        return UnhashedFileContent(
            "This run writes the directory; it has no content when the run starts."
        )

    def validate_target(
        self,
        target: Path,
        *,
        filemanager: FileManagerLike,
        backend: str,
    ) -> None:
        del target, filemanager, backend


PlateInputFile = Annotated[Path, PlateInputFileDeclaration()]
PlateInputDirectory = Annotated[Path, PlateInputDirectoryDeclaration()]
PlateOutputFile = Annotated[Path, PlateOutputFileDeclaration()]
PlateOutputDirectory = Annotated[Path, PlateOutputDirectoryDeclaration()]
