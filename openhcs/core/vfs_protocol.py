"""Nominal contract for OpenHCS virtual file-system operations."""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType
from typing import Annotated, Any, ClassVar, get_args, get_origin


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


@dataclass(frozen=True, slots=True, kw_only=True)
class OutputFileOf:
    """The file an earlier step writes through one of its output-file parameters.

    A pipeline author writes it as the argument of an input-file parameter in
    place of a path: ``OutputFileOf(step="fit", parameter="model_file")``.
    """

    step: str
    parameter: str


class DeclaredFileLinkError(ValueError):
    """An ``OutputFileOf`` argument names no file an earlier step writes."""


class SeveralWritersOfDeclaredFileError(ValueError):
    """More than one call would write the same declared output file."""


class DeclaredFileWrites:
    """The declared output files the calls of one execution have claimed."""

    def __init__(self) -> None:
        self._writer_by_path: dict[Path, str] = {}

    def claim(self, path: Path, writer: str) -> None:
        """Record ``writer`` as the one call that writes ``path``."""

        if path in self._writer_by_path:
            raise SeveralWritersOfDeclaredFileError(
                f"Declared output file {path} would be written twice in one "
                f"execution: first by {self._writer_by_path[path]}, again by "
                f"{writer}. A declared output file has one writer; run the step "
                "once for the plate, or give each call its own file."
            )
        self._writer_by_path[path] = writer


@dataclass(frozen=True, slots=True)
class DeclaredFile:
    """One declared path parameter of a compiled invocation, resolved."""

    parameter: str
    path: Path
    backend: str
    declaration: "DatasetPathDeclaration"

    def require_produced_before(self, step_index: int, *, owner: str) -> None:
        """Check that whatever writes this path runs before ``step_index``."""

        del step_index, owner

    def before_call(
        self,
        *,
        filemanager: FileManagerLike,
        writes: DeclaredFileWrites,
        call: str,
    ) -> None:
        """Check, just before the callable runs, what compilation could not."""

        if self.declaration.writes_file:
            writes.claim(self.path, f"{call} parameter {self.parameter!r}")
            filemanager.ensure_directory(self.path.parent, self.backend)


@dataclass(frozen=True, slots=True)
class LinkedInputFile(DeclaredFile):
    """A declared input file that an earlier step of the same pipeline writes."""

    producer_step_index: int
    producer_step_name: str
    producer_parameter: str

    def require_produced_before(self, step_index: int, *, owner: str) -> None:
        if self.producer_step_index >= step_index:
            raise DeclaredFileLinkError(
                f"{owner} reads the file step {self.producer_step_name!r} (index "
                f"{self.producer_step_index}) writes through "
                f"{self.producer_parameter!r}, but that step does not run earlier "
                f"than step index {step_index}."
            )

    def before_call(
        self,
        *,
        filemanager: FileManagerLike,
        writes: DeclaredFileWrites,
        call: str,
    ) -> None:
        del writes
        if not filemanager.exists(self.path, self.backend):
            raise FileNotFoundError(
                f"{call} parameter {self.parameter!r} reads {self.path}, which "
                f"step {self.producer_step_name!r} (index "
                f"{self.producer_step_index}) declares it writes through "
                f"{self.producer_parameter!r}, but the file does not exist."
            )


class ProducedFileLookup(ABC):
    """The compiler's table of files that steps of one pipeline write."""

    @abstractmethod
    def linked_input_file(
        self,
        parameter: str,
        link: OutputFileOf,
        declaration: "DatasetPathDeclaration",
        *,
        owner: str,
    ) -> LinkedInputFile:
        """Return the consumer's record for the file ``link`` names."""


class PathRoots(ABC):
    """The roots relative declared paths of one compilation resolve against."""

    @abstractmethod
    def input_dataset_root(self) -> Path:
        """Return the plate being processed."""

    @abstractmethod
    def output_dataset_root(self) -> Path:
        """Return the dataset this compilation writes."""


class DatasetPathDeclaration(ABC):
    """Nominal declaration for a path resolved against one compilation plate."""

    writes_file: ClassVar[bool] = False
    """Whether the callable creates one file at the path (so it has one writer)."""

    @abstractmethod
    def root(self, roots: PathRoots) -> Path:
        """Return the root a relative path of this declaration resolves against."""

    @abstractmethod
    def validate_target(
        self,
        target: Path,
        *,
        filemanager: FileManagerLike,
        backend: str,
    ) -> None:
        """Validate the resolved target without creating it."""

    def linked_file(
        self,
        parameter: str,
        link: OutputFileOf,
        produced_files: ProducedFileLookup,
        *,
        owner: str,
    ) -> LinkedInputFile:
        """Return the record for an argument that names an earlier step's file."""

        del parameter, produced_files
        raise TypeError(
            f"{owner} is declared {type(self).__name__} and received {link!r}; "
            "only an input file parameter can read a file another step writes."
        )

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


class InputDatasetPathDeclaration(DatasetPathDeclaration):
    """A path that, when relative, lies in the plate being processed."""

    def root(self, roots: PathRoots) -> Path:
        return roots.input_dataset_root()


class OutputDatasetPathDeclaration(DatasetPathDeclaration):
    """A path that, when relative, lies in the dataset this compilation writes."""

    def root(self, roots: PathRoots) -> Path:
        return roots.output_dataset_root()

    def validate_target(
        self,
        target: Path,
        *,
        filemanager: FileManagerLike,
        backend: str,
    ) -> None:
        del target, filemanager, backend


@dataclass(frozen=True, slots=True)
class PlateInputFileDeclaration(InputDatasetPathDeclaration):
    """Existing input file, or the file an earlier step writes."""

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

    def linked_file(
        self,
        parameter: str,
        link: OutputFileOf,
        produced_files: ProducedFileLookup,
        *,
        owner: str,
    ) -> LinkedInputFile:
        return produced_files.linked_input_file(parameter, link, self, owner=owner)


@dataclass(frozen=True, slots=True)
class PlateInputDirectoryDeclaration(InputDatasetPathDeclaration):
    """Existing plate-relative input directory."""

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
class PlateOutputFileDeclaration(OutputDatasetPathDeclaration):
    """File in the output dataset that exactly one call of the callable writes."""

    writes_file: ClassVar[bool] = True


@dataclass(frozen=True, slots=True)
class PlateOutputDirectoryDeclaration(OutputDatasetPathDeclaration):
    """Directory in the output dataset; its writers create it and share it."""


@dataclass(frozen=True, slots=True)
class OutputParentDirectoryDeclaration(InputDatasetPathDeclaration):
    """Directory under which output datasets are created.

    It defines the output dataset root, so a relative value resolves against the
    input plate.
    """

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
OutputParentDirectory = Annotated[Path, OutputParentDirectoryDeclaration()]
