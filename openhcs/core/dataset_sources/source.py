"""The dataset-source family: how the kernel opens one dataset root.

A :class:`DatasetSource` binds a filename parser and a metadata handler to a
dataset root. Each concrete source registers under its ``source_name``; that
key is the source's identity at every boundary. Domains add sources from the
modules their axis family lists in ``extension_modules``.
"""

from __future__ import annotations

import logging
from abc import ABC, abstractmethod
from collections.abc import Iterable, Mapping
from pathlib import Path
from typing import TYPE_CHECKING, ClassVar, List, Optional, Tuple, Type, Union

from metaclass_registry import AutoRegisterMeta
from objectstate.lazy_factory import replace_raw
from polystore.filemanager import FileManager
from polystore.streaming.viewer_transport import ViewerMicroscopeHandlerABC
from polystore.virtual_workspace import SourcePixelRef

from openhcs.constants.constants import Backend
from openhcs.core.axes import Axis
from openhcs.core.dataset_sources.choice import DatasetSourceChoice
from openhcs.core.dataset_sources.discovery import domain_registry_config
from openhcs.core.dataset_sources.interfaces import (
    FilenameParser,
    MetadataHandler,
    FilenameParserCapability,
)

logger = logging.getLogger(__name__)

if TYPE_CHECKING:
    from openhcs.core.config import MaterializationBackend, PipelineConfig
    from openhcs.core.runtime_pattern_cache import RuntimePatternDiscoveryCache
    from openhcs.core.source_bindings import SourceBindingsConfig


# ---------------------------------------------------------------------------
# Selection roles (capability mixins on source classes)
# ---------------------------------------------------------------------------


class SourceSelectionRole(ABC):
    """How a source class takes part in source selection.

    Each source class carries exactly one role mixin; the role is the first
    role class in its MRO.
    """

    role_name: ClassVar[str]
    requires_local_directory: ClassVar[bool] = True
    allows_declared_source_override: ClassVar[bool] = True
    detection_rank: ClassVar[int] = 0
    """Detection order: metadata detectors (0), own detectors (1), broad stores (2)."""

    @classmethod
    def bindings_may_select_source(cls, *, projects_bindings: bool) -> bool:
        """Prepared workspaces cannot be replaced by new raw-source declarations."""
        return cls.allows_declared_source_override and not projects_bindings

    @classmethod
    def require_registered_source(cls) -> type["DatasetSource"]:
        """The one registered source carrying this role."""
        matches = tuple(
            source_type
            for source_type in DatasetSource.__registry__.values()
            if source_type.source_selection_role() is cls
        )
        if len(matches) != 1:
            raise ValueError(
                f"Source role {cls.role_name!r} requires exactly one registered "
                f"dataset source; found {[match.source_name for match in matches]!r}."
            )
        return matches[0]

    @classmethod
    def pipeline_config_for_source(cls, base: "PipelineConfig") -> "PipelineConfig":
        """Select this role's source without resolving other lazy fields."""
        return replace_raw(base, dataset_source=cls.require_registered_source())

    @classmethod
    def require_available_source(cls, source_path: Path) -> None:
        """Enforce the path availability owned by this role."""

        if not cls.requires_local_directory:
            return
        if not source_path.exists():
            raise FileNotFoundError(f"Plate path does not exist: {source_path}")
        if not source_path.is_dir():
            raise NotADirectoryError(f"Plate path is not a directory: {source_path}")


class FormatSpecificSource(SourceSelectionRole):
    """Owns one vendor or format layout."""

    role_name = "format_specific"


class BroadStoreSource(SourceSelectionRole):
    """Generic structured-store decoder that runs after format-specific sources."""

    role_name = "broad_structured_store"
    detection_rank = 2

    @classmethod
    def source_selection_guidance(cls) -> str:
        return (
            "Use for a supported structured or rich container when no registered "
            "format-specific parser recognizes the source layout. A missing native "
            "metadata file alone does not make the broad decoder semantically "
            "preferable when a format-specific parser recognizes the filenames."
        )


class DeclaredFileSource(SourceSelectionRole):
    """Ordinary image files described by source-binding declarations."""

    role_name = "declared_file_fallback"


class RemoteServiceSource(SourceSelectionRole):
    """Datasets addressed through a remote service, not a local directory."""

    role_name = "remote_service"
    requires_local_directory = False


class PreparedWorkspaceSource(SourceSelectionRole):
    """Workspaces OpenHCS already prepared and described in its own format."""

    role_name = "prepared_workspace"
    allows_declared_source_override = False


# ---------------------------------------------------------------------------
# The source family
# ---------------------------------------------------------------------------


class DatasetSource(
    DatasetSourceChoice,
    FilenameParserCapability,
    ViewerMicroscopeHandlerABC,
    FormatSpecificSource,
    ABC,
    metaclass=AutoRegisterMeta,
):
    """One registered way to open a dataset root.

    The protocol the kernel uses: :meth:`axis_values`,
    :meth:`available_backends`, :meth:`resolve_metadata_artifact`, plus the
    optional filename parser supplied through :class:`FilenameParserCapability`.
    """

    __registry_config__ = domain_registry_config(
        key_attribute="source_name",
        skip_if_no_key=False,
        registry_name="dataset source",
    )

    source_name: ClassVar[str]
    metadata_handler_class: ClassVar[Type[MetadataHandler]]

    def __init__(
        self, parser: Optional[FilenameParser], metadata_handler: MetadataHandler
    ):
        self.parser = parser
        self.metadata_handler = metadata_handler
        self.plate_folder: Optional[Path] = None

    # -- selection ------------------------------------------------------------

    @classmethod
    def source_type_for(
        cls,
        root: Path,
        filemanager: FileManager,
        source_bindings: "SourceBindingsConfig | None",
    ) -> type["DatasetSource"]:
        del root, filemanager, source_bindings
        return cls

    @classmethod
    def source_selection_role(cls) -> type[SourceSelectionRole]:
        """This class's role: the first role mixin in its MRO."""
        return next(
            base
            for base in cls.__mro__
            if isinstance(base, type)
            and SourceSelectionRole in base.__bases__
        )

    @classmethod
    def detect(
        cls,
        plate_folder: Path,
        filemanager: FileManager,
        source_bindings_config: Optional["SourceBindingsConfig"] = None,
    ) -> bool:
        """Detect this source through its metadata handler's metadata file.

        Store-backed sources override this to narrow discovery by declarations.
        """
        from polystore.exceptions import MetadataNotFoundError

        del source_bindings_config
        try:
            cls.metadata_handler_class(filemanager).find_metadata_file(plate_folder)
        except (MetadataNotFoundError, FileNotFoundError, TypeError):
            return False
        return True

    @classmethod
    def detection_order(cls) -> tuple[type["DatasetSource"], ...]:
        """Prepared workspaces first, then metadata detectors, own detectors, stores."""

        prepared = PreparedWorkspaceSource.require_registered_source()
        ranked = sorted(
            (
                (
                    max(
                        source_type.source_selection_role().detection_rank,
                        1 if "detect" in source_type.__dict__ else 0,
                    ),
                    index,
                    source_type,
                )
                for index, source_type in enumerate(cls.__registry__.values())
                if source_type is not prepared
            ),
            key=lambda item: (item[0], item[1]),
        )
        return (prepared, *(source_type for _rank, _index, source_type in ranked))

    @classmethod
    def detect_source_type(
        cls,
        root: Path,
        filemanager: FileManager,
        source_bindings: "SourceBindingsConfig | None",
    ) -> type["DatasetSource"] | None:
        """The first source in detection order that claims ``root``."""

        for source_type in cls.detection_order():
            if source_type.detect(root, filemanager, source_bindings):
                logger.info("Detected dataset source %s", source_type.source_name)
                return source_type
        logger.debug("No registered dataset source claimed %s", root)
        return None

    @classmethod
    def create(
        cls,
        *,
        filemanager: FileManager,
        pattern_format: Optional[str] = None,
        source_bindings_config: Optional["SourceBindingsConfig"] = None,
    ) -> "DatasetSource":
        """Construct this source from factory inputs."""
        del source_bindings_config
        return cls(filemanager, pattern_format=pattern_format)

    @classmethod
    def projects_declared_source_bindings(cls) -> bool:
        """Return whether this source projects named bindings onto its files."""

        return False

    def source_bindings_still_required(self) -> Optional["SourceBindingsConfig"]:
        """Declarations still required to select from a retained source set."""
        return None

    @classmethod
    def supports_explicit_incomplete_export(cls) -> bool:
        """Return whether parser-recognized subsets are valid explicit inputs."""

        return True

    @classmethod
    def source_selection_guidance(cls) -> str:
        """Explain format-specific detection and explicit partial selection."""

        if not cls.supports_explicit_incomplete_export():
            return (
                "Use only when this handler's complete detection contract succeeds. "
                "Parser recognition without the required vendor metadata is filename "
                "evidence, not a valid native dataset. Obtain the complete export, or "
                "treat independently decodable ordinary files through the declared-file "
                "fallback with explicit source semantics."
            )
        return (
            "Use when this handler's parser and layout describe the dataset. Prefer a "
            "complete source layout/export so the handler detection contract and "
            "metadata owner can supply the available plate facts. If the parser "
            "recognizes an intentionally incomplete export, select this handler "
            "explicitly and expect metadata-derived fields to remain unavailable."
        )

    # -- layout -----------------------------------------------------------------

    @property
    @abstractmethod
    def root_dir(self) -> str:
        """Subdirectory where workspace preparation starts and metadata is keyed."""

    @property
    @abstractmethod
    def compatible_backends(self) -> List[Backend]:
        """Storage backends this source can read, in priority order."""

    @abstractmethod
    def initialize_workspace(self, plate_path: Path, filemanager: FileManager) -> Path:
        """Prepare the dataset for reading and return its image directory."""

    def get_required_backend(self) -> Optional["MaterializationBackend"]:
        """The materialization backend this source requires, when it has one."""
        from openhcs.core.config import MaterializationBackend

        if len(self.compatible_backends) == 1:
            backend_value = self.compatible_backends[0].value
            materialization_values = {
                materialization_backend.value
                for materialization_backend in MaterializationBackend
            }
            if backend_value not in materialization_values:
                raise RuntimeError(
                    f"{self.source_name} declares single backend "
                    f"{backend_value!r}, but it is not a materialization backend."
                )
            return MaterializationBackend(backend_value)
        return None

    def available_backends(self, plate_path: Union[str, Path]) -> List[Backend]:
        """Backends available for this dataset (default: every compatible one)."""
        del plate_path
        return self.compatible_backends

    def get_primary_backend(
        self, plate_path: Union[str, Path], filemanager: "FileManager"
    ) -> str:
        """The backend reads go through: a registered virtual workspace first."""
        if Backend.VIRTUAL_WORKSPACE.value in filemanager.registry:
            return Backend.VIRTUAL_WORKSPACE.value
        available_backends = self.available_backends(plate_path)
        if not available_backends:
            raise RuntimeError(
                f"No available backends for {self.source_name} at {plate_path}"
            )
        return available_backends[0].value

    @staticmethod
    def _register_virtual_workspace_backend(
        plate_path: Union[str, Path], filemanager: FileManager
    ) -> None:
        """Register (or reuse) the virtual workspace backend for this dataset."""
        from polystore.virtual_workspace import VirtualWorkspaceBackend

        from openhcs.core.virtual_workspace_metadata import METADATA_CONFIG

        plate_root = Path(plate_path).resolve()
        registered = filemanager.registry.get(Backend.VIRTUAL_WORKSPACE.value)
        if (
            isinstance(registered, VirtualWorkspaceBackend)
            and registered.plate_root.resolve() == plate_root
            and registered.metadata_config == METADATA_CONFIG
        ):
            return

        backend = VirtualWorkspaceBackend(
            plate_root=plate_root, metadata_config=METADATA_CONFIG
        )
        filemanager.register_backend(Backend.VIRTUAL_WORKSPACE.value, backend)
        logger.info(f"Registered virtual workspace backend for {plate_path}")

    @classmethod
    def register_workspace_backends(
        cls,
        plate_path: Union[str, Path],
        filemanager: FileManager,
    ) -> None:
        """Register the backends this source declares for workspace replay."""

        cls.register_source_backends(filemanager)
        cls._register_virtual_workspace_backend(plate_path, filemanager)

    @staticmethod
    def register_source_backends(filemanager: FileManager) -> None:
        """Register direct source backends needed before workspace materialization."""

    def save_virtual_workspace_metadata(
        self,
        plate_path: Path,
        workspace_mapping: Mapping[str, SourcePixelRef],
    ) -> None:
        """Write a virtual workspace mapping and this source's facts to metadata."""
        from openhcs.core.virtual_workspace_metadata import (
            FIELDS,
            AtomicMetadataWriter,
            get_metadata_path,
        )

        metadata_path = get_metadata_path(plate_path)
        metadata_dict = {
            FIELDS.WORKSPACE_MAPPING: {
                virtual_path: source_ref.to_workspace_mapping()
                for virtual_path, source_ref in workspace_mapping.items()
            },
            FIELDS.SOURCE_METADATA: self.metadata_handler.source_metadata_by_path(
                plate_path, self.parser, workspace_mapping
            ),
            FIELDS.AVAILABLE_BACKENDS: {
                Backend.DISK.value: True,
                Backend.VIRTUAL_WORKSPACE.value: True,
            },
            FIELDS.MICROSCOPE_HANDLER_NAME: self.source_name,
            FIELDS.SOURCE_FILENAME_PARSER_NAME: self.parser.__class__.__name__,
            FIELDS.GRID_DIMENSIONS: self.metadata_handler.get_grid_dimensions(
                plate_path
            ),
            FIELDS.PIXEL_SIZE: self.metadata_handler.get_metadata_pixel_size(
                plate_path
            ),
        }
        AtomicMetadataWriter().merge_subdirectory_metadata(
            metadata_path, {self.root_dir: metadata_dict}
        )
        logger.info(f"Saved virtual workspace metadata to {metadata_path}")

    # -- axis values and patterns --------------------------------------------------

    def axis_values(
        self,
        input_dir: Union[str, Path],
        filemanager: FileManager,
        axes: Iterable[type[Axis]],
    ) -> dict[type[Axis], list[str]]:
        """Values of ``axes`` found by parsing the dataset's image filenames once."""
        from openhcs.constants.constants import LOADABLE_IMAGE_EXTENSIONS

        values: dict[type[Axis], set[object]] = {axis: set() for axis in axes}
        backend = self.get_primary_backend(input_dir, filemanager)
        for filename in filemanager.list_files(
            str(input_dir), backend, extensions=LOADABLE_IMAGE_EXTENSIONS
        ):
            parsed = self.parser.parse_filename(str(filename))
            if parsed is None:
                logger.warning(
                    "Could not parse filename: %s (backend=%s input_dir=%s)",
                    filename,
                    backend,
                    input_dir,
                )
                continue
            for axis, axis_values in values.items():
                value = parsed.value_for(axis)
                if value is not None:
                    axis_values.add(value)
        return {
            axis: [str(value) for value in sorted(axis_values)]
            for axis, axis_values in values.items()
        }

    def auto_detect_patterns(
        self,
        folder_path: Union[str, Path],
        filemanager: FileManager,
        backend: str,
        extensions=None,
        group_by=None,
        variable_components=None,
        pattern_cache: "RuntimePatternDiscoveryCache | None" = None,
        **kwargs,
    ):
        """Group the folder's files into patterns through the pattern engine."""
        folder_path = Path(folder_path)
        if not filemanager.exists(str(folder_path), backend):
            raise ValueError(f"Folder path does not exist: {folder_path}")

        from openhcs.formats.pattern.pattern_discovery import PatternDiscoveryEngine

        pattern_engine = PatternDiscoveryEngine(self.parser, filemanager, pattern_cache)
        return dict(
            pattern_engine.auto_detect_patterns(
                folder_path,
                extensions=extensions,
                group_by=group_by,
                variable_components=variable_components,
                backend=backend,
                **kwargs,
            )
        )

    def path_list_from_pattern(
        self,
        directory: Union[str, Path],
        pattern,
        filemanager: FileManager,
        backend: str,
        variable_components=None,
        *,
        pattern_cache: "RuntimePatternDiscoveryCache | None" = None,
    ):
        """List the files one pattern matches through the pattern engine."""
        directory_path = Path(directory)
        if not filemanager.exists(str(directory_path), backend):
            raise ValueError(f"Directory does not exist: {directory}")

        from openhcs.formats.pattern.pattern_discovery import PatternDiscoveryEngine

        pattern_engine = PatternDiscoveryEngine(self.parser, filemanager, pattern_cache)
        return pattern_engine.path_list_from_pattern(
            directory_path,
            pattern,
            backend=backend,
            variable_components=variable_components,
        )

    # -- metadata -------------------------------------------------------------------

    def find_metadata_file(self, plate_path: Union[str, Path]) -> Path:
        return self.metadata_handler.find_metadata_file(plate_path)

    def get_grid_dimensions(self, plate_path: Union[str, Path]) -> Tuple[int, int]:
        return self.metadata_handler.get_grid_dimensions(plate_path)

    def can_resolve_metadata_artifact(self, artifact_name: str) -> bool:
        return self.metadata_handler.can_resolve_metadata_artifact(artifact_name)

    def resolve_metadata_artifact(
        self,
        artifact_name: str,
        plate_path: Union[str, Path],
    ) -> object:
        return self.metadata_handler.resolve_metadata_artifact(
            artifact_name,
            plate_path,
        )

    def get_pixel_size(self, plate_path: Union[str, Path]) -> float:
        return self.metadata_handler.get_pixel_size(plate_path)


__all__ = [
    "BroadStoreSource",
    "DatasetSource",
    "DeclaredFileSource",
    "FormatSpecificSource",
    "PreparedWorkspaceSource",
    "RemoteServiceSource",
    "SourceSelectionRole",
]
