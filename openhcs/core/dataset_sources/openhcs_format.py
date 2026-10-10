"""
OpenHCS microscope handler implementation for openhcs.

This module provides the OpenHCSDatasetSource, which reads plates
that have been pre-processed and standardized into the OpenHCS format.
The metadata for such plates is defined in an 'openhcs_metadata.json' file.
"""

import json
import logging
from abc import ABC
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import (
    TYPE_CHECKING,
    Any,
    Dict,
    List,
    Mapping,
    Optional,
    Tuple,
    Union,
    cast,
)

from openhcs.constants.constants import Backend
from openhcs.core.source_metadata import (
    SourceVoxelSpacing,
)
from openhcs.core.source_workspace_projection import (
    VirtualWorkspaceSourceProjection,
    VirtualWorkspaceSourceProjectionBuilder,
)
from metaclass_registry import AutoRegisterMeta
from polystore.exceptions import MetadataNotFoundError
from polystore.filemanager import FileManager
from polystore.streaming.viewer_transport import ViewerMicroscopeHandlerABC
from openhcs.core.virtual_workspace_metadata import (
    AtomicMetadataWriter,
    FIELDS,
    METADATA_CONFIG,
    MetadataWriteError,
    OpenHCSMetadataSubdirectories,
    VirtualWorkspaceMapping,
    VirtualWorkspaceSourceProjectionEntries,
    get_metadata_path,
)
from openhcs.core.dataset_sources.interfaces import (
    AnalysisResultDirectory,
    MetadataComponentValueSet,
    MetadataHandler,
    MetadataViewDocument,
    MetadataViewEntry,
)
from openhcs.core.axes import Axis, AxisFamily

if TYPE_CHECKING:
    from openhcs.core.context.processing_context import ProcessingContext

logger = logging.getLogger(__name__)


def get_subdirectory_name(
    input_dir: Union[str, Path], plate_path: Union[str, Path]
) -> str:
    """Return the OpenHCS metadata subdirectory key for an input directory."""
    input_path = Path(input_dir)
    root_path = Path(plate_path)
    return "." if input_path == root_path else input_path.name


def resolve_subdirectory_path(subdir_name: str, plate_path: Union[str, Path]) -> Path:
    """Resolve an OpenHCS metadata subdirectory key against a plate root."""
    root_path = Path(plate_path)
    return root_path if subdir_name == "." else root_path / subdir_name


def _get_available_filename_parsers():
    """Return registered source filename parsers keyed by nominal class name."""
    from openhcs.core.dataset_sources.interfaces import FilenameParser

    return {
        parser_type.__name__: parser_type
        for parser_type in FilenameParser.__registry__.values()
    }


class OpenHCSMetadataBase(ABC, metaclass=AutoRegisterMeta):
    """Shared OpenHCS metadata I/O authorities."""

    __registry_key__ = "__name__"
    __skip_if_no_key__ = True

    def __init__(self, filemanager: FileManager):
        self.filemanager = filemanager
        self.atomic_writer = AtomicMetadataWriter()


class OpenHCSMetadataHandler(MetadataHandler, OpenHCSMetadataBase):
    """
    Metadata handler for the OpenHCS pre-processed format.

    This handler reads metadata from an 'openhcs_metadata.json' file
    located in the root of the plate folder.
    """

    METADATA_FILENAME = METADATA_CONFIG.METADATA_FILENAME

    def __init__(self, filemanager: FileManager):
        """Bind the file owner and initialize derived metadata views."""
        MetadataHandler.__init__(self)
        OpenHCSMetadataBase.__init__(self, filemanager)
        self.invalidate_metadata_cache()

    def invalidate_metadata_cache(self) -> None:
        """Release derived metadata views before a new source observation."""
        self._metadata_dict_cache: Optional[Dict[str, Any]] = None
        self._metadata_dict_plate_path_cache: Optional[Path] = None

    def _metadata_field(
        self, plate_path: Union[str, Path], field: str, *, merge: bool = False,
    ) -> Any:
        """Resolve only the requested fact within the declared projection scope.

        An explicit child or main projection owns its own facts. With neither,
        readers can share an equal scalar or compatible mapping, but cannot
        silently choose one projection's geometry or execution input.
        """
        subdirectories = self._metadata_subdirectories(
            self.load_metadata_document(plate_path), plate_path,
        )
        try:
            selected = self._main_subdirectory_name(subdirectories, plate_path)
        except MetadataNotFoundError:
            values = {name: data.get(field) for name, data in subdirectories.items()}
            resolver = (
                self._merge_subdirectory_mapping if merge
                else self._consistent_subdirectory_value
            )
            return resolver(values, plate_path, field)
        return subdirectories[selected].get(field)

    def determine_main_subdirectory(self, plate_path: Union[str, Path]) -> str:
        """Determine main input subdirectory from metadata."""
        metadata_dict = self._load_metadata_dict(plate_path)
        subdirs = self._metadata_subdirectories(metadata_dict, plate_path)
        return self._main_subdirectory_name(subdirs, plate_path)

    def _load_metadata_dict(self, plate_path: Union[str, Path]) -> Dict[str, Any]:
        """Load and parse metadata JSON, fail-loud on errors."""
        current_path = self._resolve_plate_root(plate_path)
        if (
            self._metadata_dict_cache is not None
            and self._metadata_dict_plate_path_cache == current_path
        ):
            return self._metadata_dict_cache

        metadata_file_path = self.find_metadata_file(current_path)
        if not self.filemanager.exists(str(metadata_file_path), Backend.DISK.value):
            raise MetadataNotFoundError(
                f"Metadata file '{self.METADATA_FILENAME}' not found in {plate_path}"
            )

        try:
            content = self.filemanager.load(str(metadata_file_path), Backend.DISK.value)
            # Backend may return already-parsed dict (disk backend auto-parses JSON)
            if isinstance(content, dict):
                metadata_dict = content
            else:
                # Otherwise parse raw bytes/string
                metadata_dict = json.loads(
                    content.decode("utf-8") if isinstance(content, bytes) else content
                )
            self._metadata_dict_cache = metadata_dict
            self._metadata_dict_plate_path_cache = current_path
            return metadata_dict
        except json.JSONDecodeError as e:
            raise MetadataNotFoundError(
                f"Error decoding JSON from '{metadata_file_path}': {e}"
            ) from e

    def load_metadata_document(self, plate_path: Union[str, Path]) -> Dict[str, Any]:
        """Load the full subdirectory-keyed OpenHCS metadata document."""
        return self._load_metadata_dict(plate_path)

    def source_workspace_metadata_document(
        self,
        plate_path: Union[str, Path],
    ) -> Dict[str, Any]:
        """Return OpenHCS virtual source-workspace metadata."""

        document = self.load_metadata_document(plate_path)
        subdirectories = self._metadata_subdirectories(document, plate_path)
        if subdirectories is document[FIELDS.SUBDIRECTORIES]:
            return document
        return {**document, FIELDS.SUBDIRECTORIES: subdirectories}

    def source_workspace_root(self, plate_path: Union[str, Path]) -> Path:
        """Keep projection selection separate from plate-relative storage addresses."""
        return self._resolve_plate_root(plate_path)

    def source_diagnostics(
        self,
        plate_path: Union[str, Path],
    ) -> tuple[Mapping[str, object], ...]:
        """Return source diagnostics retained by all declared subdirectories."""

        metadata_document = self.load_metadata_document(plate_path)
        subdirectories = self._metadata_subdirectories(
            metadata_document,
            plate_path,
        )
        return tuple(
            diagnostic
            for subdirectory_name, subdirectory_data in subdirectories.items()
            for diagnostic in _source_diagnostics_from_subdirectory(
                subdirectory_name,
                subdirectory_data,
            )
        )

    def workspace_mapping_metadata(
        self,
        plate_path: Union[str, Path],
    ) -> Mapping[str, Any] | None:
        """Return the metadata-owned mapping for input or read-only output."""

        metadata_document = self.source_workspace_metadata_document(plate_path)
        subdirectories = self._metadata_subdirectories(
            metadata_document,
            plate_path,
        )
        mapped_subdirectories = {
            subdirectory_name: subdirectory_metadata
            for subdirectory_name, subdirectory_metadata in subdirectories.items()
            if subdirectory_metadata.get(FIELDS.WORKSPACE_MAPPING)
        }
        if not mapped_subdirectories:
            return None
        if len(mapped_subdirectories) == 1:
            return next(iter(mapped_subdirectories.values()))

        projected_metadata = self._metadata_projection(subdirectories, plate_path)
        if not projected_metadata.get(FIELDS.WORKSPACE_MAPPING):
            raise ValueError(
                f"OpenHCS selected metadata for {plate_path} "
                "does not own one of the declared workspace mappings."
            )
        return projected_metadata

    def build_metadata_view_document(
        self,
        plate_path: Union[str, Path],
        microscope_handler: ViewerMicroscopeHandlerABC,
    ) -> MetadataViewDocument:
        """Project subdirectory-keyed OpenHCS metadata into the standard UI document."""
        metadata_document = self.load_metadata_document(plate_path)
        subdirectories = self._metadata_subdirectories(metadata_document, plate_path)

        entries = tuple(
            _openhcs_metadata_view_entry(
                subdirectory_name,
                subdirectory_data,
            )
            for subdirectory_name, subdirectory_data in subdirectories.items()
        )
        title = (
            f"Metadata - {entries[0].name}"
            if len(entries) == 1
            else f"Metadata - {len(entries)} subdirectories"
        )
        return MetadataViewDocument(
            title=title,
            entries=entries,
            selector_label="Subdirectory:",
        )

    def find_metadata_file(self, plate_path: Union[str, Path]) -> Path:
        """Find the OpenHCS JSON metadata file."""
        plate_p = self._resolve_plate_root(plate_path)
        if not self.filemanager.is_dir(str(plate_p), Backend.DISK.value):
            raise MetadataNotFoundError(
                f"OpenHCS plate path is not a directory: {plate_p}"
            )

        expected_file = plate_p / self.METADATA_FILENAME
        if self.filemanager.exists(str(expected_file), Backend.DISK.value):
            return expected_file

        raise MetadataNotFoundError(
            f"OpenHCS metadata file '{self.METADATA_FILENAME}' not found at {expected_file}"
        )

    def get_grid_dimensions(self, plate_path: Union[str, Path]) -> Tuple[int, int]:
        """Get grid dimensions from OpenHCS metadata."""
        dims = self._metadata_field(plate_path, FIELDS.GRID_DIMENSIONS)
        if not (
            isinstance(dims, list)
            and len(dims) == 2
            and all(isinstance(d, int) for d in dims)
        ):
            raise ValueError(
                f"'{FIELDS.GRID_DIMENSIONS}' must be a list of two integers in {self.METADATA_FILENAME}"
            )
        return tuple(dims)

    def get_metadata_grid_dimensions(self, plate_path: Union[str, Path]) -> list[int]:
        """Preserve explicitly unknown source layout without inventing a grid."""
        dims = self._metadata_field(plate_path, FIELDS.GRID_DIMENSIONS)
        if dims == []:
            return []
        return list(self.get_grid_dimensions(plate_path))

    def get_pixel_size(self, plate_path: Union[str, Path]) -> float:
        """Require declared physical calibration, never the numeric metadata view."""
        return SourceVoxelSpacing.require_physical_pixel_size(
            self._source_voxel_spacings(plate_path)
        )

    def source_voxel_spacing(self, plate_path: Union[str, Path]) -> SourceVoxelSpacing:
        """Preserve the stored source frame, including unknown/relative units."""
        return SourceVoxelSpacing.common(self._source_voxel_spacings(plate_path))

    def _source_voxel_spacings(
        self, plate_path: Union[str, Path]
    ) -> tuple[SourceVoxelSpacing, ...]:
        """Decode source declarations once for scalar and coordinate projections."""
        return tuple(
            SourceVoxelSpacing.from_source_metadata(source)
            for source in (
                self._metadata_field(plate_path, FIELDS.SOURCE_METADATA, merge=True) or {}
            ).values()
        )

    def get_metadata_pixel_size(self, plate_path: Union[str, Path]) -> float:
        """Read the serialized numeric view without asserting coordinate units."""
        pixel_size = self._metadata_field(plate_path, FIELDS.PIXEL_SIZE)
        if not isinstance(pixel_size, (float, int)):
            raise ValueError(
                f"'{FIELDS.PIXEL_SIZE}' must be a number in {self.METADATA_FILENAME}"
            )
        return float(pixel_size)

    def get_source_filename_parser_name(self, plate_path: Union[str, Path]) -> str:
        """Get source filename parser name from OpenHCS metadata."""
        parser_name = self._metadata_field(plate_path, FIELDS.SOURCE_FILENAME_PARSER_NAME)
        if not (isinstance(parser_name, str) and parser_name):
            raise ValueError(
                f"'{FIELDS.SOURCE_FILENAME_PARSER_NAME}' must be a non-empty string in {self.METADATA_FILENAME}"
            )
        return parser_name

    def get_image_files(
        self, plate_path: Union[str, Path], all_subdirs: bool = False
    ) -> list[str]:
        """Return image files declared by OpenHCS subdirectory metadata."""
        metadata_document = self.load_metadata_document(plate_path)
        subdirectories = self._metadata_subdirectories(metadata_document, plate_path)

        if all_subdirs:
            return [
                image_file
                for subdirectory_name, subdirectory_data in subdirectories.items()
                for image_file in self._image_files(
                    subdirectory_name,
                    subdirectory_data,
                )
            ]

        main_subdirectory_name = self._main_subdirectory_name(
            subdirectories, plate_path
        )
        return list(
            self._image_files(
                main_subdirectory_name,
                subdirectories[main_subdirectory_name],
            )
        )

    def analysis_result_directories(
        self,
        plate_path: Union[str, Path],
    ) -> tuple[AnalysisResultDirectory, ...]:
        """Return OpenHCS analysis results directories declared by metadata."""
        plate_root = self.source_workspace_root(plate_path)
        metadata_document = self.source_workspace_metadata_document(plate_path)
        subdirectories = self._metadata_subdirectories(metadata_document, plate_path)
        source_projection = (
            VirtualWorkspaceSourceProjection.from_openhcs_metadata_if_available(
                plate_root, metadata_document
            )
        )
        return self._analysis_result_directories(
            plate_root, subdirectories, source_projection
        )

    def reconciliation_directories(
        self, plate_path: Union[str, Path], backend: str
    ) -> tuple[Path, ...]:
        """Derive artifact and result destinations from one admitted document.

        Projection records are admitted before workspace fields, as required by
        completed-plate reconciliation. The same admitted records then populate
        the result-directory source authority; they are not decoded a second time.
        """
        plate_root = Path(plate_path)
        metadata_path = METADATA_CONFIG.metadata_path(plate_root)
        if not metadata_path.is_file():
            return tuple(
                directory.path
                for directory in self.analysis_result_directories(plate_root)
            )
        document = OpenHCSMetadataSubdirectories.from_path(metadata_path)
        admitted_entries = {
            name: VirtualWorkspaceSourceProjectionEntries.from_subdirectory(subdirectory)
            for name, subdirectory in document.items()
        }
        return self.reconciliation_directories_from_document(
            plate_root, backend, document, admitted_entries
        )

    def reconciliation_directories_from_document(
        self,
        plate_path: Union[str, Path],
        backend: str,
        document: OpenHCSMetadataSubdirectories,
        admitted_entries: Mapping[str, VirtualWorkspaceSourceProjectionEntries],
    ) -> tuple[Path, ...]:
        """Select destinations from the current transaction's admitted entries."""
        plate_root = Path(plate_path)
        admitted = tuple(
            (
                subdirectory,
                admitted_entries[name],
            )
            for name, subdirectory in document.items()
        )
        directories = tuple(
            plate_root / directory
            for _subdirectory, entries in admitted
            for path, projection in entries.entries.items()
            if (directory := projection.artifact_result_directory(path, backend))
            is not None
        )
        subdirectories = self._metadata_subdirectories(
            document.metadata, plate_root, workspace_root=plate_root,
        )
        source_projection = None
        if document.has_workspace_mapping():
            builder = VirtualWorkspaceSourceProjectionBuilder(plate_root)
            for subdirectory, entries in admitted:
                builder.ingest_workspace_mapping(
                    VirtualWorkspaceMapping.from_subdirectory(subdirectory)
                )
                builder.ingest_admitted_subdirectory(subdirectory, entries)
            source_projection = builder.projection()
        results = self._analysis_result_directories(
            plate_root, subdirectories, source_projection
        )
        return tuple(
            dict.fromkeys((*directories, *(directory.path for directory in results)))
        )

    def _analysis_result_directories(
        self,
        plate_root: Path,
        subdirectories: Mapping[str, Mapping[str, Any]],
        source_projection: VirtualWorkspaceSourceProjection | None,
    ) -> tuple[AnalysisResultDirectory, ...]:
        """Admit declared result paths against their document's source authority."""
        result_directories = []
        for subdirectory_name, subdirectory_data in subdirectories.items():
            result_dir_name = _optional_metadata_field(subdirectory_data, "results_dir")
            if result_dir_name is None:
                continue
            if not isinstance(result_dir_name, str) or not result_dir_name:
                raise ValueError(
                    f"OpenHCS metadata subdirectory {subdirectory_name!r} "
                    "results_dir must be a non-empty string when declared."
                )
            result_directory = AnalysisResultDirectory.from_declared_path(
                subdirectory_name=subdirectory_name,
                path=plate_root / result_dir_name,
                source_projection=source_projection,
            )
            if result_directory is not None:
                result_directories.append(result_directory)
        return tuple(result_directories)

    def _metadata_projection(
        self,
        subdirectories: Mapping[str, Mapping[str, Any]],
        plate_path: Union[str, Path],
    ) -> Dict[str, Any]:
        try:
            main_subdirectory_name = self._main_subdirectory_name(
                subdirectories,
                plate_path,
            )
        except MetadataNotFoundError:
            return self._aggregate_subdirectory_metadata(subdirectories, plate_path)
        return dict(subdirectories[main_subdirectory_name])

    def _aggregate_subdirectory_metadata(
        self,
        subdirectories: Mapping[str, Mapping[str, Any]],
        plate_path: Union[str, Path],
    ) -> Dict[str, Any]:
        """Project no-main output metadata when subdirectories share authority."""
        metadata_by_subdirectory = {
            subdirectory_name: _openhcs_metadata_from_subdirectory(
                subdirectory_name,
                subdirectory_data,
            )
            for subdirectory_name, subdirectory_data in subdirectories.items()
        }

        return {
            FIELDS.MICROSCOPE_HANDLER_NAME: self._consistent_subdirectory_value(
                {
                    subdirectory_name: metadata.microscope_handler_name
                    for subdirectory_name, metadata in metadata_by_subdirectory.items()
                },
                plate_path,
                "microscope_handler_name",
            ),
            FIELDS.SOURCE_FILENAME_PARSER_NAME: self._consistent_subdirectory_value(
                {
                    subdirectory_name: metadata.source_filename_parser_name
                    for subdirectory_name, metadata in metadata_by_subdirectory.items()
                },
                plate_path,
                "source_filename_parser_name",
            ),
            **{
                field: self._merge_subdirectory_mapping(
                    {
                        subdirectory_name: metadata.axis_value_labels[field]
                        for subdirectory_name, metadata in metadata_by_subdirectory.items()
                    },
                    plate_path,
                    field,
                )
                for field in OpenHCSMetadata.collection_fields()
            },
            FIELDS.AVAILABLE_BACKENDS: self._merge_subdirectory_mapping(
                {
                    subdirectory_name: metadata.available_backends
                    for subdirectory_name, metadata in metadata_by_subdirectory.items()
                },
                plate_path,
                "available_backends",
            ),
            FIELDS.WORKSPACE_MAPPING: self._merge_subdirectory_mapping(
                {
                    subdirectory_name: metadata.workspace_mapping
                    for subdirectory_name, metadata in metadata_by_subdirectory.items()
                },
                plate_path,
                "workspace_mapping",
            ),
        }

    @staticmethod
    def _consistent_subdirectory_value(
        values_by_subdirectory: Mapping[str, Any],
        plate_path: Union[str, Path],
        field_name: str,
    ) -> Any:
        values = tuple(values_by_subdirectory.items())
        if not values:
            raise MetadataNotFoundError(
                f"No OpenHCS metadata subdirectories found for {plate_path}."
            )
        first_value = values[0][1]
        conflicting_subdirectories = tuple(
            subdirectory_name
            for subdirectory_name, value in values
            if value != first_value
        )
        if conflicting_subdirectories:
            raise ValueError(
                f"OpenHCS metadata subdirectories for {plate_path} disagree on "
                f"{field_name!r}: {conflicting_subdirectories}"
            )
        return first_value

    @staticmethod
    def _merge_subdirectory_mapping(
        values_by_subdirectory: Mapping[str, Mapping[str, Any] | None],
        plate_path: Union[str, Path],
        field_name: str,
    ) -> Dict[str, Any] | None:
        merged: Dict[str, Any] = {}
        observed = False
        for subdirectory_name, values in values_by_subdirectory.items():
            if values is None:
                continue
            observed = True
            if not isinstance(values, Mapping):
                raise ValueError(
                    f"OpenHCS metadata subdirectory {subdirectory_name!r} field "
                    f"{field_name!r} must be a mapping in {plate_path}."
                )
            for key, value in values.items():
                normalized_key = str(key)
                if normalized_key in merged and merged[normalized_key] != value:
                    raise ValueError(
                        f"OpenHCS metadata subdirectories for {plate_path} "
                        f"disagree on {field_name!r}[{normalized_key!r}]."
                    )
                merged[normalized_key] = value
        return merged if observed else None

    def _metadata_subdirectories(
        self,
        metadata_document: Mapping[str, Any],
        plate_path: Union[str, Path],
        *,
        workspace_root: Path | None = None,
    ) -> Mapping[str, Mapping[str, Any]]:
        if FIELDS.SUBDIRECTORIES not in metadata_document:
            raise MetadataNotFoundError(
                f"No subdirectories found in metadata for {plate_path}"
            )

        subdirectories = metadata_document[FIELDS.SUBDIRECTORIES]
        if not isinstance(subdirectories, Mapping) or not subdirectories:
            raise MetadataNotFoundError(
                f"No subdirectories found in metadata for {plate_path}"
            )

        for subdirectory_name, subdirectory_data in subdirectories.items():
            if not isinstance(subdirectory_name, str):
                raise ValueError(
                    "OpenHCS metadata subdirectory key must be a string: "
                    f"{subdirectory_name!r}"
                )
            if not isinstance(subdirectory_data, Mapping):
                raise ValueError(
                    f"OpenHCS metadata subdirectory {subdirectory_name!r} "
                    "must be a mapping."
                )

        root = (
            self.source_workspace_root(plate_path)
            if workspace_root is None else workspace_root
        ).absolute()
        requested = Path(plate_path).absolute()
        if requested != root:
            matches = tuple(
                name for name in subdirectories
                if requested.is_relative_to(root / name)
            )
            if not matches:
                raise MetadataNotFoundError(
                    f"No declared OpenHCS projection contains {plate_path}."
                )
            selected = max(matches, key=lambda name: len(Path(name).parts))
            return {selected: subdirectories[selected]}
        return cast(Mapping[str, Mapping[str, Any]], subdirectories)

    def _main_subdirectory_name(
        self,
        subdirectories: Mapping[str, Mapping[str, Any]],
        plate_path: Union[str, Path],
    ) -> str:
        if len(subdirectories) == 1:
            return next(iter(subdirectories))

        main_subdirectories = tuple(
            subdirectory_name
            for subdirectory_name, subdirectory_data in subdirectories.items()
            if _optional_metadata_field(subdirectory_data, "main") is True
        )
        if len(main_subdirectories) == 1:
            return main_subdirectories[0]
        if not main_subdirectories:
            raise MetadataNotFoundError(
                f"Multiple OpenHCS metadata subdirectories exist for {plate_path}, "
                "but none is marked main."
            )
        raise ValueError(
            f"Multiple OpenHCS metadata subdirectories are marked main for {plate_path}: "
            f"{main_subdirectories}"
        )

    def _image_files(
        self,
        subdirectory_name: str,
        subdirectory_data: Mapping[str, Any],
    ) -> tuple[str, ...]:
        if FIELDS.IMAGE_FILES not in subdirectory_data:
            raise ValueError(
                f"OpenHCS metadata subdirectory {subdirectory_name!r} is missing "
                f"required field {FIELDS.IMAGE_FILES!r}."
            )
        image_files = subdirectory_data[FIELDS.IMAGE_FILES]
        if not isinstance(image_files, list):
            raise ValueError(
                f"OpenHCS metadata subdirectory {subdirectory_name!r} field "
                f"{FIELDS.IMAGE_FILES!r} must be a list."
            )
        return tuple(str(image_file) for image_file in image_files)

    # Optional metadata getters
    def _get_optional_metadata_dict(
        self, plate_path: Union[str, Path], key: str
    ) -> Optional[Dict[str, Optional[str]]]:
        """Helper to get optional dictionary metadata."""
        value = self._metadata_field(plate_path, key, merge=True)
        return (
            {
                str(item_key): None if item_value is None else str(item_value)
                for item_key, item_value in value.items()
            }
            if isinstance(value, dict)
            else None
        )

    def component_value_set(
        self,
        plate_path: Union[str, Path],
    ) -> MetadataComponentValueSet:
        """Read every canonical component through the persisted schema declaration."""

        return MetadataComponentValueSet(
            (
                (
                    component,
                    self._get_optional_metadata_dict(
                        plate_path,
                        component.metadata_collection_field,
                    ),
                )
                for component in AxisFamily.active().axes
            )
        )

    def get_objective_values(
        self, plate_path: Union[str, Path]
    ) -> Optional[Dict[str, str]]:
        """Get objective lens information if available."""
        return self._get_optional_metadata_dict(plate_path, FIELDS.OBJECTIVES)

    def get_plate_acquisition_datetime(
        self, plate_path: Union[str, Path]
    ) -> Optional[str]:
        """Get plate acquisition datetime if available."""
        return self._get_optional_metadata_str(plate_path, FIELDS.ACQUISITION_DATETIME)

    def get_plate_name(self, plate_path: Union[str, Path]) -> Optional[str]:
        """Get plate name if available."""
        return self._get_optional_metadata_str(plate_path, FIELDS.PLATE_NAME)

    def _get_optional_metadata_str(
        self, plate_path: Union[str, Path], field: str
    ) -> Optional[str]:
        """Helper to get optional string metadata field."""
        value = self._metadata_field(plate_path, field)
        return value if isinstance(value, str) and value else None

    def backend_availability(self, input_dir: Union[str, Path]) -> Dict[str, bool]:
        """
        Get available storage backends for the input directory.

        This method resolves the plate root from the input directory,
        loads the OpenHCS metadata, and returns the available backends.

        Args:
            input_dir: Path to the input directory (may be plate root or subdirectory)

        Returns:
            Dictionary mapping backend names to availability (e.g., {"disk": True, "zarr": False})

        Raises:
            MetadataNotFoundError: If metadata file cannot be found or parsed
        """
        available_backends = self._metadata_field(
            input_dir, FIELDS.AVAILABLE_BACKENDS, merge=True,
        ) or {}

        if not isinstance(available_backends, dict):
            logger.warning(
                f"Invalid available_backends format in metadata: {available_backends}"
            )
            return {}

        return available_backends

    def _resolve_plate_root(self, input_dir: Union[str, Path]) -> Path:
        """
        Resolve the plate root directory from an input directory.

        The input directory may be the plate root itself or a subdirectory.
        This method walks up the directory tree to find the directory containing
        the OpenHCS metadata file.

        Args:
            input_dir: Path to resolve

        Returns:
            Path to the plate root directory

        Raises:
            MetadataNotFoundError: If no metadata file is found
        """
        current_path = Path(input_dir)

        # Walk up the directory tree looking for metadata file
        for path in [current_path] + list(current_path.parents):
            metadata_file = path / self.METADATA_FILENAME
            if self.filemanager.exists(str(metadata_file), Backend.DISK.value):
                return path

        # If not found, raise an error
        raise MetadataNotFoundError(
            f"Could not find {self.METADATA_FILENAME} in {input_dir} or any parent directory"
        )

    def update_available_backends(
        self, plate_path: Union[str, Path], available_backends: Dict[str, bool]
    ) -> None:
        """Update available storage backends in metadata and save to disk."""
        metadata_file_path = get_metadata_path(plate_path)

        try:
            self.atomic_writer.update_available_backends(
                metadata_file_path, available_backends
            )
            self.invalidate_metadata_cache()
            logger.info(
                f"Updated available backends to {available_backends} in {metadata_file_path}"
            )
        except MetadataWriteError as e:
            raise ValueError(f"Failed to update available backends: {e}") from e


@dataclass(frozen=True)
class OpenHCSMetadata:
    """
    Declarative OpenHCS metadata structure.

    Fail-loud: All fields are required, no defaults, no fallbacks.
    """

    microscope_handler_name: str
    source_filename_parser_name: str
    grid_dimensions: List[int]
    pixel_size: float
    image_files: List[str]
    axis_value_labels: Dict[str, Optional[Dict[str, Optional[str]]]]
    """Value labels per declared axis, keyed by its ``metadata_collection_field``."""
    available_backends: Dict[str, bool]
    workspace_mapping: Optional[Dict[str, Any]] = (
        None  # Virtual path -> path string or structured backend ref
    )
    source_metadata: Optional[Dict[str, Dict[str, str]]] = (
        None  # Virtual or real path → source metadata fields
    )
    source_projection: Optional[List[Dict[str, Any]]] = (
        None  # Typed source-plane projection records
    )
    source_diagnostics: Optional[List[Dict[str, Any]]] = (
        None  # Source-level exclusions and warnings
    )
    main: Optional[bool] = (
        None  # Indicates if this subdirectory is the primary/input subdirectory
    )
    results_dir: Optional[str] = (
        None  # Sibling directory containing analysis results for this subdirectory
    )

    @staticmethod
    def collection_fields() -> tuple[str, ...]:
        """Persisted value-label keys, one per declared axis."""

        return tuple(axis.metadata_collection_field for axis in AxisFamily.active().axes)

    @staticmethod
    def labels_by_field(
        values_by_axis: Mapping[type[Axis], Any],
    ) -> Dict[str, Any]:
        """Key one axis-keyed mapping by persisted collection field."""

        return {
            axis.metadata_collection_field: values_by_axis[axis]
            for axis in AxisFamily.active().axes
        }

    def labels_for(self, axis: type[Axis]) -> Optional[Dict[str, Optional[str]]]:
        return self.axis_value_labels[axis.metadata_collection_field]

    def to_document(self) -> Dict[str, Any]:
        """The persisted subdirectory record: value labels sit at top level."""

        document = asdict(self)
        document.update(document.pop("axis_value_labels"))
        return document

    @classmethod
    def from_component_value_set(
        cls,
        *,
        component_values: MetadataComponentValueSet,
        microscope_handler_name: str,
        source_filename_parser_name: str,
        grid_dimensions: List[int],
        pixel_size: float,
        image_files: List[str],
        available_backends: Dict[str, bool],
        source_diagnostics: Optional[List[Dict[str, Any]]] = None,
        main: Optional[bool] = None,
    ) -> "OpenHCSMetadata":
        """Construct persisted metadata from the nominal component authority."""

        def serialized_values(
            component: type[Axis],
        ) -> Optional[Dict[str, str | None]]:
            values = component_values.values_for(component)
            return None if values is None else dict(values)

        return cls(
            microscope_handler_name=microscope_handler_name,
            source_filename_parser_name=source_filename_parser_name,
            grid_dimensions=grid_dimensions,
            pixel_size=pixel_size,
            image_files=image_files,
            axis_value_labels=cls.labels_by_field(
                {component: serialized_values(component) for component in AxisFamily.active().axes}
            ),
            available_backends=available_backends,
            source_diagnostics=source_diagnostics,
            main=main,
        )


_OPENHCS_METADATA_REQUIRED_FIELDS = (
    FIELDS.MICROSCOPE_HANDLER_NAME,
    FIELDS.SOURCE_FILENAME_PARSER_NAME,
    FIELDS.GRID_DIMENSIONS,
    FIELDS.PIXEL_SIZE,
    FIELDS.IMAGE_FILES,
    FIELDS.AVAILABLE_BACKENDS,
)


def _openhcs_metadata_from_subdirectory(
    subdirectory_name: str,
    subdirectory_data: Mapping[str, Any],
) -> OpenHCSMetadata:
    missing_fields = tuple(
        field
        for field in (*_OPENHCS_METADATA_REQUIRED_FIELDS, *OpenHCSMetadata.collection_fields())
        if field not in subdirectory_data
    )
    if missing_fields:
        raise ValueError(
            f"OpenHCS metadata subdirectory {subdirectory_name!r} is missing "
            f"required fields: {missing_fields}"
        )

    return OpenHCSMetadata(
        microscope_handler_name=str(subdirectory_data[FIELDS.MICROSCOPE_HANDLER_NAME]),
        source_filename_parser_name=str(
            subdirectory_data[FIELDS.SOURCE_FILENAME_PARSER_NAME]
        ),
        grid_dimensions=list(subdirectory_data[FIELDS.GRID_DIMENSIONS]),
        pixel_size=float(subdirectory_data[FIELDS.PIXEL_SIZE]),
        image_files=list(subdirectory_data[FIELDS.IMAGE_FILES]),
        axis_value_labels={
            field: subdirectory_data[field]
            for field in OpenHCSMetadata.collection_fields()
        },
        available_backends=dict(subdirectory_data[FIELDS.AVAILABLE_BACKENDS]),
        workspace_mapping=_optional_metadata_field(
            subdirectory_data, FIELDS.WORKSPACE_MAPPING
        ),
        source_metadata=_optional_metadata_field(
            subdirectory_data, FIELDS.SOURCE_METADATA
        ),
        source_projection=_optional_metadata_field(
            subdirectory_data, "source_projection"
        ),
        source_diagnostics=list(
            _source_diagnostics_from_subdirectory(
                subdirectory_name,
                subdirectory_data,
            )
        )
        or None,
        main=_optional_metadata_field(subdirectory_data, "main"),
        results_dir=_optional_metadata_field(subdirectory_data, "results_dir"),
    )


def _openhcs_metadata_view_entry(
    subdirectory_name: str,
    subdirectory_data: Mapping[str, Any],
) -> MetadataViewEntry:
    """Build one read-only OpenHCS metadata entry and concise summary."""

    metadata = _openhcs_metadata_from_subdirectory(
        subdirectory_name,
        subdirectory_data,
    )
    diagnostic_summary = (
        f"; source diagnostics: {len(metadata.source_diagnostics)}"
        if metadata.source_diagnostics
        else ""
    )
    return MetadataViewEntry(
        name=subdirectory_name,
        object_instance=metadata,
        summary=(
            f"Image files: {len(metadata.image_files)} (hidden)" f"{diagnostic_summary}"
        ),
    )


def _source_diagnostics_from_subdirectory(
    subdirectory_name: str,
    subdirectory_data: Mapping[str, Any],
) -> tuple[Dict[str, Any], ...]:
    """Validate and project optional structured source diagnostics."""

    if FIELDS.SOURCE_DIAGNOSTICS not in subdirectory_data:
        return ()
    diagnostics = subdirectory_data[FIELDS.SOURCE_DIAGNOSTICS]
    if not isinstance(diagnostics, list):
        raise TypeError(
            f"OpenHCS metadata subdirectory {subdirectory_name!r} field "
            f"{FIELDS.SOURCE_DIAGNOSTICS!r} must be a list."
        )
    projected: list[Dict[str, Any]] = []
    for diagnostic_index, diagnostic in enumerate(diagnostics):
        if not isinstance(diagnostic, Mapping):
            raise TypeError(
                f"OpenHCS metadata subdirectory {subdirectory_name!r} source "
                f"diagnostic {diagnostic_index} must be an object."
            )
        projected.append(dict(diagnostic))
    return tuple(projected)


def _optional_metadata_field(
    metadata: Mapping[str, Any],
    field: str,
) -> Any | None:
    if field in metadata:
        return metadata[field]
    return None


@dataclass(frozen=True)
class OpenHCSMetadataGenerationRequest:
    """Authoritative request for writing one OpenHCS metadata subdirectory."""

    context: "ProcessingContext"
    output_dir: str
    write_backend: str
    is_main: bool
    sub_dir: str
    results_dir: Optional[str] = None
    grid_dimensions: tuple[int, int] | None = None
    pixel_size: float | None = None


class OpenHCSMetadataGenerator(OpenHCSMetadataBase):
    """
    Generator for OpenHCS metadata files.

    Handles creation of openhcs_metadata.json files for processed plates,
    extracting information from processing context and output directories.

    Design principle: Generate metadata that accurately reflects what exists on disk
    after processing, not what was originally intended or what the source contained.
    """

    def __init__(self, filemanager: FileManager):
        """
        Initialize the metadata generator.

        Args:
            filemanager: FileManager instance for file operations
        """
        super().__init__(filemanager)
        self.logger = logging.getLogger(__name__)

    def create_metadata(
        self,
        context: "ProcessingContext",
        output_dir: str,
        write_backend: str,
        is_main: bool = False,
        plate_root: str = None,
        sub_dir: str = None,
        results_dir: str = None,
        skip_if_complete: bool = False,
        allow_none_override: bool = False,
        grid_dimensions: tuple[int, int] | None = None,
        pixel_size: float | None = None,
    ) -> None:
        """Create or update subdirectory-keyed OpenHCS metadata file.

        Args:
            skip_if_complete: If True, skip update if the record already has every axis's value labels
            allow_none_override: If True, None values override existing fields;
                               if False (default), None values are filtered out to preserve existing fields
        """
        plate_root_path = Path(plate_root)
        metadata_path = get_metadata_path(plate_root_path)
        if (grid_dimensions is None) != (pixel_size is None):
            raise ValueError(
                "Explicit metadata generation requires both grid_dimensions "
                "and pixel_size."
            )

        # Check if metadata already complete (if requested)
        if skip_if_complete and metadata_path.exists():
            import json

            with open(metadata_path, "r") as f:
                existing = json.load(f)

            subdir_data = existing.get(FIELDS.SUBDIRECTORIES, {}).get(sub_dir, {})
            if all(
                field in subdir_data for field in OpenHCSMetadata.collection_fields()
            ):
                self.logger.debug(f"Metadata for {sub_dir} already complete, skipping")
                return

        # Extract metadata from current state
        current_metadata = self._extract_metadata_from_disk_state(
            OpenHCSMetadataGenerationRequest(
                context=context,
                output_dir=output_dir,
                write_backend=write_backend,
                is_main=is_main,
                sub_dir=sub_dir,
                results_dir=results_dir,
                grid_dimensions=grid_dimensions,
                pixel_size=pixel_size,
            )
        )
        metadata_dict = current_metadata.to_document()

        # Filter None values unless override allowed
        if not allow_none_override:
            metadata_dict = {k: v for k, v in metadata_dict.items() if v is not None}

        self.atomic_writer.merge_subdirectory_metadata(
            metadata_path, {sub_dir: metadata_dict}
        )

    def _extract_metadata_from_disk_state(
        self,
        request: OpenHCSMetadataGenerationRequest,
    ) -> OpenHCSMetadata:
        """Extract metadata reflecting current disk state after processing.

        CRITICAL: Extracts axis value labels
        by parsing actual filenames in output_dir, NOT from the original input metadata cache.
        This ensures metadata accurately reflects what was actually written, not what was in the input.

        For example, if processing filters to only channels 1-2, the metadata will show only those channels.
        """
        context = request.context
        handler = context.microscope_handler

        if context.metadata_cache is None:
            raise RuntimeError(
                "ProcessingContext metadata_cache must be populated by create_context()"
            )

        actual_files = self.filemanager.list_image_files(
            request.output_dir,
            request.write_backend,
        )
        relative_files = [f"{request.sub_dir}/{Path(f).name}" for f in actual_files]

        # Calculate relative results directory path (relative to plate root)
        # Example: "images_results" for images subdirectory
        relative_results_dir = None
        if request.results_dir:
            results_path = Path(request.results_dir)
            relative_results_dir = (
                results_path.name
            )  # Just the directory name, not full path

        if request.grid_dimensions is None:
            grid_dimensions = handler.metadata_handler.get_metadata_grid_dimensions(
                context.input_dir
            )
            pixel_size = handler.metadata_handler.get_metadata_pixel_size(
                context.input_dir
            )
        else:
            grid_dimensions = request.grid_dimensions
            pixel_size = request.pixel_size

        # CRITICAL: Extract component metadata from actual output files by parsing filenames
        # This ensures metadata reflects what was actually written, not the original input
        component_metadata = self._extract_component_metadata_from_files(
            actual_files, handler.parser
        )

        # Merge extracted component keys with display names from original metadata cache
        # This preserves display names (e.g., "tl-20") while using actual output components
        merged_metadata = self._merge_component_metadata(
            component_metadata, context.metadata_cache
        )

        return OpenHCSMetadata(
            microscope_handler_name=handler.source_name,
            source_filename_parser_name=handler.parser.__class__.__name__,
            grid_dimensions=grid_dimensions,
            pixel_size=pixel_size,
            image_files=relative_files,
            axis_value_labels=OpenHCSMetadata.labels_by_field(merged_metadata),
            available_backends={request.write_backend: True},
            workspace_mapping=None,  # Preserve existing - filtered out by create_metadata()
            main=request.is_main if request.is_main else None,
            results_dir=relative_results_dir,
        )

    def _extract_component_metadata_from_files(
        self, file_paths: list, parser
    ) -> Dict[type[Axis], Optional[Dict[str, Optional[str]]]]:
        """
        Extract component metadata by parsing actual filenames.

        Args:
            file_paths: List of image file paths (guaranteed properly formed)
            parser: FilenameParser instance

        Returns:
            Dict mapping each axis to its component metadata (key -> display_name)

        """
        result = {component: {} for component in AxisFamily.active().axes}

        for file_path in file_paths:
            filename = Path(file_path).name
            parsed = parser.parse_filename(filename)
            if parsed is None:
                continue

            # Extract each component from the parsed filename
            for component in AxisFamily.active().axes:
                parsed_value = parsed.value_for(component)
                if parsed_value is not None:
                    component_value = str(parsed_value)
                    # Store with None as display name (will be merged with original metadata display names)
                    if component_value not in result[component]:
                        result[component][component_value] = None

        # Convert empty dicts to None (no metadata for that component)
        return {
            component: metadata_dict if metadata_dict else None
            for component, metadata_dict in result.items()
        }

    def _merge_component_metadata(
        self,
        extracted: Dict[type[Axis], Optional[Dict[str, Optional[str]]]],
        cache: Dict[type[Axis], Optional[Dict[str, Optional[str]]]],
    ) -> Dict[type[Axis], Optional[Dict[str, Optional[str]]]]:
        """
        Merge extracted component keys with display names from original metadata cache.

        For each component:
        - Use extracted keys (what actually exists in output)
        - Preserve display names from cache (e.g., "tl-20" for channel "1")
        - If no display name in cache, use None

        Args:
            extracted: Component metadata extracted from output filenames
            cache: Original metadata cache with display names

        Returns:
            Merged metadata with actual components and preserved display names
        """
        result = {}
        for component in AxisFamily.active().axes:
            extracted_dict = extracted.get(component)
            cache_dict = cache.get(component)

            if extracted_dict is None:
                result[component] = None
            else:
                # For each extracted key, get display name from cache if available
                merged = {}
                for key in extracted_dict.keys():
                    display_name = cache_dict.get(key) if cache_dict else None
                    merged[key] = display_name

                result[component] = merged if merged else None

        return result


from openhcs.core.dataset_sources.source import (
    DatasetSource,
    PreparedWorkspaceSource,
)
from openhcs.core.dataset_sources.interfaces import FilenameParser


class OpenHCSDatasetSource(PreparedWorkspaceSource, DatasetSource):
    """
    DatasetSource for OpenHCS pre-processed format.

    This handler reads plates that have been standardized, with metadata
    provided in an 'openhcs_metadata.json' file. It dynamically loads the
    appropriate FilenameParser based on the metadata.
    """

    # Class attributes for automatic registration
    source_name = "openhcsdata"
    metadata_handler_class = OpenHCSMetadataHandler

    @classmethod
    def create(
        cls, *, filemanager: FileManager, pattern_format: Optional[str] = None,
        source_bindings_config=None,
    ) -> "OpenHCSDatasetSource":
        """Keep prepared source ownership while consuming declared admission."""
        from openhcs.core.source_bindings import source_bindings_defaults_to_base

        handler = super().create(
            filemanager=filemanager, pattern_format=pattern_format,
            source_bindings_config=source_bindings_config,
        )
        handler._source_bindings_config = (
            None if source_bindings_config is None
            else source_bindings_defaults_to_base(source_bindings_config)
        )
        return handler

    def source_bindings_still_required(self):
        """Expose the original prepared-workspace declaration to runtime readers."""
        return self._source_bindings_config


    @classmethod
    def source_selection_guidance(cls) -> str:
        """Explain when OpenHCS workspace metadata is authoritative."""

        return (
            "Use for a workspace already prepared by OpenHCS and carrying its "
            "metadata document. The recorded workspace metadata, not raw vendor "
            "filename resemblance, owns parser and backend selection."
        )

    def __init__(self, filemanager: FileManager, pattern_format: Optional[str] = None):
        """
        Initialize the OpenHCSDatasetSource.

        Args:
            filemanager: FileManager instance for file operations.
            pattern_format: Optional pattern format string, passed to dynamically loaded parser.
        """
        self.filemanager = filemanager
        self.metadata_handler = OpenHCSMetadataHandler(filemanager)
        self._parser: Optional[FilenameParser] = None
        self.plate_folder: Optional[Path] = (
            None  # Will be set by factory or post_workspace
        )
        self.pattern_format = pattern_format  # Store for parser instantiation
        self._source_bindings_config = None

        # Initialize super with a None parser. The actual parser is loaded dynamically.
        # The `parser` property will handle on-demand loading.
        super().__init__(parser=None, metadata_handler=self.metadata_handler)

    def _load_and_get_parser(self) -> FilenameParser:
        """
        Ensures the dynamic filename parser is loaded based on metadata from plate_folder.
        This method requires self.plate_folder to be set.
        """
        if self._parser is None:
            if self.plate_folder is None:
                raise RuntimeError(
                    "OpenHCSHandler: plate_folder not set. Cannot determine and load the source filename parser."
                )

            parser_name = self.metadata_handler.get_source_filename_parser_name(
                self.plate_folder
            )
            available_parsers = _get_available_filename_parsers()
            ParserClass = available_parsers.get(parser_name)

            if not ParserClass:
                raise ValueError(
                    f"Unknown or unsupported filename parser '{parser_name}' specified in "
                    f"{OpenHCSMetadataHandler.METADATA_FILENAME} for plate {self.plate_folder}. "
                    f"Available parsers: {list(available_parsers.keys())}"
                )

            try:
                # Attempt to instantiate with filemanager and pattern_format
                self._parser = ParserClass(
                    filemanager=self.filemanager, pattern_format=self.pattern_format
                )
                logger.info(
                    f"OpenHCSHandler for plate {self.plate_folder} loaded source filename parser: {parser_name} with filemanager and pattern_format."
                )
            except TypeError:
                try:
                    # Attempt with filemanager only
                    self._parser = ParserClass(filemanager=self.filemanager)
                    logger.info(
                        f"OpenHCSHandler for plate {self.plate_folder} loaded source filename parser: {parser_name} with filemanager."
                    )
                except TypeError:
                    # Attempt with default constructor
                    self._parser = ParserClass()
                    logger.info(
                        f"OpenHCSHandler for plate {self.plate_folder} loaded source filename parser: {parser_name} with default constructor."
                    )

        return self._parser

    @property
    def parser(self) -> FilenameParser:
        """
        Provides the dynamically loaded FilenameParser.
        The actual parser is determined from the 'openhcs_metadata.json' file.
        Requires `self.plate_folder` to be set prior to first access.
        """
        # If plate_folder is not set here, it means it wasn't set by the factory
        # nor by a method like post_workspace before parser access.
        if self.plate_folder is None:
            # This situation should ideally be avoided by ensuring plate_folder is set appropriately.
            raise RuntimeError(
                "OpenHCSHandler: plate_folder must be set before accessing the parser property."
            )

        return self._load_and_get_parser()

    @parser.setter
    def parser(self, value: Optional[FilenameParser]):
        """
        Allows setting the parser instance. Used by base class __init__ if it attempts to set it,
        though our dynamic loading means we primarily manage it internally.
        """
        # If the base class __init__ tries to set it (e.g. to None as we passed),
        # this setter will be called. We want our dynamic loading to take precedence.
        # If an actual parser is passed, we could use it, but it would override dynamic logic.
        # For now, if None is passed (from our super call), _parser remains None until dynamically loaded.
        # If a specific parser is passed, it will be set.
        if value is not None:
            logger.debug(
                "OpenHCSDatasetSource.parser being explicitly set to: "
                f"{type(value).__name__}"
            )
        self._parser = value

    @property
    def root_dir(self) -> str:
        """
        Root directory for OpenHCS is determined from metadata.

        OpenHCS plates can have multiple subdirectories (e.g., "zarr", "images", ".").
        The root_dir is determined dynamically from the main subdirectory in metadata.
        This property returns a placeholder - actual root_dir is determined at runtime.
        """
        # This is determined dynamically from metadata in initialize_workspace
        # Return empty string as placeholder (not used for virtual workspace)
        return ""



    @property
    def compatible_backends(self) -> List[Backend]:
        """
        OpenHCS is compatible with ZARR (preferred) and DISK (fallback) backends.

        ZARR: Advanced chunked storage for large datasets (preferred)
        DISK: Standard file operations for compatibility (fallback)
        """
        return [Backend.ZARR, Backend.DISK]

    def available_backends(self, plate_path: Union[str, Path]) -> List[Backend]:
        """
        Get available storage backends for OpenHCS plates.

        OpenHCS plates can support multiple backends based on what actually exists on disk.
        This method checks the metadata to see what backends are actually available.
        """
        try:
            # Get available backends from metadata as Dict[str, bool]
            available_backends_dict = self.metadata_handler.backend_availability(
                plate_path
            )

            # Convert to List[Backend] by filtering compatible backends that are available
            available_backends = []
            for backend_enum in self.compatible_backends:
                backend_name = backend_enum.value
                if available_backends_dict.get(backend_name, False):
                    available_backends.append(backend_enum)

            # If no backends are available from metadata, fall back to compatible backends
            # This handles cases where metadata might not have the available_backends field
            if not available_backends:
                logger.warning(
                    f"No available backends found in metadata for {plate_path}, using all compatible backends"
                )
                return self.compatible_backends

            return available_backends

        except Exception as e:
            logger.warning(
                f"Failed to get available backends from metadata for {plate_path}: {e}"
            )
            # Fall back to all compatible backends if metadata reading fails
            return self.compatible_backends

    def get_primary_backend(
        self, plate_path: Union[str, Path], filemanager: "FileManager"
    ) -> str:
        """
        Get the primary backend name for OpenHCS plates.

        Uses metadata-based detection to determine the primary backend.
        Preference hierarchy: zarr > virtual_workspace > disk
        Registers virtual_workspace backend if needed.

        Args:
            plate_path: Input directory (may be subdirectory like zarr/)
            filemanager: FileManager instance for backend registration
        """
        # plate_folder must be set before calling this method
        if self.plate_folder is None:
            raise RuntimeError(
                "OpenHCSHandler.determine_backend_preference: plate_folder not set. "
                "Call determine_input_dir() or post_workspace() first."
            )

        available_backends_dict = self.metadata_handler.backend_availability(
            self.plate_folder
        )

        # Preference hierarchy: zarr > virtual_workspace > disk
        # 1. Prefer zarr if available (best performance for large datasets)
        if "zarr" in available_backends_dict and available_backends_dict["zarr"]:
            return "zarr"

        # 2. A declared workspace mapping is itself the virtual-workspace authority.
        subdir_metadata = self.metadata_handler.workspace_mapping_metadata(
            self.plate_folder
        )
        if subdir_metadata is not None:
            self._register_declared_workspace_backends(
                self.plate_folder,
                subdir_metadata,
                filemanager,
            )
            return Backend.VIRTUAL_WORKSPACE.value

        # 3. Fall back to first available backend (usually disk)
        return next(iter(available_backends_dict.keys()))

    def initialize_workspace(self, plate_path: Path, filemanager: FileManager) -> Path:
        """
        OpenHCS format doesn't need workspace - determines the correct input subdirectory from metadata.

        Args:
            plate_path: Path to the original plate directory
            filemanager: FileManager instance for file operations

        Returns:
            Path to the main subdirectory containing input images (e.g., plate_path/images)
        """
        logger.info(
            "OpenHCS format: Determining input subdirectory from metadata in %s",
            plate_path,
        )

        plate_root = self.metadata_handler._resolve_plate_root(plate_path)

        # The caller's declared projection selects facts; storage stays root-relative.
        self.plate_folder = plate_path
        if self._source_bindings_config is not None:
            from openhcs.core.source_workspace_projection import VirtualWorkspaceSourceProjectionAuthority

            projection = VirtualWorkspaceSourceProjectionAuthority.from_plate_metadata(
                plate_path=plate_path,
                metadata_handler=self.metadata_handler,
                filemanager=filemanager,
                source_bindings=self._source_bindings_config,
            ).projection_if_available()
            if projection is None and self._source_bindings_config.source_filter_declarations:
                raise ValueError("Prepared source filtering requires a typed workspace projection.")
        logger.debug("OpenHCSHandler: plate_folder set to %s", self.plate_folder)

        # Determine the main subdirectory from metadata - fail-loud on errors
        main_subdir = self.metadata_handler.determine_main_subdirectory(plate_path)
        input_dir = plate_root / main_subdir

        # Check if workspace_mapping exists in metadata - if so, register virtual workspace backend
        subdir_metadata = self._main_subdirectory_metadata(plate_path)

        if subdir_metadata.get("workspace_mapping"):
            self._register_declared_workspace_backends(
                plate_root,
                subdir_metadata,
                filemanager,
            )

        # Verify the subdirectory exists - fail-loud if missing
        if not filemanager.is_dir(str(input_dir), Backend.DISK.value):
            raise FileNotFoundError(
                f"Main subdirectory '{main_subdir}' does not exist at {input_dir}. "
                f"Expected directory structure: {plate_root}/{main_subdir}/"
            )

        logger.info(
            f"OpenHCS input directory determined: {input_dir} "
            f"(subdirectory: {main_subdir})"
        )
        return input_dir

    def _main_subdirectory_metadata(
        self,
        plate_root: Path,
    ) -> Mapping[str, object]:
        metadata = self.metadata_handler.source_workspace_metadata_document(plate_root)
        if not isinstance(metadata, Mapping):
            raise ValueError("OpenHCS source-workspace metadata must be a mapping.")
        subdirectories = metadata.get(FIELDS.SUBDIRECTORIES)
        if not isinstance(subdirectories, Mapping):
            raise ValueError(
                f"OpenHCS metadata missing required {FIELDS.SUBDIRECTORIES!r} mapping."
            )
        main_subdir = self.metadata_handler.determine_main_subdirectory(plate_root)
        subdir_metadata = subdirectories.get(main_subdir)
        if not isinstance(subdir_metadata, Mapping):
            raise ValueError(
                f"OpenHCS metadata missing required subdirectory {main_subdir!r}."
            )
        return subdir_metadata

    def _register_declared_workspace_backends(
        self,
        plate_root: Path,
        subdir_metadata: Mapping[str, object],
        filemanager: FileManager,
    ) -> None:
        source_handler_name = str(subdir_metadata[FIELDS.MICROSCOPE_HANDLER_NAME])
        source_handler_type = DatasetSource.__registry__.get(source_handler_name)
        if source_handler_type is None:
            raise ValueError(
                "OpenHCS metadata declares unknown workspace handler "
                f"{source_handler_name!r}."
            )
        source_handler_type.register_workspace_backends(
            self.metadata_handler.source_workspace_root(plate_root),
            filemanager,
        )

    @classmethod
    def register_workspace_backends(
        cls, plate_path: Union[str, Path], filemanager: FileManager,
    ) -> None:
        """Register storage at its metadata root, not the selected projection child."""
        workspace_root = OpenHCSMetadataHandler(filemanager).source_workspace_root(plate_path)
        super().register_workspace_backends(workspace_root, filemanager)

    def post_workspace(
        self,
        plate_path: Union[str, Path],
        filemanager: FileManager,
        skip_preparation: bool = False,
    ) -> Path:
        """
        Hook called after virtual workspace mapping creation.
        For OpenHCS, this ensures the plate_folder is set (if not already) which allows
        the parser to be loaded using this plate_path. It then calls the base
        implementation which handles filename normalization using the loaded parser.
        """
        current_plate_folder = Path(plate_path)
        if self.plate_folder is None:
            logger.info(
                f"OpenHCSHandler.post_workspace: Setting plate_folder to {current_plate_folder}."
            )
            self.plate_folder = current_plate_folder
            self._parser = None  # Reset parser if plate_folder changes or is set for the first time
        elif self.plate_folder != current_plate_folder:
            logger.warning(
                f"OpenHCSHandler.post_workspace: plate_folder was {self.plate_folder}, "
                f"now processing {current_plate_folder}. Re-initializing parser."
            )
            self.plate_folder = current_plate_folder
            self._parser = None  # Force re-initialization for the new path

        # Accessing self.parser here will trigger _load_and_get_parser() if not already loaded
        _ = self.parser

        logger.info(
            f"OpenHCSHandler (plate: {self.plate_folder}): Files are expected to be pre-normalized. "
            "Superclass post_workspace will run with the dynamically loaded parser."
        )
        return super().post_workspace(plate_path, filemanager, skip_preparation)

    # The following methods from DatasetSource delegate to `self.parser`.
    # The `parser` property will ensure the correct, dynamically loaded parser is used.
    # No explicit override is needed for them unless special behavior for OpenHCS is required
    # beyond what the dynamically loaded original parser provides.
    # - parse_filename(self, filename: str)
    # - construct_filename(self, well: str, ...)
    # - auto_detect_patterns(self, folder_path: Union[str, Path], ...)
    # - path_list_from_pattern(self, directory: Union[str, Path], ...)

    # Metadata handling methods are delegated to `self.metadata_handler` by the base class.
    # - find_metadata_file(self, plate_path: Union[str, Path])
    # - get_grid_dimensions(self, plate_path: Union[str, Path])
    # - get_pixel_size(self, plate_path: Union[str, Path])
    # These will use our OpenHCSMetadataHandler correctly.
