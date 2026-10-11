"""Vendor acquisition layouts opened through a virtual workspace mapping."""

from __future__ import annotations

import logging
import os
from abc import abstractmethod
from pathlib import Path

from polystore.filemanager import FileManager
from polystore.metadata_writer import resolve_subdirectory_path

from openhcs.constants.constants import Backend
from openhcs.core.dataset_sources.openhcs_format import OpenHCSMetadataHandler
from openhcs.core.dataset_sources.source import DatasetSource
from openhcs.domains.microscopy.axes import Microscopy

logger = logging.getLogger(__name__)


class VirtualMappingSource(DatasetSource):
    """A vendor layout whose files are mapped to plane filenames in metadata.

    No workspace directory is created: the mapping lives in OpenHCS metadata
    and is read through the virtual workspace backend.
    """

    @abstractmethod
    def _build_virtual_mapping(
        self, dataset_root: Path, filemanager: FileManager
    ) -> Path:
        """Write this layout's mapping to metadata and return the image directory."""

    def initialize_workspace(
        self, dataset_root: Path, filemanager: FileManager
    ) -> Path:
        dataset_root = Path(dataset_root)
        self.dataset_root = dataset_root
        self._build_virtual_mapping(dataset_root, filemanager)
        self._register_virtual_workspace_backend(dataset_root, filemanager)
        return self._normalize_mapped_filenames(dataset_root, filemanager)

    def _normalize_mapped_filenames(
        self,
        dataset_root: Path,
        filemanager: FileManager,
    ) -> Path:
        """Rename mapped files to their padded vendor spelling with a Z index."""
        from polystore.exceptions import MetadataNotFoundError

        from openhcs.core.virtual_workspace_metadata import FIELDS

        metadata = OpenHCSMetadataHandler(filemanager)._load_metadata_dict(dataset_root)
        if FIELDS.SUBDIRECTORIES not in metadata:
            raise MetadataNotFoundError(
                f"'{FIELDS.SUBDIRECTORIES}' is missing from metadata for {dataset_root}."
            )
        subdir_with_mapping = next(
            (
                name
                for name, data in metadata[FIELDS.SUBDIRECTORIES].items()
                if FIELDS.WORKSPACE_MAPPING in data
            ),
            None,
        )
        if subdir_with_mapping is None:
            raise MetadataNotFoundError(
                f"No {FIELDS.WORKSPACE_MAPPING} found in metadata for {dataset_root}."
            )
        image_dir = resolve_subdirectory_path(subdir_with_mapping, dataset_root)

        backend_type = (
            Backend.VIRTUAL_WORKSPACE.value
            if Backend.VIRTUAL_WORKSPACE.value in filemanager.registry
            else Backend.DISK.value
        )
        rename_map = {}
        for file_path in filemanager.list_image_files(image_dir, backend_type):
            listed_name = os.path.basename(str(file_path))
            parsed = self.parser.parse_filename(listed_name)
            if not parsed:
                logger.warning("Could not parse filename: %s", listed_name)
                continue
            if (
                parsed.value_for(Microscopy.Site) is None
                or parsed.value_for(Microscopy.Channel) is None
            ):
                logger.warning("Missing site or channel in filename: %s", listed_name)
                continue
            z_index = parsed.value_for(Microscopy.ZIndex)
            new_name = self.parser.construct_filename(
                parsed.with_value(Microscopy.ZIndex, 1 if z_index is None else z_index)
            )
            if listed_name != new_name:
                rename_map[listed_name] = new_name

        for listed_name, new_name in rename_map.items():
            listed_path = Path(image_dir) / listed_name
            new_path = Path(image_dir) / new_name
            try:
                filemanager.ensure_directory(new_path.parent, Backend.DISK.value)
                filemanager.move(
                    listed_path, new_path, Backend.DISK.value, replace_symlinks=True
                )
            except Exception as e:
                logger.error("Error renaming %s to %s: %s", listed_path, new_path, e)
        return image_dir
