"""
ImageXpress microscope implementations for openhcs.

This module provides concrete implementations of FilenameParser and MetadataHandler
for ImageXpress microscopes.
"""

import logging
import re
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Union, Type

from openhcs.constants.constants import AllComponents, Backend, Microscope
from openhcs.core.components.parser_metaprogramming import (
    format_filename_component,
)
from polystore.exceptions import MetadataNotFoundError
from polystore.filemanager import FileManager
from openhcs.microscopes.microscope_base import MicroscopeHandler
from openhcs.microscopes.microscope_interfaces import (
    DiskImageFileListingMetadataHandler,
    FilenameParseResult,
    FilenameParser,
    MetadataComponentValueSet,
    MetadataHandler,
    MicroscopeImagePathParser,
)

logger = logging.getLogger(__name__)


class ImageXpressTimePointPaths(MicroscopeImagePathParser):
    """TimePoint folders independently own the acquisition time coordinate."""

    _timepoint_folder_pattern = re.compile(r"TimePoint[_-]?(\d+)", re.IGNORECASE)

    def image_path_components(
        self, path: Path
    ) -> tuple[tuple[AllComponents, int], ...]:
        return (
            *super().image_path_components(path),
            *self.indexed_folder_components(
                path,
                AllComponents.TIMEPOINT,
                self._timepoint_folder_pattern,
            ),
        )


class ImageXpressZStepPaths(MicroscopeImagePathParser):
    """ZStep folders independently own the acquisition depth coordinate."""

    _zstep_folder_pattern = re.compile(r"ZStep[_-]?(\d+)", re.IGNORECASE)

    def image_path_components(
        self, path: Path
    ) -> tuple[tuple[AllComponents, int], ...]:
        return (
            *super().image_path_components(path),
            *self.indexed_folder_components(
                path,
                AllComponents.Z_INDEX,
                self._zstep_folder_pattern,
            ),
        )


class ImageXpressHandler(
    ImageXpressTimePointPaths, ImageXpressZStepPaths, MicroscopeHandler
):
    """
    MicroscopeHandler implementation for Molecular Devices ImageXpress systems.

    This handler binds the ImageXpress filename parser and metadata handler,
    enforcing semantic alignment between file layout parsing and metadata resolution.
    """

    # Explicit microscope type for proper registration
    _microscope_type = Microscope.IMAGEXPRESS.value

    # Class attribute for automatic metadata handler registration (set after class definition)
    _metadata_handler_class = None

    @classmethod
    def supports_explicit_incomplete_export(cls) -> bool:
        """Native initialization requires the declared ImageXpress metadata file."""
        return False

    def __init__(self, filemanager: FileManager, pattern_format: Optional[str] = None):
        # Initialize parser with filemanager, respecting its interface
        self.parser = ImageXpressFilenameParser(filemanager, pattern_format)
        self.metadata_handler = ImageXpressMetadataHandler(filemanager)
        super().__init__(parser=self.parser, metadata_handler=self.metadata_handler)

    @property
    def root_dir(self) -> str:
        """
        Root directory for ImageXpress virtual workspace preparation.

        Returns "." (plate root) because ImageXpress TimePoint/ZStep folders
        are flattened starting from the plate root, and virtual paths have no prefix.
        """
        return "."

    @property
    def microscope_type(self) -> str:
        """Microscope type identifier (for interface enforcement only)."""
        return self._microscope_type

    @property
    def metadata_handler_class(self) -> Type[MetadataHandler]:
        """Metadata handler class (for interface enforcement only)."""
        return ImageXpressMetadataHandler

    @property
    def compatible_backends(self) -> List[Backend]:
        """
        ImageXpress is compatible with DISK backend only.

        Legacy microscope format with standard file operations.
        """
        return [Backend.DISK]

    # Uses default workspace initialization from base class

    def _build_virtual_mapping(
        self, plate_path: Path, filemanager: FileManager
    ) -> Path:
        """
        Build ImageXpress virtual workspace mapping using plate-relative paths.

        Flattens TimePoint and Z-step folder structures virtually by building a mapping dict.

        Args:
            plate_path: Path to plate directory
            filemanager: FileManager instance for file operations

        Returns:
            Path to image directory
        """
        plate_path = Path(plate_path)  # Ensure Path object

        logger.info(
            f"🔄 BUILDING VIRTUAL MAPPING: ImageXpress folder flattening for {plate_path}"
        )

        workspace_mapping = self.acquisition_workspace_mapping(
            self.metadata_handler.get_image_files(plate_path, all_subdirs=True),
            backend=Backend.DISK.value,
        )

        logger.info(
            f"Built {len(workspace_mapping)} virtual path mappings for ImageXpress"
        )

        # Save virtual workspace mapping and all available metadata
        self.save_virtual_workspace_metadata(plate_path, workspace_mapping)

        # Return the image directory
        return plate_path


class ImageXpressFilenameParser(FilenameParser):
    """
    Parser for ImageXpress microscope filenames.

    Handles standard ImageXpress format filenames like:
    - A01_s001_w1.tif
    - A01_s1_w1_z1.tif
    """

    # Regular expression pattern for ImageXpress filenames
    # Supports: well, site, channel, z_index, timepoint
    # Also supports result files with suffixes like: A01_s001_w1_z001_t001_cell_counts_step7.json
    _pattern = re.compile(
        r"(?:.*?_)?([A-Z]\d+)(?:_s(\d+|\{[^\}]*\}))?(?:_w(\d+|\{[^\}]*\}))?(?:_z(\d+|\{[^\}]*\}))?(?:_t(\d+|\{[^\}]*\}))?(?:_.*?)?(\.\w+)?$"
    )

    def __init__(self, filemanager=None, pattern_format=None):
        """
        Initialize the parser.

        Args:
            filemanager: FileManager instance (not used, but required for interface compatibility)
            pattern_format: Optional pattern format (not used, but required for interface compatibility)
        """
        super().__init__()  # Initialize the generic parser interface

        # These parameters are not used by this parser, but are required for interface compatibility
        self.filemanager = filemanager
        self.pattern_format = pattern_format

    @classmethod
    def can_parse(cls, filename: str) -> bool:
        """
        Check if this parser can parse the given filename.

        Args:
            filename: Filename to check (str or VirtualPath)

        Returns:
            bool: True if this parser can parse the filename, False otherwise
        """
        # For strings and other objects, convert to string and get basename
        # Use Path.name instead of os.path.basename for string operations
        basename = Path(str(filename)).name

        # Check if the filename matches the ImageXpress pattern
        return bool(cls._pattern.match(basename))

    # This is a string operation that doesn't perform actual file I/O
    # but is needed for filename parsing during runtime.
    def parse_filename(self, filename: str) -> Optional[FilenameParseResult]:
        """
        Parse an ImageXpress filename to extract all components, including extension.

        Args:
            filename: Filename to parse (str or VirtualPath)

        Returns:
            dict or None: Dictionary with extracted components or None if parsing fails
        """

        basename = Path(str(filename)).name

        match = self._pattern.match(basename)

        if match:
            well, site_str, channel_str, z_str, t_str, ext = match.groups()

            # Missing MetaXpress site/z/timepoint tokens represent scalar axes.
            parse_comp = lambda s: None if not s or "{" in s else int(s)
            site = 1 if site_str is None else parse_comp(site_str)
            channel = parse_comp(channel_str)
            z_index = 1 if z_str is None else parse_comp(z_str)
            timepoint = 1 if t_str is None else parse_comp(t_str)

            # Use the parsed components in the result
            result = FilenameParseResult(
                (
                    (AllComponents.WELL, well),
                    (AllComponents.SITE, site),
                    (AllComponents.CHANNEL, channel),
                    (AllComponents.Z_INDEX, z_index),
                    (AllComponents.TIMEPOINT, timepoint),
                ),
                extension=ext if ext else ".tif",
            )

            return result
        else:
            logger.debug("Could not parse ImageXpress filename: %s", filename)
            return None

    def extract_component_coordinates(self, component_value: str) -> Tuple[str, str]:
        """
        Extract coordinates from component identifier (typically well).

        Args:
            component_value (str): Component identifier (e.g., 'A01', 'C04')

        Returns:
            Tuple[str, str]: (row, column) where row is like 'A', 'C' and column is like '01', '04'

        Raises:
            ValueError: If component format is invalid
        """
        if not component_value or len(component_value) < 2:
            raise ValueError(f"Invalid component format: {component_value}")

        # ImageXpress format: A01, B02, C04, etc.
        row = component_value[0]
        col = component_value[1:]

        if not row.isalpha() or not col.isdigit():
            raise ValueError(
                f"Invalid ImageXpress component format: {component_value}. Expected format like 'A01', 'C04'"
            )

        return row, col

    def construct_filename(
        self,
        components: FilenameParseResult,
        site_padding: int = 3,
        z_padding: int = 3,
        timepoint_padding: int = 3,
        *,
        plate_name: str | None = None,
        include_site: bool = True,
        include_channel: bool = True,
    ) -> str:
        """Construct an ImageXpress filename from nominal component values."""

        well = components.required_value(AllComponents.WELL)
        site = components.required_value(AllComponents.SITE)
        channel = components.required_value(AllComponents.CHANNEL)
        z_index = components.value_for(AllComponents.Z_INDEX)
        timepoint = components.value_for(AllComponents.TIMEPOINT)

        parts = [f"{plate_name}_{well}" if plate_name is not None else well]

        if include_site:
            parts.append(f"_s{format_filename_component(site, site_padding)}")

        if include_channel:
            parts.append(f"_w{format_filename_component(channel)}")

        if z_index is not None:
            parts.append(f"_z{format_filename_component(z_index, z_padding)}")

        if timepoint is not None:
            parts.append(f"_t{format_filename_component(timepoint, timepoint_padding)}")

        base_name = "".join(parts)
        return f"{base_name}{components.extension}"

    def construct_acquisition_filename(
        self,
        components: FilenameParseResult,
        *,
        include_all_components: bool = False,
        plate_name: str | None = None,
        include_site: bool = True,
        include_channel: bool = True,
    ) -> str:
        """Own MetaXpress acquisition spelling, including folder-only Z axes."""
        if not include_all_components or plate_name is not None:
            components = components.with_values(
                ((AllComponents.Z_INDEX, None), (AllComponents.TIMEPOINT, None))
            )
        return self.construct_filename(
            components,
            site_padding=0 if plate_name is not None else 3,
            plate_name=plate_name,
            include_site=include_site if plate_name is not None else True,
            include_channel=include_channel if plate_name is not None else True,
        )


class ImageXpressMetadataHandler(DiskImageFileListingMetadataHandler):
    """
    Metadata handler for ImageXpress microscopes.

    Handles finding and parsing HTD files for ImageXpress microscopes.
    Inherits fallback values from MetadataHandler ABC.
    """

    def __init__(self, filemanager: FileManager):
        """
        Initialize the metadata handler.

        Args:
            filemanager: FileManager instance for file operations.
        """
        super().__init__()  # Call parent's __init__ without parameters
        self.filemanager = filemanager  # Store filemanager as an instance attribute

    def _read_htd_content(
        self,
        plate_path: Union[str, Path],
    ) -> str:
        htd_file = self.find_metadata_file(plate_path)
        encodings_to_try = ("utf-8", "windows-1252", "latin-1", "cp1252", "iso-8859-1")

        for encoding in encodings_to_try:
            try:
                with open(htd_file, "r", encoding=encoding) as f:
                    return f.read()
            except UnicodeDecodeError:
                logger.debug("Failed to read HTD file with encoding: %s", encoding)

        raise ValueError(
            f"Could not read HTD file with any supported encoding: {encodings_to_try}"
        )

    def find_metadata_file(
        self,
        plate_path: Union[str, Path],
    ) -> Path:
        """
        Find the HTD file for an ImageXpress plate.

        Args:
            plate_path: Path to the plate folder
        Returns:
            Path to the HTD file

        Raises:
            MetadataNotFoundError: If no HTD file is found
            TypeError: If plate_path is not a valid path type
        """
        # Ensure plate_path is a Path object
        if isinstance(plate_path, str):
            plate_path = Path(plate_path)
        elif not isinstance(plate_path, Path):
            raise TypeError(f"Expected str or Path, got {type(plate_path).__name__}")

        # Ensure the path exists
        if not plate_path.exists():
            raise FileNotFoundError(f"Plate path does not exist: {plate_path}")

        # Use filemanager to list files
        # Pass the backend parameter as required by Clause 306 (Backend Positional Parameters)
        htd_files = self.filemanager.list_files(
            plate_path, Backend.DISK.value, pattern="*.HTD"
        )
        if htd_files:
            for htd_file in htd_files:
                # Convert to Path if it's a string
                if isinstance(htd_file, str):
                    htd_file = Path(htd_file)

                if "plate" in htd_file.name.lower():
                    return htd_file

            # Return the first file
            first_file = htd_files[0]
            if isinstance(first_file, str):
                return Path(first_file)
            return first_file

        # Fail loudly if no HTD file is found
        raise MetadataNotFoundError(
            "No HTD or metadata file found. ImageXpressHandler requires declared metadata."
        )

    def get_grid_dimensions(
        self,
        plate_path: Union[str, Path],
    ) -> Tuple[int, int]:
        """
        Get grid dimensions for stitching from HTD file.

        Args:
            plate_path: Path to the plate folder
        Returns:
            (grid_rows, grid_cols) - UPDATED: Now returns (rows, cols) for MIST compatibility

        Raises:
            MetadataNotFoundError: If no HTD file is found
            ValueError: If grid dimensions cannot be determined from metadata
        """
        try:
            htd_content = self._read_htd_content(plate_path)

            # Extract grid dimensions - try multiple formats
            # First try the new format with "XSites" and "YSites"
            cols_match = re.search(r'"XSites", (\d+)', htd_content)
            rows_match = re.search(r'"YSites", (\d+)', htd_content)

            # If not found, try the old format with SiteColumns and SiteRows
            if not (cols_match and rows_match):
                cols_match = re.search(r"SiteColumns=(\d+)", htd_content)
                rows_match = re.search(r"SiteRows=(\d+)", htd_content)

            if cols_match and rows_match:
                grid_size_x = int(cols_match.group(1))  # cols from metadata
                grid_size_y = int(rows_match.group(1))  # rows from metadata
                logger.info(
                    "Using grid dimensions from HTD file: %dx%d (cols x rows)",
                    grid_size_x,
                    grid_size_y,
                )
                # FIXED: Return (rows, cols) for MIST compatibility instead of (cols, rows)
                return grid_size_y, grid_size_x

            # Fail loudly if grid dimensions cannot be determined
            raise ValueError(
                f"Could not find grid dimensions in HTD metadata for {plate_path}"
            )
        except Exception as e:
            # Fail loudly on any error
            raise ValueError(
                f"Error parsing ImageXpress grid dimensions for {plate_path}: {e}"
            )

    def get_pixel_size(
        self,
        plate_path: Union[str, Path],
    ) -> float:
        """
        Get pixel size from ImageXpress HTD metadata.

        Args:
            plate_path: Path to the plate folder
        Returns:
            Pixel size in micrometers

        Raises:
            ValueError: If pixel size cannot be determined from metadata
        """
        htd_content = self._read_htd_content(plate_path)
        pixel_size_match = re.search(
            r'"(?:PixelSizeUM|PixelSizeMicrons|PixelSize)",\s*([0-9]+(?:\.[0-9]+)?)',
            htd_content,
        )
        if pixel_size_match:
            return float(pixel_size_match.group(1))

        raise ValueError(
            f"ImageXpress HTD metadata does not declare pixel size for {plate_path}"
        )

    def component_value_set(
        self,
        plate_path: Union[str, Path],
    ) -> MetadataComponentValueSet:
        """Return the channel labels declared by ImageXpress HTD metadata."""

        htd_content = self._read_htd_content(plate_path)
        channel_mapping: dict[str, str | None] = {}
        wave_pattern = re.compile(r'"WaveName(\d+)", "([^"]*)"')
        for wave_num, wave_name in wave_pattern.findall(htd_content):
            if wave_name:
                channel_mapping[wave_num] = wave_name
        return MetadataComponentValueSet.from_partial(
            ((AllComponents.CHANNEL, channel_mapping or None),)
        )


# Set metadata handler class after class definition for automatic registration
from openhcs.microscopes.microscope_base import register_metadata_handler

ImageXpressHandler._metadata_handler_class = ImageXpressMetadataHandler
register_metadata_handler(ImageXpressHandler, ImageXpressMetadataHandler)
