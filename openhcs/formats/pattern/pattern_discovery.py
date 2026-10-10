"""
Pattern discovery engine for OpenHCS.

This module provides a dedicated engine for discovering and grouping patterns
in microscopy image files, separating this responsibility from FilenameParser.
"""

# Standard Library
import logging
import os
from collections import defaultdict
from pathlib import Path
from collections.abc import Sequence
from typing import Any, Dict, List, Optional, Union

from polystore.filemanager import FileManager

from openhcs.core.axes import Axis, AxisFamily, GroupingDeclaration
from openhcs.core.components.parser_metaprogramming import FilenameParseResult
from openhcs.core.runtime_pattern_cache import RuntimePatternDiscoveryCache

# Core OpenHCS Interfaces
from openhcs.core.dataset_sources.interfaces import FilenameParser

# Note: Previously used GenericPatternEngine, but now we always use microscope-specific parsers

logger = logging.getLogger(__name__)


# Pattern utility functions
def has_placeholders(pattern: str) -> bool:
    """Check if pattern contains placeholder variables."""
    return "{" in pattern and "}" in pattern


class PatternDiscoveryEngine:
    """
    Engine for discovering and grouping patterns in microscopy image files.

    This class is responsible for:
    - Finding image files in directories
    - Filtering files based on well IDs
    - Generating patterns from files
    - Grouping patterns by components

    It works with a FilenameParser to parse individual filenames and a
    FileManager to access the file system.
    """

    # Constants
    PLACEHOLDER_PATTERN = "{iii}"

    def __init__(
        self,
        parser: FilenameParser,
        filemanager: FileManager,
        pattern_cache: RuntimePatternDiscoveryCache | None = None,
    ):
        """Initialize the pattern discovery engine."""
        self.parser = parser
        self.filemanager = filemanager
        self.pattern_cache = (
            RuntimePatternDiscoveryCache() if pattern_cache is None else pattern_cache
        )

    def path_list_from_pattern(
        self,
        directory: Union[str, Path],
        pattern: str,
        backend: str,
        variable_components: Optional[Sequence[type[Axis]]] = None,
    ) -> List[str]:
        """Get a list of filenames matching a pattern in a directory."""
        variable_axes = tuple(
            AxisFamily.active().require(component)
            for component in variable_components or ()
        )
        directory_path = str(directory)  # Keep as string for FileManager consistency
        if not self.filemanager.is_dir(directory_path, backend):
            raise FileNotFoundError(f"Directory not found: {directory_path}")

        pattern_str = str(pattern)

        # Handle literal filenames (patterns without placeholders)
        if not has_placeholders(pattern_str):
            # Use FileManager to check if file exists
            file_path = os.path.join(
                directory_path, pattern_str
            )  # Use os.path.join instead of /
            file_exists = self.filemanager.exists(file_path, backend)
            if file_exists:
                self.pattern_cache.metadata_for_filename(self.parser, pattern_str)
                return [pattern_str]
            return []

        # Handle pattern strings with placeholders
        logger.debug("Using pattern template: %s", pattern_str)

        # Parse pattern template to get expected structure
        pattern_metadata = self.pattern_cache.metadata_for_filename(self.parser, pattern_str)
        if not pattern_metadata:
            logger.error("Failed to parse pattern template: %s", pattern_str)
            return []

        # Get all image files in directory using FileManager
        all_files = self.filemanager.list_image_files(str(directory_path), backend)

        matching_files = []

        for file_path in all_files:
            # Extract filename from path
            if isinstance(file_path, str):
                filename = os.path.basename(file_path)
            elif isinstance(file_path, Path):
                filename = file_path.name
            else:
                continue

            # Parse the actual filename
            file_metadata = self.pattern_cache.metadata_for_filename(self.parser, filename)
            if not file_metadata:
                continue

            # Check if file matches pattern structure
            if self._matches_pattern_structure(
                file_metadata, pattern_metadata, variable_axes
            ):
                matching_files.append(filename)

        return matching_files

    def _matches_pattern_structure(
        self,
        file_metadata: FilenameParseResult,
        pattern_metadata: FilenameParseResult,
        variable_components: Sequence[type[Axis]],
    ) -> bool:
        """Check if a file's metadata matches a pattern's structure."""
        # Check all components in the pattern
        variable_declarations = set(variable_components)
        for component in self.parser.FILENAME_COMPONENTS:
            pattern_value = pattern_metadata.value_for(component)
            file_value = file_metadata.value_for(component)

            # Variable components can have any value
            if component in variable_declarations:
                # File must have a value for this component, but it can be anything
                if file_value is None:
                    return False
                continue

            # Fixed components must match exactly
            if pattern_value != file_value:
                return False

        return True

    def group_patterns_by_component(
        self, patterns: List[str], component: type[Axis]
    ) -> Dict[str, List[str]]:
        """
        Group patterns by a required component.

        Args:
            patterns: List of pattern strings to group
            component: Component to group by

        Returns:
            Dictionary mapping component values to lists of patterns

        Raises:
            TypeError: If patterns are not strings
            ValueError: If component is not present in a pattern
        """
        grouped_patterns = defaultdict(list)
        component_declaration = AxisFamily.active().require(component)

        if not all(isinstance(p, str) for p in patterns):
            raise TypeError("All patterns must be strings")

        for pattern in patterns:
            pattern_str = str(pattern)

            # Note: Patterns with template fields (like {iii}) are EXPECTED for pattern discovery
            # The has_placeholders() check is only relevant when using patterns as concrete filenames
            # For pattern discovery and grouping, we WANT patterns with placeholders

            metadata = self.pattern_cache.metadata_for_filename(self.parser, pattern_str)

            if metadata is None or metadata.value_for(component_declaration) is None:
                raise ValueError(
                    f"Missing required component '{component.name}' in pattern: "
                    f"{pattern_str}"
                )

            value = str(metadata.value_for(component_declaration))
            grouped_patterns[value].append(pattern)

        return grouped_patterns

    def subdivide_patterns_by_components(
        self, patterns: List[str], components: Sequence[type[Axis]]
    ) -> Dict[tuple, List[str]]:
        """Subdivide patterns by multiple component values."""
        if not components:
            return {(): patterns}

        subdivided = defaultdict(list)
        component_declarations = tuple(components)
        for pattern in patterns:
            metadata = self.pattern_cache.metadata_for_filename(self.parser, str(pattern))
            if not metadata:
                raise ValueError(f"Failed to parse pattern: {pattern}")
            key = tuple(
                str(value)
                for component in component_declarations
                for value in (metadata.value_for(component),)
                if value is not None
            )
            subdivided[key].append(pattern)
        return dict(subdivided)

    def auto_detect_patterns(
        self,
        folder_path: Union[str, Path],
        variable_components: Sequence[type[Axis]],
        backend: str,
        extensions: List[str] = None,
        group_by: type[GroupingDeclaration] | None = None,
        recursive: bool = False,
        **kwargs,  # Dynamic filter parameters (e.g., well_filter, site_filter)
    ) -> Dict[str, Any]:
        """
        Automatically detect image patterns in a folder.
        """
        axis_name = AxisFamily.active().partition_axis().name
        axis_filter = kwargs.get(f"{axis_name}_filter")

        files_by_axis = self._find_and_filter_images(
            folder_path, axis_filter, extensions, recursive, backend
        )

        if not files_by_axis:
            return {}

        return self._patterns_for_files_by_axis(
            files_by_axis,
            variable_components,
            group_by,
        )

    def auto_detect_patterns_from_files(
        self,
        image_paths: List[Union[str, Path]],
        variable_components: Sequence[type[Axis]],
        group_by: type[GroupingDeclaration] | None = None,
        **kwargs,
    ) -> Dict[str, Any]:
        """Automatically detect image patterns from an authoritative file list."""

        axis_name = AxisFamily.active().partition_axis().name
        axis_filter = kwargs.get(f"{axis_name}_filter")
        files_by_axis = self._filter_images_by_axis(image_paths, axis_filter)
        if not files_by_axis:
            return {}
        return self._patterns_for_files_by_axis(
            files_by_axis,
            variable_components,
            group_by,
        )

    def auto_detect_patterns_from_axis_files(
        self,
        image_paths: List[Union[str, Path]],
        *,
        axis_id: str,
        variable_components: Sequence[type[Axis]],
        group_by: type[GroupingDeclaration] | None = None,
    ) -> Dict[str, Any]:
        """Detect patterns from files already selected for one runtime axis."""
        if not axis_id:
            raise ValueError("axis_id cannot be empty")
        if not image_paths:
            return {}
        return self._patterns_for_files_by_axis(
            {axis_id: list(image_paths)},
            variable_components,
            group_by,
        )

    def _patterns_for_files_by_axis(
        self,
        files_by_axis: Dict[str, List[Any]],
        variable_components: Sequence[type[Axis]],
        group_by: type[GroupingDeclaration] | None = None,
    ) -> Dict[str, Any]:
        result = {}
        for axis_value, files in files_by_axis.items():
            patterns = self._generate_patterns_for_files(
                files, variable_components, axis_value
            )

            # Validate patterns
            for pattern in patterns:
                if not isinstance(pattern, str):
                    raise TypeError(
                        f"Pattern generator returned invalid type: {type(pattern).__name__}"
                    )

            grouping_axes = () if group_by is None else group_by.grouping_axes()
            if grouping_axes:
                (grouping_axis,) = grouping_axes
                result[axis_value] = self.group_patterns_by_component(
                    patterns, component=grouping_axis
                )
            else:
                result[axis_value] = patterns

        return result

    def _find_and_filter_images(
        self,
        folder_path: Union[str, Path],
        axis_filter: List[str],
        extensions: List[str],
        recursive: bool,
        backend: str,
    ) -> Dict[str, List[Any]]:
        """
        Find all image files in a directory and filter by multiprocessing axis.

        Args:
            folder_path: Path to the folder to search (string or Path object)
            axis_filter: List of axis values to include
            extensions: List of file extensions to include
            recursive: Whether to search recursively
            backend: Backend to use for file operations (required)

        Returns:
            Dictionary mapping axis values to lists of image paths

        Raises:
            TypeError: If folder_path is not a string or Path object
            ValueError: If axis_filter is empty or folder_path does not exist
        """
        # Convert to Path and validate using FileManager abstraction
        folder_path = Path(folder_path)
        if not self.filemanager.exists(str(folder_path), backend):
            raise FileNotFoundError(f"Folder not found: {folder_path}")

        # Validate inputs
        if not axis_filter:
            raise ValueError("axis_filter cannot be empty")

        extensions = extensions or [".tif", ".TIF", ".tiff", ".TIFF"]

        image_paths = self.filemanager.list_image_files(
            folder_path, backend, extensions=extensions, recursive=recursive
        )
        return self._filter_images_by_axis(image_paths, axis_filter)

    def _filter_images_by_axis(
        self,
        image_paths: List[Any],
        axis_filter: List[str],
    ) -> Dict[str, List[Any]]:
        if not axis_filter:
            raise ValueError("axis_filter cannot be empty")

        files_by_axis = defaultdict(list)
        for img_path in image_paths:
            # FileManager should return strings, but handle Path objects too
            if isinstance(img_path, str):
                filename = os.path.basename(img_path)
            elif isinstance(img_path, Path):
                filename = img_path.name
            else:
                # Skip any unexpected types
                logger.warning(f"Unexpected file path type: {type(img_path).__name__}")
                continue

            metadata = self.pattern_cache.metadata_for_filename(self.parser, filename)
            if not metadata:
                continue

            partition_axis = AxisFamily.active().partition_axis()
            matched_axis = next(
                (
                    str(axis_value)
                    for axis_value in axis_filter
                    if metadata.component_matches(partition_axis, axis_value)
                ),
                None,
            )
            if matched_axis is None:
                continue

            files_by_axis[matched_axis].append(img_path)

        return files_by_axis

    def _generate_patterns_for_files(
        self,
        files: List[Any],
        variable_components: Sequence[type[Axis]],
        axis_value: str,
    ) -> List[str]:
        """Generate patterns for a list of files."""
        # Validate input parameters
        if not isinstance(files, list):
            raise TypeError(
                f"Expected list of file path objects, got {type(files).__name__}"
            )

        variable_declarations = {
            AxisFamily.active().require(component) for component in variable_components
        }

        # Use microscope-specific parser for pattern generation

        component_combinations = defaultdict(list)
        for file_path in files:
            # FileManager should return strings, but handle Path objects too
            if isinstance(file_path, str):
                filename = os.path.basename(file_path)
            elif isinstance(file_path, Path):
                filename = file_path.name
            else:
                # Skip any unexpected types
                logger.warning(f"Unexpected file path type: {type(file_path).__name__}")
                continue

            metadata = self.pattern_cache.metadata_for_filename(self.parser, filename)
            if not metadata:
                continue

            key_parts = []
            for component in self.parser.FILENAME_COMPONENTS:
                value = metadata.value_for(component)
                if component not in variable_declarations and value is not None:
                    key_parts.append(f"{component.name}={value}")

            key = ",".join(key_parts)
            component_combinations[key].append((file_path, metadata))

        patterns = []
        for _, files_metadata in component_combinations.items():
            if not files_metadata:
                continue

            _, template_metadata = files_metadata[0]
            # Generate pattern arguments for all discovered components
            pattern_str = self.parser.construct_filename(
                template_metadata.with_values(
                    (
                        (component, self.PLACEHOLDER_PATTERN)
                        for component in variable_declarations
                    )
                )
            )

            # Validate that the pattern can be instantiated
            if not self.pattern_cache.metadata_for_filename(self.parser, pattern_str):
                raise ValueError(
                    f"Clause 93 Violation: Pattern template '{pattern_str}' cannot be instantiated"
                )

            patterns.append(pattern_str)

        # Validate the final pattern list
        if not patterns:
            raise ValueError(
                "No patterns generated from files. This indicates either: "
                "(1) no image files found in the directory, "
                "(2) files don't match the expected naming convention, or "
                "(3) pattern generation logic failed. "
                "Check that image files exist and follow the expected naming pattern."
            )

        return patterns
