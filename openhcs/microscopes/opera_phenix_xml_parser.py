"""
Opera Phenix XML parser for openhcs.

This module provides a class for parsing Opera Phenix Index.xml files.
"""

import logging
import re
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import Any, Dict, Optional, Tuple, Union

import numpy as np

logger = logging.getLogger(__name__)


class OperaPhenixXmlError(Exception):
    """Base exception for Opera Phenix XML parsing errors."""

    pass


class OperaPhenixXmlParseError(OperaPhenixXmlError):
    """Exception raised when parsing the XML file fails."""

    pass


class OperaPhenixXmlContentError(OperaPhenixXmlError):
    """Exception raised when the XML content is invalid or missing required elements."""

    pass


class OperaPhenixXmlParser:
    """Parser for Opera Phenix Index.xml files."""

    def __init__(self, xml_path: Union[str, Path]):
        """
        Initialize the parser with the path to the Index.xml file.

        Args:
            xml_path: Path to the Index.xml file (string or Path object)
        """
        # Convert to Path object for filesystem operations
        if isinstance(xml_path, str):
            self.xml_path = Path(xml_path)
        else:
            self.xml_path = xml_path

        # Ensure the path exists
        if not self.xml_path.exists():
            raise FileNotFoundError(f"XML file does not exist: {self.xml_path}")

        self.tree = None
        self.root = None
        self.namespace = ""
        self._parse_xml()

    def _parse_xml(self):
        """
        Parse the XML file and extract the namespace.

        Raises:
            FileNotFoundError: If the XML file doesn't exist
            PermissionError: If there's no permission to read the file
            OperaPhenixXmlParseError: If the XML is malformed or cannot be parsed
            TypeError: If the XML path is not a string or Path object
            AttributeError: If the XML structure is unexpected
            ValueError: If there are issues with the XML content
        """
        try:
            self.tree = ET.parse(self.xml_path)
            self.root = self.tree.getroot()

            # Extract namespace from the root tag
            match = re.match(r"{.*}", self.root.tag)
            self.namespace = match.group(0) if match else ""

            logger.info("Parsed Opera Phenix XML file: %s", self.xml_path)
            logger.debug("XML namespace: %s", self.namespace)
        except FileNotFoundError:
            logger.error("XML file not found: %s", self.xml_path)
            raise
        except PermissionError:
            logger.error("Permission denied when reading XML file: %s", self.xml_path)
            raise
        except ET.ParseError as e:
            logger.error("XML parse error in file %s: %s", self.xml_path, e)
            raise OperaPhenixXmlParseError(
                f"Failed to parse XML file {self.xml_path}: {e}"
            )
        except re.error as e:
            logger.error(
                "Regex error when extracting namespace from %s: %s", self.xml_path, e
            )
            raise OperaPhenixXmlParseError(
                f"Failed to extract namespace from XML file {self.xml_path}: {e}"
            )
        except TypeError as e:
            logger.error("Type error when parsing XML file %s: %s", self.xml_path, e)
            raise TypeError(f"Invalid type for XML path: {e}")
        except AttributeError as e:
            logger.error(
                "Attribute error when parsing XML file %s: %s", self.xml_path, e
            )
            raise OperaPhenixXmlParseError(
                f"Unexpected XML structure in file {self.xml_path}: {e}"
            )
        except ValueError as e:
            logger.error("Value error when parsing XML file %s: %s", self.xml_path, e)
            raise OperaPhenixXmlParseError(
                f"Invalid value in XML file {self.xml_path}: {e}"
            )

    def get_plate_info(self) -> Dict[str, Any]:
        """
        Extract plate information from the XML.

        Returns:
            Dict containing plate information

        Raises:
            OperaPhenixXmlParseError: If XML is not parsed
            OperaPhenixXmlContentError: If Plate element is missing or required elements are missing
        """
        if self.root is None:
            raise OperaPhenixXmlParseError(
                "XML not parsed, cannot retrieve plate information"
            )

        plate_elem = self.root.find(f".//{self.namespace}Plate")
        if plate_elem is None:
            raise OperaPhenixXmlContentError("No Plate element found in XML")

        plate_rows_text = self._get_element_text(plate_elem, "PlateRows")
        plate_columns_text = self._get_element_text(plate_elem, "PlateColumns")

        if plate_rows_text is None:
            raise OperaPhenixXmlContentError(
                "PlateRows element missing or empty in XML"
            )
        if plate_columns_text is None:
            raise OperaPhenixXmlContentError(
                "PlateColumns element missing or empty in XML"
            )

        plate_info = {
            "plate_id": self._get_element_text(plate_elem, "PlateID"),
            "measurement_id": self._get_element_text(plate_elem, "MeasurementID"),
            "plate_type": self._get_element_text(plate_elem, "PlateTypeName"),
            "rows": int(plate_rows_text),
            "columns": int(plate_columns_text),
        }

        # Get well IDs
        well_elems = plate_elem.findall(f"{self.namespace}Well")
        plate_info["wells"] = [well.get("id") for well in well_elems if well.get("id")]

        logger.debug("Plate info: %s", plate_info)
        return plate_info

    def get_grid_size(self) -> Tuple[int, int]:
        """
        Determine the grid size (number of fields per well) by analyzing image positions.

        This method analyzes the positions of images for a single well, channel, and plane
        to determine the grid dimensions.

        Returns:
            Tuple of (grid_size_x, grid_size_y) - NOTE: Still returns (cols, rows) format
            The calling handler will swap this to (rows, cols) for MIST compatibility

        Raises:
            OperaPhenixXmlParseError: If XML is not parsed
            OperaPhenixXmlContentError: If no Image elements are found or grid size cannot be determined
        """
        if self.root is None:
            raise OperaPhenixXmlParseError("XML not parsed, cannot determine grid size")

        # Get all image elements
        image_elements = self.root.findall(f".//{self.namespace}Image")

        if not image_elements:
            raise OperaPhenixXmlContentError("No Image elements found in XML")

        # Keep coordinate populations separate, including colocated channels.
        image_groups: dict[tuple[int, ...], list[tuple[float, float]]] = {}

        for image in image_elements:
            try:
                group_key = tuple(
                    int(self._get_element_text(image, tag))
                    for tag in ("Row", "Col", "ChannelID", "PlaneID")
                )
            except (ValueError, TypeError):
                continue
            field_position = self._get_field_position(image)
            if field_position is not None:
                _, position = field_position
                image_groups.setdefault(group_key, []).append(position)

        if not image_groups:
            raise OperaPhenixXmlContentError("Could not determine grid size from XML data")

        # Preserve the first multi-image group's precedence on partial exports;
        # an acquisition consisting solely of singleton groups is also geometry.
        groups = tuple(image_groups.values())
        positions = next((group for group in groups if len(group) > 1), groups[0])
        x_positions, y_positions = zip(*positions)
        epsilon = 1e-10
        columns = len(np.unique(np.round(np.array(x_positions) / epsilon) * epsilon))
        rows = len(np.unique(np.round(np.array(y_positions) / epsilon) * epsilon))
        logger.info("Determined grid size from positions: %dx%d", columns, rows)
        return (columns, rows)

    def get_pixel_size(self) -> float:
        """
        Extract pixel size from the XML.

        The pixel size is stored in ImageResolutionX/Y elements with Unit="m".

        Returns:
            Pixel size in micrometers (μm)

        Raises:
            OperaPhenixXmlParseError: If XML is not parsed
            OperaPhenixXmlContentError: If pixel size cannot be determined or parsed
        """
        if self.root is None:
            raise OperaPhenixXmlParseError(
                "XML not parsed, cannot determine pixel size"
            )

        # Try to find ImageResolutionX element
        resolution_x = self.root.find(f".//{self.namespace}ImageResolutionX")
        if resolution_x is not None and resolution_x.text:
            try:
                # Convert from meters to micrometers
                pixel_size = float(resolution_x.text) * 1e6
                logger.info(
                    "Found pixel size from ImageResolutionX: %.4f μm", pixel_size
                )
                return pixel_size
            except ValueError as e:
                logger.warning(
                    "Could not parse pixel size from ImageResolutionX (invalid number format): %s",
                    e,
                )
                # Continue to try ImageResolutionY
            except TypeError as e:
                logger.warning(
                    "Could not parse pixel size from ImageResolutionX (wrong type): %s",
                    e,
                )
                # Continue to try ImageResolutionY

        # If not found in ImageResolutionX, try ImageResolutionY
        resolution_y = self.root.find(f".//{self.namespace}ImageResolutionY")
        if resolution_y is not None and resolution_y.text:
            try:
                # Convert from meters to micrometers
                pixel_size = float(resolution_y.text) * 1e6
                logger.info(
                    "Found pixel size from ImageResolutionY: %.4f μm", pixel_size
                )
                return pixel_size
            except ValueError as e:
                logger.warning(
                    "Could not parse pixel size from ImageResolutionY (invalid number format): %s",
                    e,
                )
                # Fall through to the error case
            except TypeError as e:
                logger.warning(
                    "Could not parse pixel size from ImageResolutionY (wrong type): %s",
                    e,
                )
                # Fall through to the error case

        # If not found, raise an error
        raise OperaPhenixXmlContentError(
            "Pixel size not found or could not be parsed in XML"
        )

    def get_image_info(self) -> Dict[str, Dict[str, Any]]:
        """
        Extract image information from the XML.

        Returns:
            Dictionary mapping image IDs to dictionaries containing image information

        Raises:
            OperaPhenixXmlParseError: If XML is not parsed
            OperaPhenixXmlContentError: If no Image elements are found or required elements are missing
        """
        if self.root is None:
            raise OperaPhenixXmlParseError(
                "XML not parsed, cannot retrieve image information"
            )

        # Look for Image elements
        image_elems = self.root.findall(f".//{self.namespace}Image[@Version]")
        if not image_elems:
            raise OperaPhenixXmlContentError(
                "No Image elements with Version attribute found in XML"
            )

        image_info = {}
        for image in image_elems:
            image_id = self._get_element_text(image, "id")
            if image_id:
                row_text = self._get_element_text(image, "Row")
                col_text = self._get_element_text(image, "Col")
                field_id_text = self._get_element_text(image, "FieldID")
                plane_id_text = self._get_element_text(image, "PlaneID")
                channel_id_text = self._get_element_text(image, "ChannelID")

                # Validate required fields
                if row_text is None:
                    raise OperaPhenixXmlContentError(
                        f"Row element missing or empty for image {image_id}"
                    )
                if col_text is None:
                    raise OperaPhenixXmlContentError(
                        f"Col element missing or empty for image {image_id}"
                    )
                if field_id_text is None:
                    raise OperaPhenixXmlContentError(
                        f"FieldID element missing or empty for image {image_id}"
                    )
                if plane_id_text is None:
                    raise OperaPhenixXmlContentError(
                        f"PlaneID element missing or empty for image {image_id}"
                    )
                if channel_id_text is None:
                    raise OperaPhenixXmlContentError(
                        f"ChannelID element missing or empty for image {image_id}"
                    )

                image_data = {
                    "url": self._get_element_text(image, "URL"),
                    "row": int(row_text),
                    "col": int(col_text),
                    "field_id": int(field_id_text),
                    "plane_id": int(plane_id_text),
                    "channel_id": int(channel_id_text),
                    "position_x": self._get_element_text(image, "PositionX"),
                    "position_y": self._get_element_text(image, "PositionY"),
                    "position_z": self._get_element_text(image, "PositionZ"),
                }
                image_info[image_id] = image_data

        logger.debug("Found %d images in XML", len(image_info))
        return image_info

    def get_well_positions(self) -> Dict[str, Tuple[int, int]]:
        """
        Extract well positions from the XML.

        Returns:
            Dictionary mapping well IDs to (row, column) tuples

        Raises:
            OperaPhenixXmlParseError: If XML is not parsed
            OperaPhenixXmlContentError: If no Well elements are found
        """
        if self.root is None:
            raise OperaPhenixXmlParseError(
                "XML not parsed, cannot retrieve well positions"
            )

        # Look for Well elements
        well_elems = self.root.findall(f".//{self.namespace}Wells/{self.namespace}Well")
        if not well_elems:
            raise OperaPhenixXmlContentError("No Well elements found in XML")

        well_positions = {}
        for well in well_elems:
            well_id = self._get_element_text(well, "id")
            row = self._get_element_text(well, "Row")
            col = self._get_element_text(well, "Col")

            if well_id and row and col:
                well_positions[well_id] = (int(row), int(col))

        logger.debug("Well positions: %s", well_positions)
        return well_positions

    def _get_element_text(self, parent_elem, tag_name: str) -> Optional[str]:
        """Helper method to get element text with namespace."""
        elem = parent_elem.find(f"{self.namespace}{tag_name}")
        return elem.text if elem is not None else None

    def _get_element_attribute(
        self, parent_elem, tag_name: str, attr_name: str
    ) -> Optional[str]:
        """Helper method to get element attribute with namespace."""
        elem = parent_elem.find(f"{self.namespace}{tag_name}")
        return elem.get(attr_name) if elem is not None else None

    def _get_field_position(
        self, image: ET.Element
    ) -> Optional[Tuple[int, Tuple[float, float]]]:
        """Decode one finite Harmony stage position for grid and remapping readers."""
        try:
            field_id = int(self._get_element_text(image, "FieldID"))
            position = (
                float(self._get_element_text(image, "PositionX")),
                float(self._get_element_text(image, "PositionY")),
            )
        except (ValueError, TypeError) as error:
            logger.debug("Skipping field with invalid position data: %s", error)
            return None
        if not np.isfinite(position).all():
            logger.debug("Skipping field %d with nonfinite position: %s", field_id, position)
            return None
        return field_id, position

    def detect_orphan_fields(
        self,
        positions: Dict[int, Tuple[float, float]],
        distance_threshold_multiplier: float = 3.0,
    ) -> set:
        """
        Detect orphan fields that are significantly far from the main grid.

        An orphan field is one whose distance to its nearest neighbor is much larger
        than the typical spacing between fields in the grid.

        Args:
            positions: Dictionary mapping field IDs to (x, y) position tuples
            distance_threshold_multiplier: How many times the median spacing to consider orphan

        Returns:
            set: Set of field IDs that are orphans
        """
        if len(positions) < 3:
            return set()  # Need at least 3 fields to detect orphans

        import numpy as np

        # Calculate distance from each field to its nearest neighbor
        field_ids = list(positions.keys())
        nearest_distances = {}

        for field_id in field_ids:
            x1, y1 = positions[field_id]
            min_dist = float("inf")

            for other_id in field_ids:
                if other_id == field_id:
                    continue
                x2, y2 = positions[other_id]
                dist = np.sqrt((x2 - x1) ** 2 + (y2 - y1) ** 2)
                min_dist = min(min_dist, dist)

            nearest_distances[field_id] = min_dist

        # Calculate median nearest-neighbor distance
        distances = list(nearest_distances.values())
        median_distance = np.median(distances)

        # Fields with nearest-neighbor distance > threshold are orphans
        threshold = median_distance * distance_threshold_multiplier
        orphans = {fid for fid, dist in nearest_distances.items() if dist > threshold}

        if orphans:
            logger.warning(
                f"Detected {len(orphans)} orphan field(s): {sorted(orphans)}"
            )
            logger.warning(
                f"Median field spacing: {median_distance:.6f}, threshold: {threshold:.6f}"
            )
            for fid in sorted(orphans):
                logger.warning(
                    f"  Field {fid}: nearest neighbor distance = {nearest_distances[fid]:.6f}"
                )

        return orphans

    def get_field_positions(
        self, exclude_orphans: bool = False
    ) -> Dict[int, Tuple[float, float]]:
        """
        Extract field IDs and their X,Y positions from the Index.xml file.

        Args:
            exclude_orphans: If True, exclude fields that are far from the main grid

        Returns:
            dict: Mapping of field IDs to (x, y) position tuples

        Raises:
            OperaPhenixXmlParseError: If XML is not parsed
        """
        if self.root is None:
            raise OperaPhenixXmlParseError(
                "XML not parsed, cannot extract field positions"
            )

        field_positions = {}

        # Find all Image elements
        image_elems = self.root.findall(f".//{self.namespace}Image")

        for image in image_elems:
            field_position = self._get_field_position(image)
            if field_position is not None:
                field_id, position = field_position
                field_positions.setdefault(field_id, position)

        # Detect and exclude orphan fields if requested
        if exclude_orphans and len(field_positions) > 2:
            orphans = self.detect_orphan_fields(field_positions)
            if orphans:
                logger.info(
                    f"Excluding {len(orphans)} orphan field(s) from mapping: {sorted(orphans)}"
                )
                field_positions = {
                    fid: pos
                    for fid, pos in field_positions.items()
                    if fid not in orphans
                }

        return field_positions

    def sort_fields_by_position(
        self, positions: Dict[int, Tuple[float, float]]
    ) -> list:
        """
        Sort fields based on their positions in a raster pattern starting from the top.
        All rows go left-to-right in a consistent raster scan pattern.

        Args:
            positions: Dictionary mapping field IDs to (x, y) position tuples

        Returns:
            list: Field IDs sorted in raster pattern order starting from the top
        """
        if not positions:
            return []

        # Get all unique x and y coordinates
        x_coords = sorted(set(pos[0] for pos in positions.values()))
        y_coords = sorted(
            set(pos[1] for pos in positions.values()), reverse=True
        )  # Reverse to get top row first

        # Create a grid of field IDs
        grid = {}
        for field_id, (x, y) in positions.items():
            # Find the closest x and y coordinates in our sorted lists
            x_idx = x_coords.index(x)
            y_idx = y_coords.index(y)  # This will now map top row to index 0
            grid[(x_idx, y_idx)] = field_id

        # Debug output to help diagnose field mapping issues
        logger.info("Field position grid:")
        for y_idx in range(len(y_coords)):
            row_str = ""
            for x_idx in range(len(x_coords)):
                field_id = grid.get((x_idx, y_idx), 0)
                row_str += f"{field_id:3d} "
            logger.info(row_str)

        # Sort field IDs by row (y) then column (x)
        # Use raster pattern: all rows go left-to-right in a consistent pattern
        sorted_field_ids = []
        for y_idx in range(len(y_coords)):
            row_fields = []
            # All rows go left to right in a raster pattern
            x_range = range(len(x_coords))

            for x_idx in x_range:
                if (x_idx, y_idx) in grid:
                    row_fields.append(grid[(x_idx, y_idx)])
            sorted_field_ids.extend(row_fields)

        return sorted_field_ids

    def get_field_id_mapping(self, exclude_orphans: bool = True) -> Dict[int, int]:
        """
        Generate a mapping from original field IDs to new field IDs based on position data.

        Args:
            exclude_orphans: If True, exclude orphan fields from the mapping

        Returns:
            dict: Mapping of original field IDs to new field IDs
        """
        # Get field positions (excluding orphans if requested)
        field_positions = self.get_field_positions(exclude_orphans=exclude_orphans)

        # Sort fields by position
        sorted_field_ids = self.sort_fields_by_position(field_positions)

        # Create mapping from original to new field IDs
        return {field_id: i + 1 for i, field_id in enumerate(sorted_field_ids)}

    def remap_field_id(
        self, field_id: int, mapping: Optional[Dict[int, int]] = None
    ) -> int:
        """
        Remap a field ID using the position-based mapping.

        Args:
            field_id: Original field ID
            mapping: Mapping to use. If None, generates a new mapping.

        Returns:
            int: New field ID

        Raises:
            OperaPhenixXmlContentError: If field_id is not found in the mapping
        """
        if mapping is None:
            mapping = self.get_field_id_mapping()

        if field_id not in mapping:
            raise OperaPhenixXmlContentError(
                f"Field ID {field_id} not found in remapping dictionary"
            )
        return mapping[field_id]
