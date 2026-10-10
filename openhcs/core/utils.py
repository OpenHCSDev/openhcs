"""Well filter resolution shared by the compiler and materialization planning."""

import ast
import logging
from typing import List, Set, Union

from openhcs.core.config import WellFilterMode

logger = logging.getLogger(__name__)


class WellFilterProcessor:
    """Resolve well filter specifications against a plate's available wells."""

    COMMA_SEPARATOR = ","
    RANGE_SEPARATOR = ":"
    ROW_PREFIX = "row:"
    COL_PREFIX = "col:"

    @staticmethod
    def _well_identity_key(well: object) -> str:
        """Normalize a well identifier for matching without replacing its source identity."""
        return str(well).casefold()

    @staticmethod
    def resolve_filter_with_mode(
        well_filter: Union[List[str], str, int],
        well_filter_mode: WellFilterMode,
        available_wells: List[str],
    ) -> List[str]:
        """
        Resolve well filter to concrete well list, applying INCLUDE/EXCLUDE mode.

        This is the unified method that should be used everywhere WellFilterConfig is processed.
        It handles both the resolution of the filter pattern AND the application of the mode.

        Args:
            well_filter: Filter specification (list, string pattern, or max count)
            well_filter_mode: Whether to include or exclude the matched wells
            available_wells: Ordered list of wells from orchestrator.get_component_keys(MULTIPROCESSING_AXIS)

        Returns:
            List of well IDs to process (order preserved from available_wells)

        Raises:
            ValueError: If wells don't exist (INCLUDE mode only), insufficient wells for count, or invalid patterns
        """
        # First resolve the filter to a set of wells
        # Pass strict=False for EXCLUDE mode (ignore non-existent wells)
        resolved_wells = WellFilterProcessor.resolve_compilation_filter(
            well_filter,
            available_wells,
            strict=(well_filter_mode == WellFilterMode.INCLUDE),
        )

        logger.debug(
            f"resolve_filter_with_mode: well_filter={well_filter}, mode={well_filter_mode.value}, "
            f"available_wells={available_wells}, resolved_wells={resolved_wells}"
        )

        # Apply mode: INCLUDE = use resolved wells, EXCLUDE = use all except resolved wells
        resolved_identity_keys = {
            WellFilterProcessor._well_identity_key(well) for well in resolved_wells
        }
        if well_filter_mode == WellFilterMode.EXCLUDE:
            # Return all wells that are NOT in the resolved set, preserving order
            result = [
                w
                for w in available_wells
                if WellFilterProcessor._well_identity_key(w)
                not in resolved_identity_keys
            ]
            logger.debug(f"EXCLUDE mode: returning {result}")
            return result
        else:
            # Return resolved wells in the order they appear in available_wells
            result = [
                w
                for w in available_wells
                if WellFilterProcessor._well_identity_key(w) in resolved_identity_keys
            ]
            logger.debug(f"INCLUDE mode: returning {result}")
            return result

    @staticmethod
    def resolve_compilation_filter(
        well_filter: Union[List[str], str, int],
        available_wells: List[str],
        strict: bool = True,
    ) -> Set[str]:
        """
        Resolve well filter to concrete well set during compilation.

        NOTE: This method does NOT apply INCLUDE/EXCLUDE mode. Use resolve_filter_with_mode() instead
        for complete filter processing that respects well_filter_mode.

        Combines validation and resolution in single method to avoid verbose helper methods.
        Supports all existing filter types while providing compilation-time optimization.
        Works with any well naming format (A01, R01C03, etc.) by using available wells.

        Args:
            well_filter: Filter specification (list, string pattern, or max count)
            available_wells: Ordered list of wells from orchestrator.get_component_keys(MULTIPROCESSING_AXIS)
            strict: If True, raise error for non-existent wells. If False, silently ignore them.

        Returns:
            Set of well IDs that match the filter (mode NOT applied)

        Raises:
            ValueError: If wells don't exist (strict=True only), insufficient wells for count, or invalid patterns
        """
        if isinstance(well_filter, list):
            # Inline validation for specific wells
            available_set = set(available_wells)
            available_identity_keys = {
                WellFilterProcessor._well_identity_key(well) for well in available_wells
            }
            invalid_wells = [
                well
                for well in well_filter
                if WellFilterProcessor._well_identity_key(well)
                not in available_identity_keys
            ]

            if invalid_wells:
                if strict:
                    raise ValueError(
                        f"Invalid wells specified: {invalid_wells}. "
                        f"Available wells: {sorted(available_set)}"
                    )
                else:
                    # Non-strict mode: filter out invalid wells and continue
                    logger.warning(
                        f"Ignoring non-existent wells in filter: {invalid_wells}"
                    )

            # Return only valid wells
            requested_identity_keys = {
                WellFilterProcessor._well_identity_key(well)
                for well in well_filter
                if WellFilterProcessor._well_identity_key(well)
                in available_identity_keys
            }
            return {
                well
                for well in available_set
                if WellFilterProcessor._well_identity_key(well)
                in requested_identity_keys
            }

        elif isinstance(well_filter, int):
            # Inline validation for max count. Zero is the explicit empty
            # selection used by persistence policies that should emit no wells.
            if well_filter < 0:
                raise ValueError(f"Max count must be non-negative, got: {well_filter}")
            if well_filter == 0:
                return set()
            if well_filter > len(available_wells):
                raise ValueError(
                    f"Requested {well_filter} wells but only {len(available_wells)} available"
                )
            return set(available_wells[:well_filter])

        elif isinstance(well_filter, str):
            # Check if string is a Python list literal (common UI input issue)
            stripped = well_filter.strip()
            if stripped.startswith("[") and stripped.endswith("]"):
                # Parse as Python list literal
                try:
                    parsed = ast.literal_eval(stripped)
                    if isinstance(parsed, list):
                        # Recursively call with the parsed list, preserving strict mode
                        return WellFilterProcessor.resolve_compilation_filter(
                            parsed, available_wells, strict
                        )
                except (ValueError, SyntaxError):
                    # Not a valid Python literal, fall through to pattern parsing
                    pass

            # Check if string is a numeric value (common UI input issue)
            if stripped.isdigit():
                # Convert numeric string to integer and process as max count
                numeric_value = int(stripped)
                if numeric_value == 0:
                    return set()
                if numeric_value > len(available_wells):
                    raise ValueError(
                        f"Requested {numeric_value} wells but only {len(available_wells)} available"
                    )
                return set(available_wells[:numeric_value])

            else:
                # Non-numeric string - pass to pattern parsing for format-agnostic support
                return WellFilterProcessor._parse_well_pattern(
                    well_filter, available_wells
                )

        else:
            raise ValueError(f"Unsupported well filter type: {type(well_filter)}")

    @staticmethod
    def _parse_well_pattern(pattern: str, available_wells: List[str]) -> Set[str]:
        """Parse string well patterns into well ID sets using available wells."""
        pattern = pattern.strip()

        # Comma-separated list
        if WellFilterProcessor.COMMA_SEPARATOR in pattern:
            return set(
                w.strip() for w in pattern.split(WellFilterProcessor.COMMA_SEPARATOR)
            )

        # Row pattern: "row:A"
        if pattern.startswith(WellFilterProcessor.ROW_PREFIX):
            row = pattern[len(WellFilterProcessor.ROW_PREFIX) :].strip()
            return WellFilterProcessor._expand_row_pattern(row, available_wells)

        # Column pattern: "col:01-06"
        if pattern.startswith(WellFilterProcessor.COL_PREFIX):
            col_spec = pattern[len(WellFilterProcessor.COL_PREFIX) :].strip()
            return WellFilterProcessor._expand_col_pattern(col_spec, available_wells)

        # Range pattern: "A01:A12"
        if WellFilterProcessor.RANGE_SEPARATOR in pattern:
            return WellFilterProcessor._expand_range_pattern(pattern, available_wells)

        # Single well
        return {pattern}

    @staticmethod
    def _expand_row_pattern(row: str, available_wells: List[str]) -> Set[str]:
        """Expand row pattern using available wells (format-agnostic)."""
        # Direct prefix match (A01, B02, etc.)
        result = {well for well in available_wells if well.startswith(row)}

        # Opera Phenix format fallback (A → R01C*, B → R02C*)
        if not result and len(row) == 1 and row.isalpha():
            row_pattern = f"R{ord(row.upper()) - ord('A') + 1:02d}C"
            result = {well for well in available_wells if well.startswith(row_pattern)}

        return result

    @staticmethod
    def _expand_col_pattern(col_spec: str, available_wells: List[str]) -> Set[str]:
        """Expand column pattern using available wells (format-agnostic)."""
        # Parse column range
        if "-" in col_spec:
            start_col, end_col = map(int, col_spec.split("-"))
            col_range = set(range(start_col, end_col + 1))
        else:
            col_range = {int(col_spec)}

        # Extract numeric suffix and match (A01, B02, etc.)
        def get_numeric_suffix(well: str) -> int:
            digits = "".join(char for char in reversed(well) if char.isdigit())
            return int(digits[::-1]) if digits else 0

        result = {
            well for well in available_wells if get_numeric_suffix(well) in col_range
        }

        # Opera Phenix format fallback (C01, C02, etc.)
        if not result:
            patterns = {f"C{col:02d}" for col in col_range}
            result = {
                well
                for well in available_wells
                if any(pattern in well for pattern in patterns)
            }

        return result

    @staticmethod
    def _expand_range_pattern(pattern: str, available_wells: List[str]) -> Set[str]:
        """Expand range pattern using available wells (format-agnostic)."""
        start_well, end_well = map(
            str.strip, pattern.split(WellFilterProcessor.RANGE_SEPARATOR)
        )

        try:
            start_idx, end_idx = available_wells.index(
                start_well
            ), available_wells.index(end_well)
        except ValueError as e:
            raise ValueError(
                f"Range pattern '{pattern}' contains wells not in available wells: {e}"
            )

        # Ensure proper order and return range (inclusive)
        start_idx, end_idx = sorted([start_idx, end_idx])
        return set(available_wells[start_idx : end_idx + 1])
