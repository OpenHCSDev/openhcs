"""Partition filter resolution shared by the compiler and materialization planning."""

import ast
import logging
from typing import List, Set, Union

from openhcs.core.config import PartitionFilterMode

logger = logging.getLogger(__name__)


class PartitionFilterProcessor:
    """Resolve partition filter specifications against the available partition values."""

    COMMA_SEPARATOR = ","
    RANGE_SEPARATOR = ":"
    ROW_PREFIX = "row:"
    COL_PREFIX = "col:"

    @staticmethod
    def _identity_key(value: object) -> str:
        """Normalize a partition value for matching without replacing its source identity."""
        return str(value).casefold()

    @staticmethod
    def resolve_filter_with_mode(
        partition_filter: Union[List[str], str, int],
        partition_filter_mode: PartitionFilterMode,
        available_values: List[str],
    ) -> List[str]:
        """
        Resolve partition filter to concrete value list, applying INCLUDE/EXCLUDE mode.

        This is the unified method that should be used everywhere PartitionFilterConfig is processed.
        It handles both the resolution of the filter pattern AND the application of the mode.

        Args:
            partition_filter: Filter specification (list, string pattern, or max count)
            partition_filter_mode: Whether to include or exclude the matched values
            available_values: Ordered list of values from orchestrator.get_component_keys(partition_axis)

        Returns:
            List of value IDs to process (order preserved from available_values)

        Raises:
            ValueError: If values don't exist (INCLUDE mode only), insufficient values for count, or invalid patterns
        """
        resolved_values = PartitionFilterProcessor.resolve_compilation_filter(
            partition_filter,
            available_values,
            strict=partition_filter_mode.rejects_unknown_values,
        )
        resolved_identity_keys = {
            PartitionFilterProcessor._identity_key(value) for value in resolved_values
        }
        result = [
            value
            for value in available_values
            if (PartitionFilterProcessor._identity_key(value) in resolved_identity_keys)
            is partition_filter_mode.keeps_matches
        ]
        logger.debug(
            "Partition filter %r (%s) over %s selects %s",
            partition_filter,
            partition_filter_mode.value,
            available_values,
            result,
        )
        return result

    @staticmethod
    def resolve_compilation_filter(
        partition_filter: Union[List[str], str, int],
        available_values: List[str],
        strict: bool = True,
    ) -> Set[str]:
        """
        Resolve partition filter to concrete value set during compilation.

        NOTE: This method does NOT apply INCLUDE/EXCLUDE mode. Use resolve_filter_with_mode() instead
        for complete filter processing that respects partition_filter_mode.

        Combines validation and resolution in single method to avoid verbose helper methods.
        Supports all existing filter types while providing compilation-time optimization.
        Works with any value naming format (A01, R01C03, etc.) by using available values.

        Args:
            partition_filter: Filter specification (list, string pattern, or max count)
            available_values: Ordered list of values from orchestrator.get_component_keys(partition_axis)
            strict: If True, raise error for unknown partition values. If False, silently ignore them.

        Returns:
            Set of value IDs that match the filter (mode NOT applied)

        Raises:
            ValueError: If values don't exist (strict=True only), insufficient values for count, or invalid patterns
        """
        if isinstance(partition_filter, list):
            # Inline validation for specific values
            available_set = set(available_values)
            available_identity_keys = {
                PartitionFilterProcessor._identity_key(value) for value in available_values
            }
            invalid_values = [
                value
                for value in partition_filter
                if PartitionFilterProcessor._identity_key(value)
                not in available_identity_keys
            ]

            if invalid_values:
                if strict:
                    raise ValueError(
                        f"Invalid partition values specified: {invalid_values}. "
                        f"Available partition values: {sorted(available_set)}"
                    )
                else:
                    # Non-strict mode: filter out invalid values and continue
                    logger.warning(
                        f"Ignoring unknown partition values in filter: {invalid_values}"
                    )

            # Return only valid values
            requested_identity_keys = {
                PartitionFilterProcessor._identity_key(value)
                for value in partition_filter
                if PartitionFilterProcessor._identity_key(value)
                in available_identity_keys
            }
            return {
                value
                for value in available_set
                if PartitionFilterProcessor._identity_key(value)
                in requested_identity_keys
            }

        elif isinstance(partition_filter, int):
            # Inline validation for max count. Zero is the explicit empty
            # selection used by persistence policies that should emit no values.
            if partition_filter < 0:
                raise ValueError(f"Max count must be non-negative, got: {partition_filter}")
            if partition_filter == 0:
                return set()
            if partition_filter > len(available_values):
                raise ValueError(
                    f"Requested {partition_filter} values but only {len(available_values)} available"
                )
            return set(available_values[:partition_filter])

        elif isinstance(partition_filter, str):
            # Check if string is a Python list literal (common UI input issue)
            stripped = partition_filter.strip()
            if stripped.startswith("[") and stripped.endswith("]"):
                # Parse as Python list literal
                try:
                    parsed = ast.literal_eval(stripped)
                    if isinstance(parsed, list):
                        # Recursively call with the parsed list, preserving strict mode
                        return PartitionFilterProcessor.resolve_compilation_filter(
                            parsed, available_values, strict
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
                if numeric_value > len(available_values):
                    raise ValueError(
                        f"Requested {numeric_value} values but only {len(available_values)} available"
                    )
                return set(available_values[:numeric_value])

            else:
                # Non-numeric string - pass to pattern parsing for format-agnostic support
                return PartitionFilterProcessor._parse_pattern(
                    partition_filter, available_values
                )

        else:
            raise ValueError(f"Unsupported partition filter type: {type(partition_filter)}")

    @staticmethod
    def _parse_pattern(pattern: str, available_values: List[str]) -> Set[str]:
        """Parse string value patterns into value ID sets using available values."""
        pattern = pattern.strip()

        # Comma-separated list
        if PartitionFilterProcessor.COMMA_SEPARATOR in pattern:
            return set(
                w.strip() for w in pattern.split(PartitionFilterProcessor.COMMA_SEPARATOR)
            )

        # Row pattern: "row:A"
        if pattern.startswith(PartitionFilterProcessor.ROW_PREFIX):
            row = pattern[len(PartitionFilterProcessor.ROW_PREFIX) :].strip()
            return PartitionFilterProcessor._expand_row_pattern(row, available_values)

        # Column pattern: "col:01-06"
        if pattern.startswith(PartitionFilterProcessor.COL_PREFIX):
            col_spec = pattern[len(PartitionFilterProcessor.COL_PREFIX) :].strip()
            return PartitionFilterProcessor._expand_col_pattern(col_spec, available_values)

        # Range pattern: "A01:A12"
        if PartitionFilterProcessor.RANGE_SEPARATOR in pattern:
            return PartitionFilterProcessor._expand_range_pattern(pattern, available_values)

        # Single value
        return {pattern}

    @staticmethod
    def _expand_row_pattern(row: str, available_values: List[str]) -> Set[str]:
        """Expand row pattern using available values (format-agnostic)."""
        # Direct prefix match (A01, B02, etc.)
        result = {value for value in available_values if value.startswith(row)}

        # Opera Phenix format fallback (A → R01C*, B → R02C*)
        if not result and len(row) == 1 and row.isalpha():
            row_pattern = f"R{ord(row.upper()) - ord('A') + 1:02d}C"
            result = {value for value in available_values if value.startswith(row_pattern)}

        return result

    @staticmethod
    def _expand_col_pattern(col_spec: str, available_values: List[str]) -> Set[str]:
        """Expand column pattern using available values (format-agnostic)."""
        # Parse column range
        if "-" in col_spec:
            start_col, end_col = map(int, col_spec.split("-"))
            col_range = set(range(start_col, end_col + 1))
        else:
            col_range = {int(col_spec)}

        # Extract numeric suffix and match (A01, B02, etc.)
        def get_numeric_suffix(value: str) -> int:
            digits = "".join(char for char in reversed(value) if char.isdigit())
            return int(digits[::-1]) if digits else 0

        result = {
            value for value in available_values if get_numeric_suffix(value) in col_range
        }

        # Opera Phenix format fallback (C01, C02, etc.)
        if not result:
            patterns = {f"C{col:02d}" for col in col_range}
            result = {
                value
                for value in available_values
                if any(pattern in value for pattern in patterns)
            }

        return result

    @staticmethod
    def _expand_range_pattern(pattern: str, available_values: List[str]) -> Set[str]:
        """Expand range pattern using available values (format-agnostic)."""
        start_value, end_value = map(
            str.strip, pattern.split(PartitionFilterProcessor.RANGE_SEPARATOR)
        )

        try:
            start_idx, end_idx = available_values.index(
                start_value
            ), available_values.index(end_value)
        except ValueError as e:
            raise ValueError(
                f"Range pattern '{pattern}' contains values not in available values: {e}"
            )

        # Ensure proper order and return range (inclusive)
        start_idx, end_idx = sorted([start_idx, end_idx])
        return set(available_values[start_idx : end_idx + 1])
