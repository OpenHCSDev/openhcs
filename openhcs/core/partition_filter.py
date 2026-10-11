"""Partition filter resolution shared by the compiler and materialization planning.

A configured partition filter is a list of values, a count of leading values,
or a text pattern. It is decoded once into the member of the
``PartitionFilter`` family that owns its spelling; each member resolves itself
against the dataset's ordered partition values.
"""

import ast
import logging
from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import ClassVar, List, Sequence, Set, Union

from metaclass_registry import AutoRegisterMeta

from openhcs.core.config import PartitionFilterMode

logger = logging.getLogger(__name__)

PartitionFilterValue = Union[List[str], str, int]


def _identity_key(value: object) -> str:
    """Normalize a partition value for matching without replacing its source identity."""
    return str(value).casefold()


class PartitionFilter(ABC, metaclass=AutoRegisterMeta):
    """One decoded partition filter; the configured value's type picks the member."""

    __registry_key__ = "spelled_as"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[type, type["PartitionFilter"]]] = {}

    spelled_as: ClassVar[type | None] = None

    @classmethod
    def decode(cls, value: PartitionFilterValue) -> "PartitionFilter":
        member = cls.__registry__.get(type(value))
        if member is None:
            raise ValueError(f"Unsupported partition filter type: {type(value)}")
        return member.from_value(value)

    @classmethod
    @abstractmethod
    def from_value(cls, value: PartitionFilterValue) -> "PartitionFilter":
        """Decode one configured value of this member's spelling."""

    @abstractmethod
    def matches(self, available_values: Sequence[str], *, strict: bool) -> Set[str]:
        """The available values this filter names (the mode is not applied)."""


@dataclass(frozen=True)
class PartitionValueList(PartitionFilter):
    """Exact partition values, matched case-insensitively."""

    spelled_as: ClassVar[type] = list

    values: tuple[str, ...]

    @classmethod
    def from_value(cls, value: list) -> "PartitionValueList":
        return cls(tuple(value))

    def matches(self, available_values: Sequence[str], *, strict: bool) -> Set[str]:
        available_keys = {_identity_key(value) for value in available_values}
        unknown = [value for value in self.values if _identity_key(value) not in available_keys]
        if unknown and strict:
            raise ValueError(
                f"Invalid partition values specified: {unknown}. "
                f"Available partition values: {sorted(set(available_values))}"
            )
        if unknown:
            logger.warning(f"Ignoring unknown partition values in filter: {unknown}")
        requested = {_identity_key(value) for value in self.values}
        return {value for value in available_values if _identity_key(value) in requested}


@dataclass(frozen=True)
class LeadingPartitionCount(PartitionFilter):
    """The first N available partition values; zero selects none."""

    spelled_as: ClassVar[type] = int

    count: int

    @classmethod
    def from_value(cls, value: int) -> "LeadingPartitionCount":
        if value < 0:
            raise ValueError(f"Max count must be non-negative, got: {value}")
        return cls(value)

    def matches(self, available_values: Sequence[str], *, strict: bool) -> Set[str]:
        if self.count > len(available_values):
            raise ValueError(
                f"Requested {self.count} partition values but only "
                f"{len(available_values)} available"
            )
        return set(available_values[: self.count])


@dataclass(frozen=True)
class PartitionPattern(PartitionFilter):
    """Text: one value, ``a,b``, ``row:A``, ``col:01-06`` or an ``A01:A12`` range.

    A text that spells a list literal or a count decodes to that member.
    """

    spelled_as: ClassVar[type] = str

    COMMA_SEPARATOR: ClassVar[str] = ","
    RANGE_SEPARATOR: ClassVar[str] = ":"
    ROW_PREFIX: ClassVar[str] = "row:"
    COL_PREFIX: ClassVar[str] = "col:"

    pattern: str

    @classmethod
    def from_value(cls, value: str) -> PartitionFilter:
        stripped = value.strip()
        if stripped.startswith("[") and stripped.endswith("]"):
            try:
                return PartitionValueList.from_value(ast.literal_eval(stripped))
            except (ValueError, SyntaxError):
                pass
        if stripped.isdigit():
            return LeadingPartitionCount.from_value(int(stripped))
        return cls(stripped)

    def matches(self, available_values: Sequence[str], *, strict: bool) -> Set[str]:
        pattern = self.pattern
        if self.COMMA_SEPARATOR in pattern:
            return {value.strip() for value in pattern.split(self.COMMA_SEPARATOR)}
        if pattern.startswith(self.ROW_PREFIX):
            return self._row(pattern[len(self.ROW_PREFIX) :].strip(), available_values)
        if pattern.startswith(self.COL_PREFIX):
            return self._column(pattern[len(self.COL_PREFIX) :].strip(), available_values)
        if self.RANGE_SEPARATOR in pattern:
            return self._range(pattern, available_values)
        return {pattern}

    @staticmethod
    def _row(row: str, available_values: Sequence[str]) -> Set[str]:
        """Expand row pattern using available values (format-agnostic)."""
        result = {value for value in available_values if value.startswith(row)}
        # Opera Phenix format fallback (A → R01C*, B → R02C*)
        if not result and len(row) == 1 and row.isalpha():
            row_pattern = f"R{ord(row.upper()) - ord('A') + 1:02d}C"
            result = {value for value in available_values if value.startswith(row_pattern)}
        return result

    @staticmethod
    def _column(col_spec: str, available_values: Sequence[str]) -> Set[str]:
        """Expand column pattern using available values (format-agnostic)."""
        if "-" in col_spec:
            start_col, end_col = map(int, col_spec.split("-"))
            col_range = set(range(start_col, end_col + 1))
        else:
            col_range = {int(col_spec)}

        def numeric_suffix(value: str) -> int:
            digits = "".join(char for char in reversed(value) if char.isdigit())
            return int(digits[::-1]) if digits else 0

        result = {value for value in available_values if numeric_suffix(value) in col_range}
        # Opera Phenix format fallback (C01, C02, etc.)
        if not result:
            patterns = {f"C{col:02d}" for col in col_range}
            result = {
                value
                for value in available_values
                if any(pattern in value for pattern in patterns)
            }
        return result

    def _range(self, pattern: str, available_values: Sequence[str]) -> Set[str]:
        """Expand an inclusive range over the ordered available values."""
        start_value, end_value = map(str.strip, pattern.split(self.RANGE_SEPARATOR))
        ordered = list(available_values)
        try:
            start_idx, end_idx = ordered.index(start_value), ordered.index(end_value)
        except ValueError as e:
            raise ValueError(
                f"Range pattern '{pattern}' contains values not in available values: {e}"
            )
        start_idx, end_idx = sorted([start_idx, end_idx])
        return set(ordered[start_idx : end_idx + 1])


class PartitionFilterProcessor:
    """Resolve partition filter specifications against the available partition values."""

    @staticmethod
    def resolve_filter_with_mode(
        partition_filter: PartitionFilterValue,
        partition_filter_mode: PartitionFilterMode,
        available_values: List[str],
    ) -> List[str]:
        """The available values the filter and its mode select, in available order.

        Raises ValueError for values the dataset lacks (include mode only), counts
        beyond the available values, and malformed patterns.
        """
        matched_keys = {
            _identity_key(value)
            for value in PartitionFilter.decode(partition_filter).matches(
                available_values,
                strict=partition_filter_mode.rejects_unknown_values,
            )
        }
        result = [
            value
            for value in available_values
            if (_identity_key(value) in matched_keys) is partition_filter_mode.keeps_matches
        ]
        logger.debug(
            "Partition filter %r (%s) over %s selects %s",
            partition_filter,
            partition_filter_mode.value,
            available_values,
            result,
        )
        return result
