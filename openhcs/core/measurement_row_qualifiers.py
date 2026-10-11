"""Row fields that qualify measurement feature names.

Some measurements produce several values per object or sample that differ only
by a row field: texture by scale, direction and gray levels, radial
distribution by bin. A :class:`RuntimeMeasurementRowQualifier` names those
fields; its :class:`RowQualifierFormat` renders their values into a feature-name
suffix (``_3_00_256``, ``_2of4``) and recognizes that suffix again when parsing
a feature name.
"""

from __future__ import annotations

import math
from abc import ABC, abstractmethod
from collections.abc import Mapping
from dataclasses import dataclass
from typing import ClassVar

from openhcs.core.runtime_identifier import normalize_runtime_identifier


class RowQualifierFormat(ABC):
    """How one qualifier's values render into, and parse from, a feature suffix."""

    distinctive: ClassVar[bool] = True
    """Whether a suffix in this format identifies itself without a known prefix."""

    @classmethod
    @abstractmethod
    def render(cls, values: tuple[object, ...]) -> str | None:
        """Render present qualifier values as one suffix, or ``None``."""

    @classmethod
    @abstractmethod
    def suffix_token_width(
        cls,
        feature_tokens: tuple[str, ...],
        end_index: int,
    ) -> int | None:
        """Return how many tokens before ``end_index`` this format owns."""


class IdentifierFormat(RowQualifierFormat):
    """Free-form identifiers joined by underscores (``scale`` -> ``3``)."""

    distinctive = False

    @classmethod
    def render(cls, values: tuple[object, ...]) -> str | None:
        return "_".join(_qualifier_identifier(value) for value in values)

    @classmethod
    def suffix_token_width(
        cls,
        feature_tokens: tuple[str, ...],
        end_index: int,
    ) -> int | None:
        del feature_tokens
        return 1 if end_index > 0 else None


class TwoDigitIntegerFormat(RowQualifierFormat):
    """A zero-padded two-digit integer (``direction`` -> ``00``)."""

    @classmethod
    def render(cls, values: tuple[object, ...]) -> str | None:
        return str(_qualifier_integer(values[0])).zfill(2)

    @classmethod
    def suffix_token_width(
        cls,
        feature_tokens: tuple[str, ...],
        end_index: int,
    ) -> int | None:
        if end_index <= 0:
            return None
        token = feature_tokens[end_index - 1]
        return 1 if len(token) == 2 and token.isdigit() else None


class FractionOfCountFormat(RowQualifierFormat):
    """An index and a count as ``NofM`` (``bin_index``, ``bin_count`` -> ``2of4``)."""

    @classmethod
    def render(cls, values: tuple[object, ...]) -> str | None:
        if len(values) != 2:
            return None
        return f"{_qualifier_integer(values[0])}of{_qualifier_integer(values[1])}"

    @classmethod
    def suffix_token_width(
        cls,
        feature_tokens: tuple[str, ...],
        end_index: int,
    ) -> int | None:
        if end_index < 3:
            return None
        left, of_token, right = feature_tokens[end_index - 3 : end_index]
        return 3 if left.isdigit() and of_token == "of" and right.isdigit() else None


@dataclass(frozen=True, slots=True)
class RuntimeMeasurementRowQualifier:
    """Row fields whose values qualify the names of the features they apply to."""

    field_names: tuple[str, ...]
    value_format: type[RowQualifierFormat] = IdentifierFormat
    feature_prefixes: tuple[tuple[str, ...], ...] = ()

    def __post_init__(self) -> None:
        field_names = tuple(
            normalize_runtime_identifier(field_name)
            for field_name in self.field_names
            if str(field_name).strip()
        )
        if not field_names:
            raise ValueError(
                "RuntimeMeasurementRowQualifier.field_names cannot be empty."
            )
        object.__setattr__(self, "field_names", field_names)
        object.__setattr__(
            self,
            "feature_prefixes",
            tuple(
                tuple(
                    normalize_runtime_identifier(part)
                    for part in prefix
                    if str(part).strip()
                )
                for prefix in self.feature_prefixes
            ),
        )

    def applies_to(self, field_parts: tuple[str, ...]) -> bool:
        """Return whether this qualifier qualifies a feature with these parts."""
        if not self.feature_prefixes:
            return True
        return any(
            len(field_parts) >= len(prefix) and field_parts[: len(prefix)] == prefix
            for prefix in self.feature_prefixes
        )

    def render_values(self, values: tuple[object, ...]) -> str | None:
        """Render this qualifier's values, or ``None`` when any is missing."""
        if any(_is_missing_qualifier_value(value) for value in values):
            return None
        return self.value_format.render(values)

    def render_row(self, row: Mapping[str, object]) -> str | None:
        """Render this qualifier from a row whose field names may need normalizing."""
        normalized_fields = {normalize_runtime_identifier(field): field for field in row}
        return self.render_values(
            tuple(
                row[normalized_fields[field_name]]
                if field_name in normalized_fields
                else None
                for field_name in self.field_names
            )
        )

    def render_normalized_row(self, row: Mapping[str, object]) -> str | None:
        """Render this qualifier from a row keyed by normalized field names."""
        return self.render_values(
            tuple(row.get(field_name) for field_name in self.field_names)
        )

    def suffix_token_width(
        self,
        feature_tokens: tuple[str, ...],
        end_index: int,
    ) -> int | None:
        """Return how many tokens before ``end_index`` this qualifier owns."""
        return self.value_format.suffix_token_width(feature_tokens, end_index)


@dataclass(frozen=True, slots=True)
class RuntimeMeasurementRowQualifierSequence:
    """Declared row-qualifier sequence rendered as one feature suffix."""

    field_names_by_qualifier: tuple[tuple[str, ...], ...]

    def __post_init__(self) -> None:
        field_names_by_qualifier = tuple(
            tuple(
                normalize_runtime_identifier(field_name)
                for field_name in field_names
                if str(field_name).strip()
            )
            for field_names in self.field_names_by_qualifier
        )
        if not field_names_by_qualifier or any(
            not field_names for field_names in field_names_by_qualifier
        ):
            raise ValueError(
                "RuntimeMeasurementRowQualifierSequence requires non-empty "
                "qualifier field names."
            )
        object.__setattr__(
            self,
            "field_names_by_qualifier",
            field_names_by_qualifier,
        )


DEFAULT_MEASUREMENT_ROW_QUALIFIERS = (
    RuntimeMeasurementRowQualifier(("scale",)),
    RuntimeMeasurementRowQualifier(("direction",), TwoDigitIntegerFormat),
    RuntimeMeasurementRowQualifier(("gray_levels",)),
    RuntimeMeasurementRowQualifier(
        ("bin_index", "bin_count"),
        FractionOfCountFormat,
    ),
)
DEFAULT_MEASUREMENT_ROW_QUALIFIER_SEQUENCES = (
    RuntimeMeasurementRowQualifierSequence(
        (("scale",), ("direction",), ("gray_levels",))
    ),
    RuntimeMeasurementRowQualifierSequence((("bin_index", "bin_count"),)),
)


def _qualifier_identifier(value: object) -> str:
    integer_value = _optional_qualifier_integer(value)
    if integer_value is not None:
        return str(integer_value)
    return normalize_runtime_identifier(value)


def _is_missing_qualifier_value(value: object) -> bool:
    if value is None:
        return True
    text = str(value).strip()
    if not text:
        return True
    try:
        return math.isnan(float(text))
    except (TypeError, ValueError):
        return False


def _qualifier_integer(value: object) -> int:
    integer_value = _optional_qualifier_integer(value)
    if integer_value is None:
        raise ValueError(f"Measurement qualifier {value!r} is not integer-like.")
    return integer_value


def _optional_qualifier_integer(value: object) -> int | None:
    try:
        numeric = float(str(value).strip())
    except (TypeError, ValueError):
        return None
    if not math.isfinite(numeric) or not numeric.is_integer():
        return None
    return int(numeric)
