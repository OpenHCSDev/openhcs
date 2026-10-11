"""Per-axis value filters, validated against the active axis family."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass

from openhcs.core.axes import AxisFamily

ComponentFilterMapping = Mapping[str, Sequence[str] | str]
"""Boundary spelling: axis name to one accepted value or several."""


@dataclass(frozen=True, slots=True)
class ComponentFilters:
    """Accepted values per axis.

    A record matches when, for every filtered axis, its metadata holds one of
    that axis's accepted values. No filters match every record.
    """

    by_axis: tuple[tuple[str, tuple[str, ...]], ...] = ()

    def __post_init__(self) -> None:
        if not self.by_axis:
            return
        family = AxisFamily.active()
        unknown = sorted(name for name, _values in self.by_axis if name not in family.names())
        if unknown:
            raise ValueError(
                f"component_filters name unknown axes {unknown}; the "
                f"{family.__qualname__} axes are {list(family.names())}."
            )
        empty = sorted(name for name, values in self.by_axis if not values)
        if empty:
            raise ValueError(f"component_filters give no values for axes {empty}.")

    @classmethod
    def from_mapping(cls, mapping: ComponentFilterMapping | None) -> ComponentFilters:
        """Read the boundary spelling; a single string is one accepted value."""

        if not mapping:
            return cls()
        return cls(
            by_axis=tuple(
                (
                    str(name),
                    (values,) if isinstance(values, str) else tuple(str(value) for value in values),
                )
                for name, values in mapping.items()
            )
        )

    @classmethod
    def from_assignments(cls, assignments: Sequence[str]) -> ComponentFilters:
        """Read repeated ``axis=value`` assignments (the CLI spelling)."""

        accepted: dict[str, list[str]] = {}
        for assignment in assignments:
            name, separator, value = assignment.partition("=")
            if not separator or not name or not value:
                raise ValueError(f"Expected axis=value, received {assignment!r}.")
            accepted.setdefault(name, []).append(value)
        return cls.from_mapping(accepted)

    def as_mapping(self) -> dict[str, list[str]]:
        return {name: list(values) for name, values in self.by_axis}

    def matches(self, metadata: Mapping[str, object]) -> bool:
        return all(
            metadata.get(name) is not None and str(metadata[name]) in values
            for name, values in self.by_axis
        )

    def __bool__(self) -> bool:
        return bool(self.by_axis)
