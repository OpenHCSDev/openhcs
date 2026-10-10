"""Complete value sets over the active axis family."""

from __future__ import annotations

from collections.abc import Iterable, Iterator, Mapping
from types import MappingProxyType
from typing import Generic, TypeVar

from openhcs.core.axes import Axis, AxisFamily, is_axis

ComponentValueT = TypeVar("ComponentValueT")


class AxisValues(
    Mapping[type[Axis], ComponentValueT],
    Generic[ComponentValueT],
):
    """Complete immutable values, one per axis of the active family."""

    __slots__ = ("_declared_values",)

    def __init__(
        self,
        component_values: Iterable[tuple[type[Axis], ComponentValueT]],
    ) -> None:
        family = AxisFamily.active()
        supplied_values = tuple(component_values)
        if any(not family.contains(axis) for axis, _ in supplied_values):
            raise TypeError(
                f"Axis values require axes of {family.__qualname__}; got "
                f"{[axis for axis, _ in supplied_values if not family.contains(axis)]}"
            )

        values_by_axis = dict(supplied_values)
        if len(values_by_axis) != len(supplied_values):
            raise ValueError("Each axis may be bound only once")

        missing = tuple(axis for axis in family.axes if axis not in values_by_axis)
        if missing:
            raise ValueError(
                "Axis values must bind the active family exactly: "
                + ", ".join(f"missing {axis.name}" for axis in missing)
            )

        self._declared_values = tuple(
            (axis, values_by_axis[axis]) for axis in family.axes
        )

    @classmethod
    def from_partial(
        cls,
        component_values: Iterable[tuple[type[Axis], ComponentValueT]],
        *,
        missing_value: ComponentValueT,
    ) -> "AxisValues[ComponentValueT]":
        """Complete a partial binding with one explicit absent value."""

        supplied_values = tuple(component_values)
        values_by_axis = dict(supplied_values)
        if len(values_by_axis) != len(supplied_values):
            raise ValueError("Each axis may be bound only once")
        family = AxisFamily.active()
        for axis in values_by_axis:
            family.require(axis)
        return cls(
            (axis, values_by_axis.get(axis, missing_value)) for axis in family.axes
        )

    @classmethod
    def from_wire_mapping(
        cls,
        component_values: Mapping[str, ComponentValueT],
        *,
        missing_value: ComponentValueT,
    ) -> "AxisValues[ComponentValueT]":
        """Read each declared axis's boundary name from ``component_values``."""

        family = AxisFamily.active()
        return cls(
            (axis, component_values.get(axis.name, missing_value))
            for axis in family.axes
        )

    def declared_values(
        self,
    ) -> tuple[tuple[type[Axis], ComponentValueT], ...]:
        """Return values in declaration order."""

        return self._declared_values

    def __getitem__(self, component: type[Axis]) -> ComponentValueT:
        return self.value_for(component)

    def __iter__(self) -> Iterator[type[Axis]]:
        return (axis for axis, _ in self._declared_values)

    def __len__(self) -> int:
        return len(self._declared_values)

    def value_for(self, component: type[Axis]) -> ComponentValueT:
        """Return the value for one declared axis."""

        if not is_axis(component):
            raise TypeError(f"Axis lookup requires a declared axis; got {component!r}")
        for declared_axis, value in self._declared_values:
            if declared_axis is component:
                return value
        raise KeyError(component)

    def with_value(
        self,
        component: type[Axis],
        value: ComponentValueT,
    ) -> "AxisValues[ComponentValueT]":
        """Return a value set with one axis replaced."""

        self.value_for(component)
        return type(self)(
            (
                declared_axis,
                value if declared_axis is component else current_value,
            )
            for declared_axis, current_value in self._declared_values
        )

    def wire_mapping(self) -> Mapping[str, ComponentValueT]:
        """Serialize values at an explicit string-keyed boundary."""

        return MappingProxyType(
            {axis.name: value for axis, value in self._declared_values}
        )

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, AxisValues):
            return NotImplemented
        return self._declared_values == other._declared_values

    def __hash__(self) -> int:
        return hash(self._declared_values)
