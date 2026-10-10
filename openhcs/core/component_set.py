"""Ordered unique sets of declared axes."""

from __future__ import annotations

from collections.abc import Iterable, Iterator
from dataclasses import dataclass

from openhcs.core.axes import Axis, AxisFamily, PartitionAxis, is_axis


@dataclass(slots=True)
class ComponentSet:
    """Ordered unique set of declared axes."""

    components: tuple[type[Axis], ...] = ()

    def __post_init__(self) -> None:
        normalized: list[type[Axis]] = []
        for component in self.components:
            if not is_axis(component):
                raise TypeError(
                    f"ComponentSet components must be declared axes, got {component!r}."
                )
            if component not in normalized:
                normalized.append(component)
        self.components = tuple(normalized)

    @classmethod
    def of(cls, components: Iterable[type[Axis]]) -> "ComponentSet":
        return cls(tuple(components))

    @classmethod
    def collect(
        cls,
        *groups: Iterable[type[Axis] | None],
    ) -> "ComponentSet":
        return cls(
            tuple(
                component
                for group in groups
                for component in group
                if component is not None
            )
        )

    @classmethod
    def default_variable(cls) -> "ComponentSet":
        return cls(AxisFamily.active().default_variable())

    @classmethod
    def default_group_by(cls) -> "ComponentSet":
        return cls(AxisFamily.active().default_group_by().grouping_axes())

    def __bool__(self) -> bool:
        return bool(self.components)

    def __contains__(self, component: type[Axis]) -> bool:
        return component in self.components

    def __iter__(self) -> Iterator[type[Axis]]:
        return iter(self.components)

    def as_tuple(self) -> tuple[type[Axis], ...]:
        return self.components

    def variable(self) -> "ComponentSet":
        return ComponentSet(
            tuple(
                component
                for component in self.components
                if not issubclass(component, PartitionAxis)
            )
        )

    def excluding(self, *others: "ComponentSet") -> "ComponentSet":
        excluded = frozenset(
            component for other in others for component in other.components
        )
        return ComponentSet(
            tuple(
                component for component in self.components if component not in excluded
            )
        )

    def intersection(self, other: "ComponentSet") -> "ComponentSet":
        return ComponentSet(
            tuple(component for component in self.components if component in other)
        )

    def required_last(self, error_message: str) -> type[Axis]:
        if not self.components:
            raise ValueError(error_message)
        return self.components[-1]

    def single_or_none(self, multiple_error_message: str) -> type[Axis] | None:
        if not self.components:
            return None
        if len(self.components) == 1:
            return self.components[0]
        raise ValueError(multiple_error_message)

    def last(self) -> type[Axis] | None:
        if not self.components:
            return None
        return self.components[-1]
