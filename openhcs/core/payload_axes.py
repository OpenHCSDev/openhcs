"""Declared dimensions of a tensor payload.

A payload's array has one :class:`AxisSpec` per dimension. Most dimensions are
declared explicitly, by position, in :class:`PayloadAxes` (a family axis, the
colour samples of one source image); the spatial dimensions come from the
payload's spatial domain, which names them; the leading runtime plane axis
comes from the payload's plane declaration. Whatever nothing declares is an
:class:`UndeclaredAxisSpec`. Kernel code asks for dimensions by role, never by
position or name.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from typing import Any, ClassVar

from metaclass_registry import AutoRegisterMeta
from python_introspect import to_jsonable

from openhcs.core.axes import Axis, AxisFamily, AxisRole, ColourAxis


class SpatialAxis(AxisRole):
    """A spatial dimension, named by the payload's spatial domain."""


class AxisSpec(ABC, metaclass=AutoRegisterMeta):
    """One declared dimension of a tensor payload."""

    __registry_key__ = "spec_kind"
    __skip_if_no_key__ = True
    spec_kind: ClassVar[str | None] = None

    @property
    @abstractmethod
    def name(self) -> str:
        """Boundary spelling of this dimension."""

    @property
    @abstractmethod
    def roles(self) -> tuple[type[AxisRole], ...]:
        """Roles this dimension carries."""

    def has_role(self, role: type[AxisRole]) -> bool:
        return any(issubclass(declared, role) for declared in self.roles)

    def to_mapping(self) -> dict[str, Any]:
        return {"kind": self.spec_kind}

    @classmethod
    def from_mapping(cls, values: Mapping[str, Any]) -> "AxisSpec":
        payload = dict(values)
        spec_type = cls.__registry__[payload.pop("kind")]
        return spec_type.decode(payload)

    @classmethod
    def decode(cls, values: Mapping[str, Any]) -> "AxisSpec":
        if values:
            raise ValueError(f"{cls.__name__} takes no fields; got {sorted(values)!r}.")
        return cls()


@dataclass(frozen=True, slots=True)
class FamilyAxisSpec(AxisSpec):
    """A dimension that carries one axis of the active family."""

    spec_kind: ClassVar[str] = "family"
    axis: type[Axis]

    @property
    def name(self) -> str:
        return self.axis.name

    @property
    def roles(self) -> tuple[type[AxisRole], ...]:
        return tuple(
            base
            for base in self.axis.__mro__
            if isinstance(base, type)
            and issubclass(base, AxisRole)
            and base is not AxisRole
        )

    def to_mapping(self) -> dict[str, Any]:
        return {"kind": self.spec_kind, "axis": self.axis.name}

    @classmethod
    def decode(cls, values: Mapping[str, Any]) -> "FamilyAxisSpec":
        return cls(AxisFamily.active().named(str(values["axis"])))


@dataclass(frozen=True, slots=True)
class ColourSampleAxisSpec(AxisSpec):
    """The colour samples (for example RGB) inside one source image."""

    spec_kind: ClassVar[str] = "colour_samples"

    @property
    def name(self) -> str:
        return "colour_samples"

    @property
    def roles(self) -> tuple[type[AxisRole], ...]:
        return (ColourAxis,)


@dataclass(frozen=True, slots=True)
class SpatialAxisSpec(AxisSpec):
    """One spatial dimension, named by the spatial domain's rank."""

    spec_kind: ClassVar[str] = "spatial"
    axis_name: str

    @property
    def name(self) -> str:
        return self.axis_name

    @property
    def roles(self) -> tuple[type[AxisRole], ...]:
        return (SpatialAxis,)


@dataclass(frozen=True, slots=True)
class RuntimePlaneAxisSpec(AxisSpec):
    """The leading runtime plane axis a payload declares."""

    spec_kind: ClassVar[str] = "runtime_plane"
    plane_axis_name: str

    @property
    def name(self) -> str:
        return self.plane_axis_name

    @property
    def roles(self) -> tuple[type[AxisRole], ...]:
        return ()


@dataclass(frozen=True, slots=True)
class UndeclaredAxisSpec(AxisSpec):
    """A dimension nothing declares."""

    spec_kind: ClassVar[str] = "undeclared"

    @property
    def name(self) -> str:
        return ""

    @property
    def roles(self) -> tuple[type[AxisRole], ...]:
        return ()


def _require_position(position: object) -> int:
    if not isinstance(position, int) or isinstance(position, bool):
        raise TypeError(f"Declared payload axis positions must be int; got {position!r}.")
    return position


@dataclass(frozen=True, slots=True)
class PositionedAxis:
    """A declared dimension at a rank-relative position (negative counts from the end)."""

    spec: AxisSpec
    position: int

    def __post_init__(self) -> None:
        if not isinstance(self.spec, AxisSpec):
            raise TypeError(f"PositionedAxis.spec must be an AxisSpec; got {self.spec!r}.")
        _require_position(self.position)

    def index(self, ndim: int) -> int:
        """Return this axis's index in an array of rank ``ndim``."""
        index = self.position if self.position >= 0 else ndim + self.position
        if index < 0 or index >= ndim:
            raise ValueError(
                f"Declared {self.spec.name!r} axis at position {self.position} is "
                f"invalid for payload rank {ndim}."
            )
        return index

    def to_mapping(self) -> dict[str, Any]:
        return {"spec": self.spec.to_mapping(), "position": self.position}


@dataclass(frozen=True, slots=True)
class PayloadAxes:
    """The explicitly declared dimensions of a payload, by rank-relative position."""

    declared: tuple[PositionedAxis, ...] = ()

    def __post_init__(self) -> None:
        declared = tuple(self.declared)
        if any(not isinstance(axis, PositionedAxis) for axis in declared):
            raise TypeError("PayloadAxes.declared must contain PositionedAxis values.")
        positions = [axis.position for axis in declared]
        if len(set(positions)) != len(positions):
            raise ValueError(f"Declared payload axes repeat a position: {positions!r}.")
        object.__setattr__(self, "declared", declared)

    @classmethod
    def of(cls, *axes: tuple[AxisSpec, int]) -> "PayloadAxes":
        return cls(tuple(PositionedAxis(spec, position) for spec, position in axes))

    @classmethod
    def colour_samples(cls, position: int | None) -> "PayloadAxes":
        """Declare a source file's colour-sample axis, as file formats report it.

        Image formats and source bindings spell an absent colour axis as None.
        """
        if position is None:
            return cls()
        return cls.of((ColourSampleAxisSpec(), position))

    @property
    def has_values(self) -> bool:
        return bool(self.declared)

    def with_axis(self, spec: AxisSpec, position: int) -> "PayloadAxes":
        """Declare ``spec`` at ``position``, replacing any axis with the same spec."""
        return type(self)(
            (
                *(axis for axis in self.declared if axis.spec != spec),
                PositionedAxis(spec, position),
            )
        )

    def without_role(self, role: type[AxisRole]) -> "PayloadAxes":
        return type(self)(
            tuple(axis for axis in self.declared if not axis.spec.has_role(role))
        )

    def with_role(self, role: type[AxisRole]) -> tuple[PositionedAxis, ...]:
        return tuple(axis for axis in self.declared if axis.spec.has_role(role))

    def position_of(self, role: type[AxisRole]) -> int | None:
        """Return the declared position of the one axis carrying ``role``."""
        matches = self.with_role(role)
        if len(matches) > 1:
            raise ValueError(
                f"Payload declares {len(matches)} axes with role {role.__name__}."
            )
        return matches[0].position if matches else None

    def index_of(self, role: type[AxisRole], ndim: int) -> int | None:
        matches = self.with_role(role)
        if len(matches) > 1:
            raise ValueError(
                f"Payload declares {len(matches)} axes with role {role.__name__}."
            )
        return matches[0].index(ndim) if matches else None

    def indices(self, ndim: int) -> dict[int, AxisSpec]:
        """Return each declared axis keyed by its index for rank ``ndim``."""
        resolved: dict[int, AxisSpec] = {}
        for axis in self.declared:
            index = axis.index(ndim)
            if index in resolved:
                raise ValueError(
                    f"Declared payload axes {resolved[index].name!r} and "
                    f"{axis.spec.name!r} share index {index} at rank {ndim}."
                )
            resolved[index] = axis.spec
        return resolved

    def after_leading_axis_removed(self) -> "PayloadAxes":
        """Positions after a leading axis is removed; the removed axis is not declared here."""
        if any(axis.position == 0 for axis in self.declared):
            leading = next(axis for axis in self.declared if axis.position == 0)
            raise ValueError(
                "Image metadata cannot declare the same leading axis as both plane "
                f"and {leading.spec.name!r}."
            )
        return type(self)(
            tuple(
                PositionedAxis(axis.spec, axis.position - 1 if axis.position > 0 else axis.position)
                for axis in self.declared
            )
        )

    def normalized_for(self, ndim: int) -> "PayloadAxes":
        """Positions as nonnegative indices for one concrete rank."""
        return type(self)(
            tuple(PositionedAxis(axis.spec, axis.index(ndim)) for axis in self.declared)
        )

    def after_leading_axis_added(self, ndim: int) -> "PayloadAxes":
        """Positions after a new leading axis is stacked onto arrays of rank ``ndim``."""
        return type(self)(
            tuple(
                PositionedAxis(axis.spec, axis.index(ndim) + 1) for axis in self.declared
            )
        )

    @classmethod
    def common_after_stacking(
        cls, members: Iterable[tuple["PayloadAxes", int]],
    ) -> "PayloadAxes":
        """Return the axes of a stack built from members, each with its rank."""
        normalized = tuple(
            axes.normalized_for(ndim) for axes, ndim in members if axes.has_values
        )
        if not normalized:
            return cls()
        first = normalized[0]
        if any(axes != first for axes in normalized[1:]):
            raise ValueError(
                "Cannot compose image payloads with conflicting declared axes: "
                f"{tuple(axes.declared for axes in normalized)!r}."
            )
        return cls(
            tuple(PositionedAxis(axis.spec, axis.position + 1) for axis in first.declared)
        )

    def to_mapping(self) -> list[dict[str, Any]]:
        return [axis.to_mapping() for axis in self.declared]

    @classmethod
    def from_mapping(cls, values: Iterable[Mapping[str, Any]]) -> "PayloadAxes":
        return cls(
            tuple(
                PositionedAxis(
                    AxisSpec.from_mapping(item["spec"]),
                    _require_position(item["position"]),
                )
                for item in values
            )
        )


to_jsonable.register(PayloadAxes, PayloadAxes.to_mapping)


__all__ = [
    "AxisSpec",
    "ColourSampleAxisSpec",
    "FamilyAxisSpec",
    "PayloadAxes",
    "PositionedAxis",
    "RuntimePlaneAxisSpec",
    "SpatialAxis",
    "SpatialAxisSpec",
    "UndeclaredAxisSpec",
]
