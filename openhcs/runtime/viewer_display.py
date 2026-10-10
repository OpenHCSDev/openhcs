"""What a viewer is told about a stream's axes, and where each viewer puts them.

A stream's display config carries its own :class:`DeclaredAxis` list. The
viewer validates and lays out the stream from those declarations, never from
the axis family active in its own process, so a viewer shows any domain's
axes. Each viewer owns a :class:`ViewerSlotFamily`: the native slots it can put
an axis into, and which roles default to which slot.
"""

from abc import ABC
from collections.abc import Iterator, Mapping, Sequence
from dataclasses import dataclass, field, fields
from enum import Enum
from functools import cache
from typing import ClassVar

from python_introspect import (
    AnnotatedDataclassValidationMixin,
    dataclass_from_mapping,
)
from zmqruntime.config import NonBlankString
from zmqruntime.viewer_protocol import ViewerWireMapping, ViewerWirePayload, ViewerWireValue

from openhcs.core.axes import (
    Axis,
    AxisRole,
    AxisValueKind,
    ColourAxis,
    OrdinalValued,
    StackAxis,
    TimeAxis,
)

DECLARED_AXES_FIELD = "declared_axes"
"""Display-config wire field carrying the stream's axis declarations."""


def _declared_kinds(base: type) -> dict[str, type]:
    """Role or value-kind classes by wire name, derived from inheritance."""

    kinds: dict[str, type] = {}
    pending = list(base.__subclasses__())
    while pending:
        kind = pending.pop()
        pending.extend(kind.__subclasses__())
        if not issubclass(kind, Axis):
            kinds[kind.__name__] = kind
    return kinds


def _decode_kind(base: type, name: object, *, context: str) -> type:
    kinds = _declared_kinds(base)
    if not isinstance(name, str) or name not in kinds:
        raise ValueError(f"{context} names unknown {base.__name__} {name!r}.")
    return kinds[name]


@dataclass(frozen=True, slots=True)
class DeclaredAxis:
    """One axis of a stream, as declared by the domain that produced it."""

    name: str
    label: str
    roles: tuple[type[AxisRole], ...]
    value_kind: type[AxisValueKind]

    @classmethod
    def of(cls, axis: type[Axis]) -> "DeclaredAxis":
        return cls(
            name=axis.name,
            label=axis.label,
            roles=tuple(
                base
                for base in axis.__mro__
                if issubclass(base, AxisRole)
                and base is not AxisRole
                and not issubclass(base, Axis)
            ),
            value_kind=next(
                base
                for base in axis.__mro__
                if AxisValueKind in base.__bases__ and not issubclass(base, Axis)
            ),
        )

    def has_role(self, role: type[AxisRole]) -> bool:
        return any(issubclass(declared, role) for declared in self.roles)

    def normalize_value(self, value: object) -> object:
        """Read numeric text of an ordinal axis as its integer value."""

        if issubclass(self.value_kind, OrdinalValued) and isinstance(value, str):
            stripped = value.strip()
            if stripped and stripped.lstrip("+-").isdigit():
                return int(stripped)
        return value

    def to_wire(self) -> dict[str, ViewerWireValue]:
        return {
            "name": self.name,
            "label": self.label,
            "roles": [role.__name__ for role in self.roles],
            "value_kind": self.value_kind.__name__,
        }

    @classmethod
    def from_wire(cls, payload: object) -> "DeclaredAxis":
        if not isinstance(payload, Mapping):
            raise TypeError("A declared axis must be a mapping.")
        name = payload["name"]
        label = payload["label"]
        roles = payload["roles"]
        if not isinstance(name, str) or not name or not isinstance(label, str):
            raise TypeError(f"Declared axis needs text name and label, got {payload!r}.")
        if isinstance(roles, str) or not isinstance(roles, Sequence):
            raise TypeError(f"Declared axis {name!r} roles must be a sequence.")
        context = f"Declared axis {name!r}"
        return cls(
            name=name,
            label=label,
            roles=tuple(_decode_kind(AxisRole, role, context=context) for role in roles),
            value_kind=_decode_kind(AxisValueKind, payload["value_kind"], context=context),
        )


@dataclass(frozen=True, slots=True)
class DeclaredAxes:
    """A stream's declared axes, in declaration order."""

    axes: tuple[DeclaredAxis, ...] = ()

    def __post_init__(self) -> None:
        names = [axis.name for axis in self.axes]
        if len(set(names)) != len(names):
            raise ValueError(f"Declared axes repeat a name: {names!r}.")

    @classmethod
    def of(cls, axes: Sequence[type[Axis]]) -> "DeclaredAxes":
        return cls(tuple(DeclaredAxis.of(axis) for axis in axes))

    @classmethod
    def from_wire(cls, payload: object) -> "DeclaredAxes":
        if isinstance(payload, str) or not isinstance(payload, Sequence):
            raise TypeError(f"{DECLARED_AXES_FIELD!r} must be a sequence of axes.")
        return cls(tuple(DeclaredAxis.from_wire(axis) for axis in payload))

    @classmethod
    def from_display_payload(cls, payload: Mapping[str, ViewerWireValue]) -> "DeclaredAxes":
        if DECLARED_AXES_FIELD not in payload:
            raise ValueError(f"Display config is missing {DECLARED_AXES_FIELD!r}.")
        return cls.from_wire(payload[DECLARED_AXES_FIELD])

    def to_wire(self) -> list[dict[str, ViewerWireValue]]:
        return [axis.to_wire() for axis in self.axes]

    def __iter__(self) -> Iterator[DeclaredAxis]:
        return iter(self.axes)

    def __bool__(self) -> bool:
        return bool(self.axes)

    def names(self) -> tuple[str, ...]:
        return tuple(axis.name for axis in self.axes)

    def __contains__(self, name: object) -> bool:
        return name in self.names()

    def named(self, name: str) -> DeclaredAxis:
        for axis in self.axes:
            if axis.name == name:
                return axis
        raise ValueError(f"{name!r} is not a declared axis; declared: {self.names()!r}.")

    def with_role(self, role: type[AxisRole]) -> tuple[DeclaredAxis, ...]:
        return tuple(axis for axis in self.axes if axis.has_role(role))

    def names_with_role(self, role: type[AxisRole]) -> tuple[str, ...]:
        return tuple(axis.name for axis in self.with_role(role))

    def label(self, name: str) -> str:
        """The declared label of an axis; an undeclared component keeps its name."""

        return self.named(name).label if name in self else name

    def normalize_value(self, name: str, value: object) -> object:
        return self.named(name).normalize_value(value) if name in self else value

    def require_names(self, names: Sequence[str], *, context: str) -> None:
        undeclared = tuple(name for name in names if name not in self)
        if undeclared:
            raise ValueError(
                f"{context} names undeclared axes {undeclared!r}; "
                f"the stream declares {self.names()!r}."
            )


# ---------------------------------------------------------------------------
# Native slots
# ---------------------------------------------------------------------------


class ViewerSlot(ABC):
    """One native place a viewer can put an axis's values."""

    wire_value: ClassVar[str]
    roles: ClassVar[tuple[type[AxisRole], ...]] = ()
    """Axes with one of these roles default to this slot."""
    separates_values: ClassVar[bool] = False
    """Each value of an axis in this slot gets its own native layer or window."""


class ViewerSlotFamily(ABC):
    """The slots one viewer offers, declared as nested :class:`ViewerSlot` classes."""

    slots: ClassVar[tuple[type[ViewerSlot], ...]] = ()
    default_slot: ClassVar[type[ViewerSlot]]
    families: ClassVar[list[type["ViewerSlotFamily"]]] = []

    def __init_subclass__(cls, **kwargs: object) -> None:
        super().__init_subclass__(**kwargs)
        ViewerSlotFamily.families.append(cls)
        cls.slots = tuple(
            value
            for key, value in cls.__dict__.items()
            if isinstance(value, type)
            and issubclass(value, ViewerSlot)
            and key == value.__name__
        )

    @staticmethod
    def separating_wire_values() -> frozenset[str]:
        """Wire values of every slot, in any viewer, that splits values apart."""

        return frozenset(
            slot.wire_value
            for family in ViewerSlotFamily.families
            for slot in family.slots
            if slot.separates_values
        )

    @classmethod
    def slot_for_roles(cls, roles: Sequence[type[AxisRole]]) -> type[ViewerSlot]:
        """The first slot claiming one of ``roles``, else the default slot."""

        for slot in cls.slots:
            if any(issubclass(role, claimed) for role in roles for claimed in slot.roles):
                return slot
        return cls.default_slot

    @classmethod
    def slot_for(cls, axis: DeclaredAxis) -> type[ViewerSlot]:
        return cls.slot_for_roles(axis.roles)

    @classmethod
    def named(cls, wire_value: object) -> type[ViewerSlot]:
        for slot in cls.slots:
            if slot.wire_value == wire_value:
                return slot
        raise ValueError(
            f"{wire_value!r} is not a {cls.__name__} slot; "
            f"slots are {[slot.wire_value for slot in cls.slots]!r}."
        )

    @classmethod
    @cache
    def choice_enum(cls, name: str, module: str) -> type[Enum]:
        """The form-choice view of this family (members named after the slots' wire values)."""

        choices = Enum(
            name,
            [(slot.wire_value.upper(), slot.wire_value) for slot in cls.slots],
            module=module,
        )
        choices.__doc__ = cls.__doc__.splitlines()[0]
        return choices


class NapariSlots(ViewerSlotFamily):
    """Napari places each axis on a stacked dims slider or in separate layers."""

    class Layer(ViewerSlot):
        wire_value = "layer"
        separates_values = True

    class Stack(ViewerSlot):
        wire_value = "stack"

    default_slot = Stack


class FijiSlots(ViewerSlotFamily):
    """ImageJ hyperstack C, Z and T, or a separate window per value.

    Several axes in one slot combine their values in declared order.
    """

    class Window(ViewerSlot):
        wire_value = "window"
        separates_values = True

    class HyperstackChannel(ViewerSlot):
        wire_value = "channel"
        roles = (ColourAxis,)

    class HyperstackSlice(ViewerSlot):
        wire_value = "slice"
        roles = (StackAxis,)

    class HyperstackFrame(ViewerSlot):
        wire_value = "frame"
        roles = (TimeAxis,)

    default_slot = HyperstackFrame


# ---------------------------------------------------------------------------
# Viewer-specific display settings (the non-axis part of a display config)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ViewerDisplaySettings(AnnotatedDataclassValidationMixin):
    """Display settings one viewer reads from a stream's display config.

    Each direct subclass is one viewer's settings: its fields are the wire
    keys, and it names the viewer's slot family.
    """

    slot_family: ClassVar[type[ViewerSlotFamily]]
    _viewer_settings: ClassVar[list[type["ViewerDisplaySettings"]]] = []

    def __init_subclass__(cls, **kwargs: object) -> None:
        super().__init_subclass__(**kwargs)
        if ViewerDisplaySettings in cls.__bases__:
            ViewerDisplaySettings._viewer_settings.append(cls)

    @classmethod
    def settings_type(cls) -> type["ViewerDisplaySettings"]:
        """The viewer settings class this class is or inherits."""

        return next(
            base for base in cls.__mro__ if base in ViewerDisplaySettings._viewer_settings
        )

    @classmethod
    def from_display_payload(cls, payload: Mapping[str, ViewerWireValue]):
        settings_type = cls.settings_type()
        names = tuple(declared.name for declared in fields(settings_type))
        missing = tuple(name for name in names if name not in payload)
        if missing:
            raise ValueError(
                f"{settings_type.__name__} display config is missing {missing!r}."
            )
        return dataclass_from_mapping(
            settings_type, {name: payload[name] for name in names}
        )

    def settings_wire_mapping(self) -> ViewerWireMapping:
        return ViewerWirePayload.mapping(
            {
                declared.name: getattr(self, declared.name)
                for declared in fields(self.settings_type())
            },
            context=f"{type(self).__name__} display settings",
        )


class NapariVariableSizeHandling(Enum):
    """How to handle images with different sizes in the same layer."""

    SEPARATE_LAYERS = "separate_layers"
    PAD_TO_MAX = "pad_to_max"


@dataclass(frozen=True)
class NapariDisplaySettings(ViewerDisplaySettings):
    slot_family = NapariSlots

    colormap: NonBlankString = field(
        default="gray",
        metadata={
            "description": (
                "Name of a colormap registered in the installed Napari viewer. "
                "Napari validates this extensible registry name when displaying "
                "the layer."
            )
        },
    )
    variable_size_handling: NapariVariableSizeHandling = field(
        default=NapariVariableSizeHandling.PAD_TO_MAX,
        metadata={
            "description": (
                "How Napari handles streamed images with different spatial "
                "dimensions: preserve each shape in separate layers or pad "
                "smaller images to the largest shape before stacking."
            )
        },
    )


@dataclass(frozen=True)
class FijiDisplaySettings(ViewerDisplaySettings):
    slot_family = FijiSlots

    lut: NonBlankString = field(
        default="Grays",
        metadata={
            "description": (
                "Name of a lookup table available to the installed Fiji/ImageJ "
                "runtime, including plugin-provided LUTs."
            )
        },
    )
    auto_contrast: bool = field(
        default=True,
        metadata={
            "description": (
                "Automatically set Fiji display limits from the streamed image data."
            )
        },
    )
