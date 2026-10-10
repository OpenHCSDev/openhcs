"""Declared data axes: the kernel's only notion of which dimensions exist.

A domain declares one :class:`AxisFamily` whose nested :class:`Axis` classes
are the axes. Each axis is a nominal class: identity is the class, membership
in a role is inheritance from an :class:`AxisRole` capability mixin, and the
behaviour the kernel needs lives on the role. The kernel never names a member;
it asks the active family by role (``AxisFamily.active().with_role(StackAxis)``).

Strings exist only at external boundaries (wire payloads, filenames, metadata,
MCP), spelled by ``Axis.name`` and decoded by ``AxisFamily.named``.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from typing import ClassVar, TypeGuard

from metaclass_registry import AutoRegisterMeta
from python_introspect import AnnotationChoices


class AxisDeclarationMeta(AutoRegisterMeta):
    """Metaclass for axis declarations: classes that are values.

    Axis classes travel through configs, logs and placeholders as values, so
    their ``repr`` is their declared qualified name rather than ``<class …>``.
    """

    def __repr__(cls) -> str:
        return cls.__qualname__

    __str__ = __repr__


# ---------------------------------------------------------------------------
# Cardinality
# ---------------------------------------------------------------------------


class Cardinality(ABC):
    """How many axes of one family may carry a role."""

    @classmethod
    @abstractmethod
    def admits(cls, count: int) -> bool:
        """Return whether ``count`` axes may carry the role."""

    @classmethod
    @abstractmethod
    def describe(cls) -> str:
        """Human-readable rule for error messages."""


class Many(Cardinality):
    @classmethod
    def admits(cls, count: int) -> bool:
        return count >= 0

    @classmethod
    def describe(cls) -> str:
        return "any number of axes"


class ExactlyOne(Cardinality):
    @classmethod
    def admits(cls, count: int) -> bool:
        return count == 1

    @classmethod
    def describe(cls) -> str:
        return "exactly one axis"


class AtMostOne(Cardinality):
    @classmethod
    def admits(cls, count: int) -> bool:
        return count <= 1

    @classmethod
    def describe(cls) -> str:
        return "at most one axis"


# ---------------------------------------------------------------------------
# Roles and value kinds (capability mixins)
# ---------------------------------------------------------------------------


class AxisRole(ABC):
    """Capability an axis carries; the kernel asks the family by role."""

    cardinality: ClassVar[type[Cardinality]] = Many


class PartitionAxis(AxisRole):
    """The parallel axis: one worker lane, filter target and reduction key per value."""

    cardinality = ExactlyOne


class StackAxis(AxisRole):
    """Ordered planes; a "plane" is one slice along this axis."""

    cardinality = AtMostOne


class ColourAxis(AxisRole):
    """Spectral or channel axis."""


class TileAxis(AxisRole):
    """Spatial tiles or fields that together cover one partition."""


class TimeAxis(AxisRole):
    """Acquisition time."""


class DefaultVariable(AxisRole):
    """Axes a step assembles along when it declares no variable axes."""


class DefaultGroupBy(AxisRole):
    """The axis a step groups by when it declares no grouping."""

    cardinality = AtMostOne


class AxisValueKind(ABC):
    """How an axis spells its values. Every axis carries exactly one kind."""

    @classmethod
    @abstractmethod
    def sort_key(cls, value: object) -> tuple[int, int | str]:
        """Order key for one axis value."""

    @classmethod
    @abstractmethod
    def normalize_value(cls, value: object) -> str:
        """Canonical text for one axis value."""


class LabelValued(AxisValueKind):
    """Values are labels compared as text (for example ``"A01"``)."""

    @classmethod
    def sort_key(cls, value: object) -> tuple[int, int | str]:
        return (1, str(value))

    @classmethod
    def normalize_value(cls, value: object) -> str:
        return str(value)


class OrdinalValued(AxisValueKind):
    """Values are ordinals; numeric text orders numerically."""

    @classmethod
    def sort_key(cls, value: object) -> tuple[int, int | str]:
        text = str(value)
        if text.isdigit():
            return (0, int(text))
        return (1, text)

    @classmethod
    def normalize_value(cls, value: object) -> str:
        text = str(value)
        return str(int(text)) if text.isdecimal() else text


# ---------------------------------------------------------------------------
# Grouping declarations: an axis, or the explicit absence of grouping
# ---------------------------------------------------------------------------


class GroupingDeclaration(ABC, metaclass=AxisDeclarationMeta):
    """What a step's ``group_by`` holds: one axis, or :class:`Ungrouped`."""

    name: ClassVar[str]

    @classmethod
    @abstractmethod
    def grouping_axes(cls) -> tuple[type[Axis], ...]:
        """The axes whose values partition an assembled value (empty: none)."""


class Axis(GroupingDeclaration):
    """One declared axis. Subclasses are nested in an :class:`AxisFamily`."""

    __registry_key__ = "axis_key"
    __skip_if_no_key__ = True

    name: ClassVar[str]
    axis_key: ClassVar[str | None] = None
    family: ClassVar[type[AxisFamily]]
    filename_prefix: ClassVar[str | None] = None
    """Token before this axis's value in plane filenames (variable axes)."""
    filename_padding: ClassVar[int] = 0
    """Zero padding for ordinal values in plane filenames."""

    sort_key: ClassVar  # supplied by the axis's AxisValueKind
    normalize_value: ClassVar  # supplied by the axis's AxisValueKind

    def __init_subclass__(cls, **kwargs: object) -> None:
        super().__init_subclass__(**kwargs)
        if "name" not in cls.__dict__:
            raise TypeError(f"Axis {cls.__qualname__} must declare its boundary name.")
        kinds = [base for base in cls.__mro__ if AxisValueKind in base.__bases__]
        if len(kinds) != 1:
            raise TypeError(
                f"Axis {cls.__qualname__} must carry exactly one AxisValueKind; "
                f"found {[kind.__name__ for kind in kinds]}."
            )

        cls.axis_key = f"{cls.__module__}:{cls.__qualname__}"

    def __new__(cls, *args: object, **kwargs: object):
        raise TypeError(f"{cls.__qualname__} is an axis declaration, not a value type.")

    @classmethod
    def grouping_axes(cls) -> tuple[type[Axis], ...]:
        return (cls,)

    @classmethod
    def has_role(cls, role: type[AxisRole]) -> bool:
        return issubclass(cls, role)

    @classmethod
    def filename_token(cls, value: object) -> str:
        """Spell one value in a plane filename."""

        if cls.filename_prefix is None:
            raise TypeError(f"Axis {cls!r} declares no filename prefix.")
        text = cls.normalize_value(value)
        if cls.filename_padding and text.isdecimal():
            text = f"{int(text):0{cls.filename_padding}d}"
        return f"{cls.filename_prefix}{text}"



class Ungrouped(GroupingDeclaration):
    """Explicit absent-grouping declaration: the step does not partition its value."""

    name = "none"

    @classmethod
    def grouping_axes(cls) -> tuple[type[Axis], ...]:
        return ()


def is_axis(value: object) -> TypeGuard[type[Axis]]:
    """Return whether ``value`` is a declared axis class."""

    return isinstance(value, type) and issubclass(value, Axis) and value is not Axis


def is_grouping_declaration(value: object) -> TypeGuard[type[GroupingDeclaration]]:
    """Return whether ``value`` is an axis or :class:`Ungrouped`."""

    return is_axis(value) or value is Ungrouped


# ---------------------------------------------------------------------------
# Families
# ---------------------------------------------------------------------------


class AxisFamilyNotActive(RuntimeError):
    """The kernel was used before a domain activated its axis family."""


class AxisFamily(metaclass=AxisDeclarationMeta):
    """A domain's declared axes, in declaration order.

    Subclasses declare their axes as nested :class:`Axis` subclasses. Role
    cardinalities are checked when the family is declared.
    """

    __registry_key__ = "family_name"
    __skip_if_no_key__ = True

    family_name: ClassVar[str | None] = None
    axes: ClassVar[tuple[type[Axis], ...]] = ()

    _active: ClassVar[type[AxisFamily] | None] = None

    def __init_subclass__(cls, **kwargs: object) -> None:
        super().__init_subclass__(**kwargs)
        declared = tuple(value for value in cls.__dict__.values() if is_axis(value))
        if not declared:
            raise TypeError(f"Axis family {cls.__qualname__} declares no axes.")
        names = [axis.name for axis in declared]
        if Ungrouped.name in names:
            raise TypeError(
                f"Axis family {cls.__qualname__} may not name an axis "
                f"{Ungrouped.name!r}; that spelling belongs to Ungrouped."
            )
        duplicates = sorted({name for name in names if names.count(name) > 1})
        if duplicates:
            raise TypeError(
                f"Axis family {cls.__qualname__} declares duplicate names {duplicates}."
            )
        for role in _declared_roles(declared):
            count = sum(1 for axis in declared if issubclass(axis, role))
            if not role.cardinality.admits(count):
                raise TypeError(
                    f"Axis family {cls.__qualname__} gives {role.__name__} to "
                    f"{count} axes; the role admits {role.cardinality.describe()}."
                )
        partition_count = sum(1 for axis in declared if issubclass(axis, PartitionAxis))
        if not PartitionAxis.cardinality.admits(partition_count):
            raise TypeError(
                f"Axis family {cls.__qualname__} must declare exactly one PartitionAxis."
            )
        for axis in declared:
            if "family" in axis.__dict__:
                raise TypeError(f"Axis {axis.__qualname__} already belongs to a family.")
            axis.family = cls
        cls.axes = declared
        cls.family_name = f"{cls.__module__}:{cls.__qualname__}"


    def __new__(cls, *args: object, **kwargs: object):
        raise TypeError(f"{cls.__qualname__} is a family declaration, not a value type.")

    # -- activation ---------------------------------------------------------

    @classmethod
    def activate(cls) -> None:
        """Make this family the process's active family."""

        if cls is AxisFamily:
            raise TypeError("Activate a declared family, not the AxisFamily base.")
        AxisFamily._active = cls

    @staticmethod
    def active() -> type[AxisFamily]:
        """Return the process's active family."""

        family = AxisFamily._active
        if family is None:
            raise AxisFamilyNotActive(
                "No axis family is active; the domain entry point must call "
                "<Family>.activate() before the kernel is used."
            )
        return family

    # -- queries ------------------------------------------------------------

    @classmethod
    def with_role(cls, role: type[AxisRole]) -> tuple[type[Axis], ...]:
        """Axes carrying ``role``, in declaration order."""

        return tuple(axis for axis in cls.axes if issubclass(axis, role))

    @classmethod
    def one(cls, role: type[AxisRole]) -> type[Axis]:
        """The single axis carrying ``role``; fails unless exactly one does."""

        matches = cls.with_role(role)
        if len(matches) != 1:
            raise LookupError(
                f"Axis family {cls.__qualname__} has {len(matches)} axes with "
                f"role {role.__name__}; exactly one is required here."
            )
        return matches[0]

    @classmethod
    def partition_axis(cls) -> type[Axis]:
        """The parallel axis."""

        return cls.one(PartitionAxis)

    @classmethod
    def variable_axes(cls) -> tuple[type[Axis], ...]:
        """Axes a step may assemble, group or sequence along (all but the partition)."""

        return tuple(axis for axis in cls.axes if not issubclass(axis, PartitionAxis))

    @classmethod
    def default_variable(cls) -> tuple[type[Axis], ...]:
        return cls.with_role(DefaultVariable)

    @classmethod
    def default_group_by(cls) -> type[GroupingDeclaration]:
        grouping = cls.with_role(DefaultGroupBy)
        return grouping[0] if grouping else Ungrouped

    @classmethod
    def grouping_choices(cls) -> tuple[type[GroupingDeclaration], ...]:
        """Every value a step's ``group_by`` may hold."""

        return (*cls.variable_axes(), Ungrouped)

    @classmethod
    def names(cls) -> tuple[str, ...]:
        """Boundary names in declaration order."""

        return tuple(axis.name for axis in cls.axes)

    @classmethod
    def grouping_named(cls, name: str) -> type[GroupingDeclaration]:
        """Decode one boundary ``group_by`` spelling (an axis name or ``"none"``)."""

        if name == Ungrouped.name:
            return Ungrouped
        return cls.named(name)

    @classmethod
    def named(cls, name: str) -> type[Axis]:
        """Decode one boundary name."""

        for axis in cls.axes:
            if axis.name == name:
                return axis
        raise ValueError(
            f"{name!r} is not an axis of {cls.__qualname__}; "
            f"declared axes are {cls.names()}."
        )

    @classmethod
    def contains(cls, axis: object) -> bool:
        return is_axis(axis) and axis in cls.axes

    @classmethod
    def require(cls, axis: object) -> type[Axis]:
        """Return ``axis`` if it is declared by this family."""

        if not cls.contains(axis):
            raise TypeError(
                f"{axis!r} is not an axis of {cls.__qualname__}; "
                f"declared axes are {cls.names()}."
            )
        return axis  # type: ignore[return-value]

    @classmethod
    def index(cls, axis: type[Axis]) -> int:
        """Declaration position of ``axis``."""

        return cls.axes.index(cls.require(axis))


# ---------------------------------------------------------------------------
# Strategy families keyed by role
# ---------------------------------------------------------------------------


class AxisRoleKeyedStrategyMixin:
    """Strategy family whose leaves each implement one axis role.

    The class that lists this mixin directly among its bases is the family
    root. Each leaf declares ``implements_role``; an axis selects the one leaf
    whose role it carries.
    """

    implements_role: ClassVar[type[AxisRole]]
    _role_strategies: ClassVar[dict[type[AxisRole], type]]

    def __init_subclass__(cls, **kwargs: object) -> None:
        super().__init_subclass__(**kwargs)
        if AxisRoleKeyedStrategyMixin in cls.__bases__:
            cls._role_strategies = {}
            return
        role = cls.__dict__.get("implements_role")
        if role is None:
            return
        existing = cls._role_strategies.get(role)
        if existing is not None:
            raise TypeError(
                f"{cls.__qualname__} and {existing.__qualname__} both implement "
                f"{role.__name__}."
            )
        cls._role_strategies[role] = cls

    @classmethod
    def role_strategy_types(cls) -> tuple[type, ...]:
        return tuple(cls._role_strategies.values())

    @classmethod
    def strategy_type_for_axis(cls, axis: type[Axis]) -> type:
        matches = tuple(
            strategy
            for role, strategy in cls._role_strategies.items()
            if issubclass(axis, role)
        )
        if len(matches) != 1:
            raise LookupError(
                f"{cls.__qualname__} needs exactly one strategy for {axis!r}; "
                f"found {[strategy.__qualname__ for strategy in matches]}."
            )
        return matches[0]

    @classmethod
    def for_axis(cls, axis: type[Axis]):
        return cls.strategy_type_for_axis(axis)()


# ---------------------------------------------------------------------------
# Choice sets for configuration fields (form and validation boundary)
# ---------------------------------------------------------------------------


class _AxisDeclarationChoices(AnnotationChoices):
    def label(self, choice: object) -> str:
        return choice.name  # type: ignore[attr-defined]

    def __eq__(self, other: object) -> bool:
        return type(self) is type(other)

    def __hash__(self) -> int:
        return hash(type(self))

    def __repr__(self) -> str:
        return f"{type(self).__name__}()"


class VariableAxisChoices(_AxisDeclarationChoices):
    """A field holding variable axes of the active family."""

    def choices(self) -> tuple[object, ...]:
        return AxisFamily.active().variable_axes()


class GroupingChoices(_AxisDeclarationChoices):
    """A field holding a grouping declaration of the active family."""

    def choices(self) -> tuple[object, ...]:
        return AxisFamily.active().grouping_choices()


def _declared_roles(axes: tuple[type[Axis], ...]) -> tuple[type[AxisRole], ...]:
    roles: list[type[AxisRole]] = []
    for axis in axes:
        for base in axis.__mro__:
            if (
                isinstance(base, type)
                and issubclass(base, AxisRole)
                and base is not AxisRole
                and base not in roles
            ):
                roles.append(base)
    return tuple(roles)


__all__ = [
    "AtMostOne",
    "Axis",
    "AxisDeclarationMeta",
    "AxisFamily",
    "AxisFamilyNotActive",
    "AxisRole",
    "AxisRoleKeyedStrategyMixin",
    "AxisValueKind",
    "Cardinality",
    "ColourAxis",
    "DefaultGroupBy",
    "DefaultVariable",
    "ExactlyOne",
    "GroupingChoices",
    "GroupingDeclaration",
    "LabelValued",
    "Many",
    "OrdinalValued",
    "PartitionAxis",
    "StackAxis",
    "TileAxis",
    "TimeAxis",
    "Ungrouped",
    "VariableAxisChoices",
    "is_axis",
    "is_grouping_declaration",
]
