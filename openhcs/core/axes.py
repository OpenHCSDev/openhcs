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
from collections.abc import Callable
from dataclasses import dataclass
from typing import ClassVar, TypeGuard

from metaclass_registry import AutoRegisterMeta


class AxisDeclarationMeta(AutoRegisterMeta):
    """Metaclass for axis declarations: classes that are values.

    Axis classes travel through configs, logs and placeholders as values, so
    their ``repr`` is their declared qualified name rather than ``<class …>``.
    """

    def __init__(cls, name, bases, namespace, **kwargs) -> None:
        # Declarations are checked once the class is complete. Raising from
        # ``__init_subclass__`` would leave a half-built ABC subclass whose
        # inherited subclass-check state makes unrelated axes pass role checks.
        super().__init__(name, bases, namespace, **kwargs)
        validate = getattr(cls, "_validate_declaration", None)
        if validate is not None:
            validate()

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


class GridAddressed(AxisRole):
    """Values sit on a two-dimensional grid of rows and columns.

    The axis declares how one value spells its row and column and how row and
    column labels map to one-based grid positions; views lay the axis out as a
    grid only when the family has an axis with this role.
    """

    cardinality = AtMostOne

    default_grid: ClassVar[tuple[int, int]]
    """(rows, columns) shown when no value places the grid's extent."""

    @classmethod
    def grid_coordinates(cls, value: object) -> tuple[str, str]:
        """(row label, column label) of one value."""

        raise NotImplementedError(f"{cls.__qualname__} must declare grid_coordinates.")

    @classmethod
    def grid_position(cls, row_label: str, column_label: str) -> tuple[int, int]:
        """One-based (row, column) position of a row and column label."""

        raise NotImplementedError(f"{cls.__qualname__} must declare grid_position.")

    @classmethod
    def row_label(cls, row: int) -> str:
        """Label of the one-based ``row``."""

        raise NotImplementedError(f"{cls.__qualname__} must declare row_label.")

    @classmethod
    def grid_index(cls, value: object) -> tuple[int, int] | None:
        """One-based (row, column) position of one value; None if it has none."""

        try:
            return cls.grid_position(*cls.grid_coordinates(value))
        except ValueError:
            return None


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
# Source-metadata fallbacks: the value an axis takes when metadata lacks it
# ---------------------------------------------------------------------------


MetadataLookup = Callable[[str], "str | None"]
"""Return the source-metadata value stored under one alias, if any."""


class AxisValueFallback(ABC):
    """How an axis gets a value when no source-metadata alias carries one."""

    @abstractmethod
    def value(
        self,
        *,
        image_set_index: int,
        has_value: Callable[[type[Axis]], bool],
    ) -> str:
        """Fallback value for one source image set."""


@dataclass(frozen=True)
class FirstOrdinal(AxisValueFallback):
    """The axis is singleton: every image set takes ``"1"``."""

    def value(self, *, image_set_index, has_value) -> str:
        del image_set_index, has_value
        return "1"


@dataclass(frozen=True)
class ImageSetOrdinal(AxisValueFallback):
    """Each image set is its own value, numbered from 1."""

    def value(self, *, image_set_index, has_value) -> str:
        del has_value
        return str(image_set_index + 1)


@dataclass(frozen=True)
class ImageSetOrdinalUnlessIndexedBy(AxisValueFallback):
    """Image-set ordinal, unless an axis with one of ``roles`` indexes the set."""

    roles: tuple[type[AxisRole], ...]

    def value(self, *, image_set_index, has_value) -> str:
        if any(
            has_value(axis)
            for role in self.roles
            for axis in AxisFamily.active().with_role(role)
        ):
            return "1"
        return str(image_set_index + 1)


@dataclass(frozen=True)
class ConstantValue(AxisValueFallback):
    """Every image set takes one declared value."""

    constant: str

    def value(self, *, image_set_index, has_value) -> str:
        del image_set_index, has_value
        return self.constant


# ---------------------------------------------------------------------------
# Grouping declarations: an axis, or the explicit absence of grouping
# ---------------------------------------------------------------------------


class GroupingDeclaration(ABC, metaclass=AxisDeclarationMeta):
    """What a step's ``group_by`` holds: one axis, or :class:`Ungrouped`.

    Declarations register under their boundary ``name``, which is therefore
    also their JSON spelling. Boundaries decode names through the active family
    (``AxisFamily.named``), never through this registry: two families may
    declare the same name.
    """

    __registry_key__ = "name"
    __skip_if_no_key__ = True

    name: ClassVar[str]

    @classmethod
    @abstractmethod
    def grouping_axes(cls) -> tuple[type[Axis], ...]:
        """The axes whose values partition an assembled value (empty: none)."""


class Axis(GroupingDeclaration):
    """One declared axis. Subclasses are nested in an :class:`AxisFamily`."""

    name: ClassVar[str]
    family: ClassVar[type[AxisFamily]]
    filename_prefix: ClassVar[str | None] = None
    """Token before this axis's value in plane filenames (variable axes)."""
    filename_padding: ClassVar[int] = 0
    """Zero padding for ordinal values in plane filenames."""
    label: ClassVar[str]
    """Short human-facing name, for example a viewer axis label (default: title-cased name)."""
    metadata_aliases: ClassVar[tuple[str, ...]]
    """Source-metadata field spellings that carry this axis (default: its name)."""
    metadata_collection_field: ClassVar[str]
    """Key of this axis's value-label collection in dataset metadata (default: plural name)."""
    metadata_fallback: ClassVar[AxisValueFallback] = FirstOrdinal()
    """Value an image set takes when its metadata carries none of the aliases."""

    sort_key: ClassVar  # supplied by the axis's AxisValueKind
    normalize_value: ClassVar  # supplied by the axis's AxisValueKind

    @classmethod
    def _validate_declaration(cls) -> None:
        if "_validate_declaration" in cls.__dict__:
            return  # the declaring base itself
        if "name" not in cls.__dict__:
            raise TypeError(f"Axis {cls.__qualname__} must declare its boundary name.")
        if "label" not in cls.__dict__:
            cls.label = cls.name.replace("_", " ").title()
        kinds = [base for base in cls.__mro__ if AxisValueKind in base.__bases__]
        if len(kinds) != 1:
            raise TypeError(
                f"Axis {cls.__qualname__} must carry exactly one AxisValueKind; "
                f"found {[kind.__name__ for kind in kinds]}."
            )
        if issubclass(cls, GridAddressed):
            undeclared = [
                member
                for member in ("default_grid", "grid_coordinates", "grid_position", "row_label")
                if not any(member in base.__dict__ for base in cls.__mro__ if base is not GridAddressed)
            ]
            if undeclared:
                raise TypeError(
                    f"Grid axis {cls.__qualname__} must declare {', '.join(undeclared)}."
                )
        if "metadata_aliases" not in cls.__dict__:
            cls.metadata_aliases = (cls.name,)
        if "metadata_collection_field" not in cls.__dict__:
            cls.metadata_collection_field = f"{cls.name}s"

    def __new__(cls, *args: object, **kwargs: object):
        raise TypeError(f"{cls.__qualname__} is an axis declaration, not a value type.")

    @classmethod
    def grouping_axes(cls) -> tuple[type[Axis], ...]:
        return (cls,)

    @classmethod
    def has_role(cls, role: type[AxisRole]) -> bool:
        return issubclass(cls, role)

    @classmethod
    def metadata_value(cls, lookup: MetadataLookup) -> str | None:
        """This axis's value from source metadata: the first alias present."""

        for alias in cls.metadata_aliases:
            value = lookup(alias)
            if value is not None:
                return value
        return None

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
    config_modules: ClassVar[tuple[str, ...]] = ()
    """Modules declaring this domain's global-config sections.

    Imported by the kernel config module before its fields are injected, so
    they must import nothing beyond the config decorator they use.
    """
    extension_modules: ClassVar[tuple[str, ...]] = ()
    """Modules that register this domain's members of kernel families.

    Kernel families that domains extend (dataset sources, filename parsers,
    post-execute hooks, dataset root rules) import these on first registry
    access, so activation itself stays free of domain imports.
    """
    payload_spatial_rank: ClassVar[int]
    """Spatial rank of a payload that declares no spatial domain of its own.

    Each family declares it: an undeclared array of rank r has r - k leading
    undeclared axes and k trailing spatial axes, named by the spatial domain
    of rank k.
    """

    _active: ClassVar[type[AxisFamily] | None] = None

    @classmethod
    def _validate_declaration(cls) -> None:
        if "_validate_declaration" in cls.__dict__:
            return  # the declaring base itself
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
        spatial_rank = cls.__dict__.get("payload_spatial_rank")
        if not isinstance(spatial_rank, int) or isinstance(spatial_rank, bool) or spatial_rank < 0:
            raise TypeError(
                f"Axis family {cls.__qualname__} must declare payload_spatial_rank "
                "as a nonnegative int."
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
    "AxisValueFallback",
    "ConstantValue",
    "FirstOrdinal",
    "ImageSetOrdinal",
    "ImageSetOrdinalUnlessIndexedBy",
    "MetadataLookup",
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
    "GridAddressed",
    "GroupingDeclaration",
    "LabelValued",
    "Many",
    "OrdinalValued",
    "PartitionAxis",
    "StackAxis",
    "TileAxis",
    "TimeAxis",
    "Ungrouped",
    "is_axis",
    "is_grouping_declaration",
]
