"""Typed component-group scope shared by compilation and runtime execution."""

from __future__ import annotations

from collections.abc import Hashable, Iterable, Mapping, Sequence
from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import TYPE_CHECKING, ClassVar

from openhcs.core.component_set import ComponentSet
from openhcs.core.source_metadata import (
    SourceMetadataFields,
    SourceMetadataMapping,
    SourceMetadataScalar,
)
from openhcs.core.axes import Axis, AxisFamily, PartitionAxis, is_axis

if TYPE_CHECKING:
    from openhcs.core.context.processing_context import ProcessingContext
    from openhcs.core.source_matching import (
        SourceAxisMetadataScope,
        SourceImageSetIdentity,
        SourceImageSetIdentityPolicy,
    )

ComponentGroupKey = str | None
RuntimeFixedComponentValues = tuple[tuple[type[Axis], str], ...]


class ComponentGroupScope(ABC):
    """Which component groups one execution or artifact covers.

    Each variant is a subclass: ``UngroupedScope`` (one default group),
    ``DynamicGroupScope`` (groups of one axis discovered at run time),
    ``StaticGroupScope`` (several groups named at compile time) and
    ``SingleKeyScope`` (exactly one named group).
    """

    __slots__ = ()

    component: type[Axis] | None
    keys: tuple[ComponentGroupKey, ...]
    has_compiled_keys: ClassVar[bool] = True
    names_several_keys: ClassVar[bool] = False

    @staticmethod
    def of(
        group_keys: Iterable[Hashable | None],
        component: type[Axis] | None = None,
    ) -> "ComponentGroupScope":
        """Read a scope from its raw spelling: group keys plus a component."""

        keys = tuple(
            dict.fromkeys(ComponentGroupScope.normalize_key(key) for key in group_keys)
        )
        if component is None:
            if keys not in ((), (None,)):
                raise ValueError(
                    "Concrete component-group keys require a component identity."
                )
            return UngroupedScope()
        axis = AxisFamily.active().require(component)
        if keys in ((), (None,)):
            return DynamicGroupScope(axis)
        if None in keys:
            raise ValueError(
                "ComponentGroupScope may use None only as the sole dynamic or "
                "ungrouped key."
            )
        if len(keys) == 1:
            return SingleKeyScope(axis, keys[0])
        return StaticGroupScope(axis, keys)

    @staticmethod
    def normalize_key(key: Hashable | None) -> ComponentGroupKey:
        if key is None:
            return None
        return str(key)

    @classmethod
    def one_per_component(
        cls,
        scopes: Iterable["ComponentGroupScope"],
        *,
        owner: str,
    ) -> tuple["GroupedScope", ...]:
        """Allow one consistent grouped scope per component."""
        by_component: dict[type[Axis], GroupedScope] = {}
        for scope in scopes:
            grouped = scope.require_grouped(owner)
            existing = by_component.get(grouped.component)
            if existing is not None and existing != grouped:
                raise ValueError(
                    f"{owner} declares conflicting scopes for component "
                    f"{grouped.component.name!r}: {existing!r} and {grouped!r}."
                )
            by_component[grouped.component] = grouped
        return tuple(by_component.values())

    @staticmethod
    def union_compatible(
        scopes: Sequence["ComponentGroupScope"],
    ) -> "ComponentGroupScope | None":
        """Union scopes of one component; None when their components differ."""

        if not scopes:
            return None
        component = scopes[0].component
        if any(scope.component is not component for scope in scopes[1:]):
            return None
        if not all(scope.has_compiled_keys for scope in scopes):
            return DynamicGroupScope(component)
        return ComponentGroupScope.of(
            (key for scope in scopes for key in scope.keys),
            component,
        )

    def missing_from(
        self,
        producer_scope: "ComponentGroupScope",
    ) -> list[ComponentGroupKey]:
        """Return this scope's keys the producer does not plan."""
        return [key for key in self.keys if key not in producer_scope.keys]

    def single_key(self) -> str | None:
        """Return the one compiler-known coordinate of a single-key scope."""
        return None

    def require_single_key(self) -> str:
        raise ValueError(
            f"A single static component key is required, got {self!r}."
        )

    @abstractmethod
    def as_grouped(self) -> tuple["GroupedScope", ...]:
        """Return this scope when it groups by a component, else nothing."""

    def require_grouped(self, owner: str) -> "GroupedScope":
        raise ValueError(f"{owner} component scopes cannot be ungrouped.")

    def groups_by(self, component: type[Axis] | None) -> bool:
        """Whether this scope groups by ``component``."""
        return False

    @abstractmethod
    def runtime_keys(
        self,
        discovered_keys: Iterable[Hashable | None],
    ) -> tuple[ComponentGroupKey, ...]:
        """Resolve concrete execution keys from this compiler-owned scope."""

    @abstractmethod
    def candidate_keys(
        self, runtime_value: str | None
    ) -> tuple[ComponentGroupKey, ...]:
        """Return the keys one observed coordinate can execute under."""

    @abstractmethod
    def contains_runtime_key(self, key: Hashable | None) -> bool:
        """Return whether one concrete invocation belongs to this scope."""

    @abstractmethod
    def contains_scope(self, required: "ComponentGroupScope") -> bool:
        """Return whether every invocation in ``required`` is available here."""

    def lies_within_keys(self, keys: tuple[str, ...]) -> bool:
        """Whether every key of this scope is one of ``keys``."""
        return False

    @abstractmethod
    def resolve_runtime_key(
        self,
        runtime_key: Hashable | None,
    ) -> ComponentGroupKey:
        """Resolve one concrete key against this compiler-owned scope."""

    def select_runtime_key(
        self,
        runtime_key: Hashable | None,
    ) -> ComponentGroupKey:
        """Select one coordinate from this compiled scope for an invocation."""
        return self.resolve_runtime_key(runtime_key)

    def selectable_from(self, producer_scope: "ComponentGroupScope") -> bool:
        """Whether a consumer may select this scope from ``producer_scope``."""
        return producer_scope.contains_scope(self)

    def owned_by(self, invocation_scope: "ComponentGroupScope") -> bool:
        """Whether ``invocation_scope`` supplies the keys this scope selects."""
        return True

    def may_supply_key(self, component: type[Axis] | None, key: str) -> bool:
        """Whether a source of this scope can feed group ``key`` of ``component``."""
        return True

    def shared_invocation_scope(self) -> "ComponentGroupScope":
        """Scope of one callable applied across every group of this scope."""
        return self

    def excludes(self, other: "ComponentGroupScope") -> bool:
        """Whether two compiled scopes of one component share no coordinate."""
        return False

    def keys_excluded_by(self, keys: tuple[str, ...]) -> bool:
        return False

    def admits_record_key(
        self,
        execution_component: type[Axis] | None,
        component_key: ComponentGroupKey,
        record_key: str | None,
    ) -> bool:
        """Whether a producer record under ``record_key`` serves ``component_key``."""
        return True

    def value_for_plane(
        self,
        metadata: Mapping[str, object] | None,
        component: type[Axis],
    ) -> str | None:
        """Return this scope's coordinate for one projected stack plane."""
        return self.select_runtime_key(None)

    def output_lineage_scope(
        self,
        consumer_scope: "ComponentGroupScope",
        consumer_variable_components: ComponentSet,
    ) -> "ComponentGroupScope":
        """Propagate this source scope through one consumer invocation."""
        return consumer_scope


@dataclass(frozen=True, slots=True)
class UngroupedScope(ComponentGroupScope):
    """One default group: the invocation is not split by any component."""

    component: ClassVar[None] = None
    keys: ClassVar[tuple[None]] = (None,)

    def as_grouped(self) -> tuple["GroupedScope", ...]:
        return ()

    def runtime_keys(self, discovered_keys):
        return (None,)

    def candidate_keys(self, runtime_value):
        return (None,)

    def contains_runtime_key(self, key):
        return self.normalize_key(key) is None

    def contains_scope(self, required):
        return required == self

    def resolve_runtime_key(self, runtime_key):
        return None

    def select_runtime_key(self, runtime_key):
        return None


@dataclass(frozen=True, slots=True)
class GroupedScope(ComponentGroupScope):
    """Groups split along one declared component axis."""

    component: type[Axis]

    def __post_init__(self) -> None:
        if not is_axis(self.component):
            raise TypeError("ComponentGroupScope.component must be a declared axis.")

    def as_grouped(self) -> tuple["GroupedScope", ...]:
        return (self,)

    def require_grouped(self, owner: str) -> "GroupedScope":
        return self

    def groups_by(self, component: type[Axis] | None) -> bool:
        return self.component is component

    def output_lineage_scope(self, consumer_scope, consumer_variable_components):
        if self.component in consumer_variable_components:
            return consumer_scope
        if consumer_scope.groups_by(self.component) or not consumer_scope.as_grouped():
            return self
        raise ValueError(
            f"Output lineage component {self.component.name!r} is neither the "
            f"consumer group component {consumer_scope.component.name!r} nor one "
            "of its variable components."
        )

    def contains_scope(self, required):
        return required.groups_by(self.component) and self._contains_keys_of(required)

    def may_supply_key(self, component, key):
        return self.component is not component or self.contains_runtime_key(key)

    @abstractmethod
    def _contains_keys_of(self, required: ComponentGroupScope) -> bool:
        """Whether every key of ``required`` (same component) is planned here."""


@dataclass(frozen=True, slots=True)
class DynamicGroupScope(GroupedScope):
    """Groups of one component whose keys are discovered at run time."""

    keys: ClassVar[tuple[None]] = (None,)
    has_compiled_keys = False

    def runtime_keys(self, discovered_keys):
        keys = tuple(
            dict.fromkeys(
                self.normalize_key(key) for key in discovered_keys if key is not None
            )
        )
        if not keys:
            raise ValueError(
                f"Dynamic {self.component.name} execution scope requires "
                "component-grouped runtime patterns."
            )
        return keys

    def candidate_keys(self, runtime_value):
        return () if runtime_value is None else (self.normalize_key(runtime_value),)

    def contains_runtime_key(self, key):
        return self.normalize_key(key) is not None

    def _contains_keys_of(self, required):
        return True

    def resolve_runtime_key(self, runtime_key):
        normalized_key = self.normalize_key(runtime_key)
        if normalized_key is None:
            raise ValueError(
                f"Dynamic {self.component.name} component scope requires a "
                "concrete runtime key."
            )
        return normalized_key

    def selectable_from(self, producer_scope):
        return producer_scope.groups_by(self.component)

    def owned_by(self, invocation_scope):
        return invocation_scope.groups_by(self.component)

    def admits_record_key(self, execution_component, component_key, record_key):
        return self.component is not execution_component or record_key == component_key

    def value_for_plane(self, metadata, component):
        from openhcs.core.source_matching import semantic_source_metadata_value

        value = semantic_source_metadata_value(metadata, component.name)
        return None if value is None else str(value)


@dataclass(frozen=True, slots=True)
class StaticGroupScope(GroupedScope):
    """Several groups of one component named at compile time."""

    keys: tuple[str, ...]
    names_several_keys = True

    def __post_init__(self) -> None:
        GroupedScope.__post_init__(self)
        if len(self.keys) < self.minimum_key_count() or any(
            not isinstance(key, str) for key in self.keys
        ):
            raise ValueError(
                f"{type(self).__name__} keys must be at least "
                f"{self.minimum_key_count()} strings, got {self.keys!r}."
            )

    @staticmethod
    def minimum_key_count() -> int:
        return 2

    def runtime_keys(self, discovered_keys):
        return self.keys

    def candidate_keys(self, runtime_value):
        return self.keys

    def contains_runtime_key(self, key):
        return self.normalize_key(key) in self.keys

    def _contains_keys_of(self, required):
        return required.lies_within_keys(self.keys)

    def lies_within_keys(self, keys):
        return set(self.keys).issubset(keys)

    def resolve_runtime_key(self, runtime_key):
        normalized_key = self.normalize_key(runtime_key)
        if normalized_key in self.keys:
            return normalized_key
        raise ValueError(
            f"Component scope {self.component.name!r} groups {self.keys!r} do not "
            f"contain runtime key {normalized_key!r}."
        )

    def shared_invocation_scope(self):
        return DynamicGroupScope(self.component)

    def excludes(self, other):
        return other.keys_excluded_by(self.keys)

    def keys_excluded_by(self, keys):
        return set(self.keys).isdisjoint(keys)


@dataclass(frozen=True, slots=True, init=False)
class SingleKeyScope(StaticGroupScope):
    """Exactly one group of one component, named at compile time."""

    names_several_keys = False

    def __init__(self, component: type[Axis], key: str) -> None:
        object.__setattr__(self, "component", component)
        object.__setattr__(self, "keys", (key,))
        self.__post_init__()

    @staticmethod
    def minimum_key_count() -> int:
        return 1

    def single_key(self) -> str:
        return self.keys[0]

    def require_single_key(self) -> str:
        return self.keys[0]

    def select_runtime_key(self, runtime_key):
        return self.keys[0]

    def shared_invocation_scope(self):
        return self


@dataclass(frozen=True, slots=True)
class RuntimeExecutionAxisScope:
    """Typed runtime axis coordinate for component projection."""

    axis_id: str
    component: type[Axis] | None = None
    value: SourceMetadataScalar = None
    fixed_component_values: RuntimeFixedComponentValues = ()

    @classmethod
    def from_context(
        cls,
        context: "ProcessingContext",
        *,
        component: type[Axis] | str | None = None,
        value: SourceMetadataScalar = None,
    ) -> "RuntimeExecutionAxisScope":
        axis_id = context.axis_id
        if not axis_id:
            raise RuntimeError(
                "ProcessingContext.axis_id is required for runtime execution."
            )
        return cls.from_raw(
            str(axis_id),
            component=component,
            value=value,
        )

    @classmethod
    def from_raw(
        cls,
        axis_id: str,
        *,
        component: type[Axis] | None,
        value: SourceMetadataScalar,
        fixed_component_values: Iterable[
            tuple[type[Axis], SourceMetadataScalar]
        ] = (),
    ) -> "RuntimeExecutionAxisScope":
        if not axis_id:
            raise ValueError("RuntimeExecutionAxisScope.axis_id cannot be empty.")
        resolved_component = (
            None if component is None else AxisFamily.active().require(component)
        )
        canonical_value = None if value is None else str(value)
        canonical_fixed_values = cls._canonical_fixed_component_values(
            fixed_component_values,
            group_component=resolved_component,
        )
        return cls(
            axis_id=str(axis_id),
            component=resolved_component,
            value=canonical_value,
            fixed_component_values=canonical_fixed_values,
        )

    def __post_init__(self) -> None:
        if not self.axis_id:
            raise ValueError("RuntimeExecutionAxisScope.axis_id cannot be empty.")
        if self.component is not None and not is_axis(self.component):
            raise TypeError(
                "RuntimeExecutionAxisScope.component must be a declared axis. "
                "Use RuntimeExecutionAxisScope.from_raw() for coercion."
            )
        if (self.component is None) != (self.value is None):
            raise ValueError(
                "RuntimeExecutionAxisScope component and value must be declared "
                "together."
            )
        if self.value is not None and not isinstance(self.value, str):
            raise TypeError(
                "RuntimeExecutionAxisScope.value must be canonical text. Use "
                "RuntimeExecutionAxisScope.from_raw() for coercion."
            )
        canonical_fixed_values = self._canonical_fixed_component_values(
            self.fixed_component_values,
            group_component=self.component,
        )
        if self.fixed_component_values != canonical_fixed_values:
            raise ValueError(
                "RuntimeExecutionAxisScope.fixed_component_values must already be "
                "canonical. Use RuntimeExecutionAxisScope.from_raw() to construct "
                "from raw coordinates."
            )

    @staticmethod
    def _canonical_fixed_component_values(
        fixed_component_values: Iterable[
            tuple[type[Axis], SourceMetadataScalar]
        ],
        *,
        group_component: type[Axis] | None,
    ) -> RuntimeFixedComponentValues:
        """Validate and order fixed coordinates before scope construction."""

        normalized_fixed_values: dict[type[Axis], str] = {}
        for component, value in fixed_component_values:
            resolved_component = AxisFamily.active().require(component)
            if issubclass(resolved_component, PartitionAxis):
                raise ValueError(
                    "RuntimeExecutionAxisScope fixed components cannot repeat the "
                    "multiprocessing axis."
                )
            if value is None:
                raise ValueError(
                    "RuntimeExecutionAxisScope fixed component values cannot be None."
                )
            if resolved_component in normalized_fixed_values:
                raise ValueError(
                    "RuntimeExecutionAxisScope fixed components cannot contain "
                    f"duplicate {resolved_component.name!r} identity."
                )
            normalized_fixed_values[resolved_component] = str(value)
        if group_component in normalized_fixed_values:
            raise ValueError(
                "RuntimeExecutionAxisScope group component cannot also be declared "
                "as a fixed component."
            )
        return tuple(
            (component, normalized_fixed_values[component])
            for component in AxisFamily.active().axes
            if component in normalized_fixed_values
        )

    @property
    def component_name(self) -> str | None:
        if self.component is None:
            return None
        return str(self.component.name)

    def require_component_name(self) -> str:
        component_name = self.component_name
        if component_name is None:
            raise ValueError("Runtime component-axis scope has no component.")
        return component_name

    @property
    def value_text(self) -> str | None:
        if self.value is None:
            return None
        return str(self.value)

    def require_value_text(self) -> str:
        value_text = self.value_text
        if value_text is None:
            raise ValueError("Runtime component-axis scope has no value.")
        return value_text

    def value_text_for_component(
        self,
        component: type[Axis] | None,
    ) -> str | None:
        """Return this runtime scope's value for one component axis."""

        if component is None:
            return None
        resolved_component = AxisFamily.active().require(component)
        if issubclass(resolved_component, PartitionAxis):
            return self.axis_id
        if self.component == resolved_component:
            return self.value_text
        for fixed_component, fixed_value in self.fixed_component_values:
            if fixed_component is resolved_component:
                return fixed_value
        return None

    @property
    def has_fixed_components(self) -> bool:
        return bool(self.fixed_component_values)

    def join_execution_cohort(
        self,
        other: "RuntimeExecutionAxisScope",
    ) -> "RuntimeExecutionAxisScope | None":
        """Join complete producer coordinates within one consumer execution group.

        An absent fixed coordinate leaves that axis unconstrained. Shared
        coordinates must agree before either correlated row contributes its
        remaining coordinates; fields from conflicting rows are never combined.
        """

        if not isinstance(other, RuntimeExecutionAxisScope):
            raise TypeError("Execution cohorts require RuntimeExecutionAxisScope values.")
        if (
            self.axis_id != other.axis_id
            or self.component is not other.component
            or self.value_text != other.value_text
        ):
            return None
        own_fixed = dict(self.fixed_component_values)
        other_fixed = dict(other.fixed_component_values)
        if any(
            own_fixed[component] != other_fixed[component]
            for component in own_fixed.keys() & other_fixed.keys()
        ):
            return None
        return type(self).from_raw(
            self.axis_id,
            component=self.component,
            value=self.value_text,
            fixed_component_values=tuple((own_fixed | other_fixed).items()),
        )

    @property
    def source_component_values(self) -> RuntimeFixedComponentValues:
        """Return every typed source coordinate represented by this scope."""

        values: list[tuple[type[Axis], str]] = []
        for component in AxisFamily.active().axes:
            value = self.value_text_for_component(component)
            if value is not None:
                values.append((component, value))
        return tuple(values)

    @property
    def presentation_component_values(self) -> RuntimeFixedComponentValues:
        """Return coordinates in a user-facing axis-first order."""

        values = self.source_component_values
        return (
            *(item for item in values if issubclass(item[0], PartitionAxis)),
            *(item for item in values if not issubclass(item[0], PartitionAxis)),
        )

    @property
    def coordinate_label(self) -> str:
        """Return a stable user-facing label without enum representations."""

        return " / ".join(
            f"{component.name}={value}"
            for component, value in self.presentation_component_values
        )

    def for_output_scope(
        self, output_scope: ComponentGroupScope
    ) -> "RuntimeExecutionAxisScope":
        """Project this execution identity onto an output's single group key."""

        key = output_scope.single_key()
        return self.for_group_coordinate(
            None if key is None else output_scope.component, key
        )

    def for_group_coordinate(
        self,
        component: type[Axis] | None,
        value: SourceMetadataScalar,
    ) -> "RuntimeExecutionAxisScope":
        """Project this execution identity onto one artifact group coordinate."""

        resolved_component = (
            None if component is None else AxisFamily.active().require(component)
        )
        if (resolved_component is None) != (value is None):
            raise ValueError(
                "Artifact group component and value must be declared together."
            )
        resolved_value = None if value is None else str(value)
        fixed_values = dict(self.fixed_component_values)
        if self.component is not None and self.component is not resolved_component:
            existing = fixed_values.get(self.component)
            if existing is not None and existing != self.require_value_text():
                raise ValueError(
                    "Runtime execution group conflicts with its fixed component "
                    f"identity for {self.component.name!r}."
                )
            fixed_values[self.component] = self.require_value_text()
        if resolved_component is not None:
            existing = fixed_values.pop(resolved_component, None)
            if existing is not None and existing != resolved_value:
                raise ValueError(
                    "Artifact group coordinate conflicts with fixed runtime identity "
                    f"for {resolved_component.name!r}: {existing!r} != "
                    f"{resolved_value!r}."
                )
            if (
                self.component is resolved_component
                and self.value_text != resolved_value
            ):
                raise ValueError(
                    "Artifact group coordinate conflicts with runtime execution group "
                    f"for {resolved_component.name!r}: {self.value_text!r} != "
                    f"{resolved_value!r}."
                )
        return type(self).from_raw(
            self.axis_id,
            component=resolved_component,
            value=resolved_value,
            fixed_component_values=tuple(fixed_values.items()),
        )

    def source_component_metadata(
        self,
        metadata: SourceMetadataMapping | None = None,
    ) -> SourceMetadataMapping:
        """Project scope coordinates while retaining an explicit measured source.

        A measurement's physical source can differ from its object's grouped
        channel. Keep that declared source coordinate; only absent group
        metadata is supplied by this scope. Axis and fixed coordinates must
        agree, and unrepresented coordinates are never invented.
        """
        from openhcs.core.source_matching import (
            source_component_metadata_value,
            with_source_component_metadata,
        )

        merged = SourceMetadataFields.composition_snapshot(
            metadata if metadata is not None else {}
        )
        for component, value in self.source_component_values:
            existing = source_component_metadata_value(merged, component)
            if component is self.component and existing is not None:
                continue
            if existing is not None and str(existing) != value:
                raise ValueError(
                    "Runtime execution scope conflicts with source component metadata "
                    f"for {component.name!r}: {existing!r} != {value!r}."
                )
            merged = with_source_component_metadata(merged, component, value)
        return merged

    @property
    def has_value(self) -> bool:
        return self.component is not None

    @property
    def group_scope(self) -> ComponentGroupScope:
        """Return this runtime coordinate as one concrete component-group scope."""
        if self.component is None:
            return UngroupedScope()
        return SingleKeyScope(self.component, self.require_value_text())

    @property
    def cache_key(self) -> tuple[tuple[str, str], ...]:
        return tuple(
            (component.name, value)
            for component, value in self.source_component_values
            if not issubclass(component, PartitionAxis)
        )

    def source_axis_metadata_scope(self) -> "SourceAxisMetadataScope":
        """Return metadata constraints for this runtime axis."""

        from openhcs.core.source_matching import SourceAxisMetadataScope

        component_values = tuple(
            (component.name, value)
            for component, value in self.source_component_values
        )
        multiprocessing_component = AxisFamily.active().partition_axis()
        if not any(
            component_name == multiprocessing_component.name
            for component_name, _value in component_values
        ):
            raise RuntimeError(
                "Runtime execution source scope is missing its multiprocessing axis."
            )
        return SourceAxisMetadataScope.from_component_values(component_values)

    def source_image_set_identity(
        self,
        policy: "SourceImageSetIdentityPolicy",
        *,
        components: ComponentSet,
    ) -> "SourceImageSetIdentity":
        """Project typed coordinates through declared image-set membership."""

        from openhcs.core.source_matching import SourceImageSetIdentity

        return SourceImageSetIdentity(
            tuple(
                (component.name, value)
                for component, value in self.source_component_values
                if component in components
                if policy.is_identity_component(component)
            )
        )

    @property
    def source_components(self) -> ComponentSet:
        """Return the typed components whose coordinates this scope declares."""

        return ComponentSet.collect(
            (component for component, _value in self.source_component_values)
        )

    def matching_component_plane_indices(
        self,
        component_metadata: Sequence[Mapping[str, object] | None],
    ) -> tuple[int, ...] | None:
        """Select payload planes owned by this scope's typed component value.

        ``None`` means the payload does not declare this component axis. A tuple
        is an exact selection, including the complete plane sequence when every
        plane belongs to the runtime scope.
        """

        if not self.has_value or not component_metadata:
            return None

        from openhcs.core.source_matching import (
            SourceAxisMetadataScope,
            semantic_source_metadata_value,
        )

        component_name = self.require_component_name()
        values = tuple(
            (
                None
                if metadata is None
                else semantic_source_metadata_value(metadata, component_name)
            )
            for metadata in component_metadata
        )
        present_values = tuple(value for value in values if value is not None)
        if not present_values:
            return None
        if len(present_values) != len(values):
            raise RuntimeError(
                "Runtime payload plane metadata only partially declares component "
                f"{component_name!r}: {values!r}."
            )

        component_scope = SourceAxisMetadataScope.from_component_values(
            ((component_name, self.require_value_text()),)
        )
        matching_indices = component_scope.matching_indices(component_metadata)
        if not matching_indices:
            raise RuntimeError(
                "Runtime payload plane metadata has no plane for execution scope "
                f"{component_name}={self.require_value_text()!r}: {values!r}."
            )
        return matching_indices
