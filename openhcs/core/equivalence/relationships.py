"""Relationship-derived runtime measurement projection."""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Mapping
from dataclasses import dataclass, field
from typing import ClassVar

from metaclass_registry import RegistryFamily, RegistryKeyAttribute

from openhcs.core.component_group_scope import (
    ComponentGroupScope,
    RuntimeExecutionAxisScope,
)
from openhcs.core.equivalence.keys import (
    RuntimeAggregateFeatureIdentity,
    RuntimeMeasurementFeatureKey,
)
from openhcs.core.equivalence.measurement_rows import (
    RuntimeSampleNumberOffset,
    RuntimeMeasurementRowMapping,
)
from openhcs.core.measurement_dialect import MeasurementDialect
from openhcs.core.runtime_identifier import normalize_runtime_identifier
from metaclass_registry.strategies import MostDerivedContextStrategyMixin
from openhcs.core.runtime_measurements import (
    MeasurementStatistic,
)
from openhcs.core.runtime_relationships import (
    ObjectInstanceKey,
)
from openhcs.core.runtime_tabular_values import (
    measurement_row_mapping,
)
from openhcs.core.runtime_measurements import MeasurementTable
from openhcs.core.source_image_provenance import (
    SourceImageProvenanceIdentity,
)

_ObjectInstanceChildrenByParent = Mapping[
    ObjectInstanceKey,
    tuple[ObjectInstanceKey, ...],
]


@dataclass(frozen=True, slots=True)
class RuntimeScopedMeasurementTable:
    """Measurement table plus its nominal runtime execution scope."""

    table: MeasurementTable
    record_identity: str | None = None
    execution_scope: RuntimeExecutionAxisScope | None = None
    occurrence_identity: object = field(
        default_factory=object,
        repr=False,
        compare=False,
    )

    def object_instance_key(
        self,
        row: RuntimeMeasurementRowMapping,
        object_id: int,
        *,
        sample_number_offset: RuntimeSampleNumberOffset,
    ) -> ObjectInstanceKey:
        return sample_number_offset.object_instance_key(
            row.row,
            object_id,
        )

    def object_row_occurrence_scope(
        self,
        sample_number_offset: RuntimeSampleNumberOffset,
    ) -> ComponentGroupScope | None:
        """Return group identity only when this carrier owns one local row domain."""
        if self.execution_scope is None or not self.execution_scope.has_value:
            return None

        slice_indices: set[int | None] = set()
        for raw_row in self.table.rows.iter_row_mappings():
            row = RuntimeMeasurementRowMapping(
                measurement_row_mapping(raw_row),
                object_row_identity=self.table.rows.object_row_identity,
            )
            object_id = row.object_label(
                object_id_field=self.table.subject.object_id_field
            )
            if object_id is None:
                continue
            slice_indices.add(
                self.object_instance_key(
                    row,
                    object_id,
                    sample_number_offset=sample_number_offset,
                ).slice_index
            )
            if len(slice_indices) > 1:
                return None
        return self.execution_scope.group_scope

    def image_row_occurrence_identity(
        self,
        axis_key: str | None,
        dialect: MeasurementDialect,
    ) -> tuple[str | None, SourceImageProvenanceIdentity | None]:
        """Return carrier identity only when rows do not identify a complete domain."""

        sample_identities: set[tuple[tuple[str, object], ...]] = set()
        for raw_row in self.table.rows.iter_row_mappings():
            row = RuntimeMeasurementRowMapping(
                measurement_row_mapping(raw_row),
                object_row_identity=self.table.rows.object_row_identity,
            )
            sample_identity = row.sample_identity_key(dialect)
            if not sample_identity:
                continue
            sample_identities.add(sample_identity)
            if len(sample_identities) > 1:
                return None, None
        return axis_key, self.table.source_provenance.equality_identity


@dataclass(frozen=True, slots=True)
class ObjectInstanceKeyPlaneAlignmentContext:
    """Object-instance relationship keys plus measured child value identity."""

    child_ids_by_parent: _ObjectInstanceChildrenByParent
    values_by_child_id: Mapping[ObjectInstanceKey, float]

    @property
    def child_slice_indices(self) -> frozenset[int | None]:
        return frozenset(
            child_id.slice_index
            for child_ids in self.child_ids_by_parent.values()
            for child_id in child_ids
        )

    @property
    def value_slice_indices(self) -> frozenset[int | None]:
        return frozenset(child_id.slice_index for child_id in self.values_by_child_id)

    @property
    def single_value_slice_index(self) -> int | None:
        slice_indices = self.value_slice_indices
        if len(slice_indices) != 1:
            return None
        slice_index = next(iter(slice_indices))
        return slice_index if slice_index is not None else None


class ObjectInstanceKeyPlaneAlignmentStrategy(
    MostDerivedContextStrategyMixin[ObjectInstanceKeyPlaneAlignmentContext],
    ABC,
):
    """Nominal projection between relationship and measurement-row plane identity."""

    __registry_family__ = RegistryFamily(RegistryKeyAttribute.STRATEGY_KEY)

    strategy_key: ClassVar[str | None] = None

    @classmethod
    def align_child_ids_by_parent(
        cls,
        child_ids_by_parent: _ObjectInstanceChildrenByParent,
        values_by_child_id: Mapping[ObjectInstanceKey, float],
    ) -> _ObjectInstanceChildrenByParent:
        """Align relationship child identities to the measured value domain."""
        context = ObjectInstanceKeyPlaneAlignmentContext(
            child_ids_by_parent=child_ids_by_parent,
            values_by_child_id=values_by_child_id,
        )
        strategy = cls.for_context(
            context,
            error_subject="Object instance plane alignment",
        )
        if strategy is None:
            raise ValueError("Object instance plane alignment requires a strategy.")
        return strategy.align(context)

    @abstractmethod
    def align(
        self,
        context: ObjectInstanceKeyPlaneAlignmentContext,
    ) -> _ObjectInstanceChildrenByParent:
        """Return relationship child identities projected into value identity."""


class UnmodifiedObjectInstanceKeyPlaneAlignmentStrategy(
    ObjectInstanceKeyPlaneAlignmentStrategy
):
    """Preserve relationship identity when no plane projection is required."""

    strategy_key = "unmodified"

    def matches(
        self,
        context: ObjectInstanceKeyPlaneAlignmentContext,
    ) -> bool:
        del context
        return True

    def align(
        self,
        context: ObjectInstanceKeyPlaneAlignmentContext,
    ) -> _ObjectInstanceChildrenByParent:
        return context.child_ids_by_parent


class SingleSliceValueObjectInstanceKeyPlaneAlignmentStrategy(
    UnmodifiedObjectInstanceKeyPlaneAlignmentStrategy
):
    """Inject the single measured plane into unscoped relationship identities."""

    strategy_key = "single_slice_value"

    def matches(
        self,
        context: ObjectInstanceKeyPlaneAlignmentContext,
    ) -> bool:
        return (
            context.child_slice_indices == frozenset({None})
            and context.single_value_slice_index is not None
        )

    def align(
        self,
        context: ObjectInstanceKeyPlaneAlignmentContext,
    ) -> _ObjectInstanceChildrenByParent:
        slice_index = context.single_value_slice_index
        if slice_index is None:
            raise ValueError("Single-slice alignment requires a value slice index.")
        return {
            ObjectInstanceKey(parent_id.object_id, slice_index=slice_index): tuple(
                ObjectInstanceKey(child_id.object_id, slice_index=slice_index)
                for child_id in child_ids
            )
            for parent_id, child_ids in context.child_ids_by_parent.items()
        }


class MultiSliceValueObjectInstanceKeyPlaneAlignmentStrategy(
    UnmodifiedObjectInstanceKeyPlaneAlignmentStrategy
):
    """Expand unscoped relationship identities across measured child planes."""

    strategy_key = "multi_slice_value"

    def matches(
        self,
        context: ObjectInstanceKeyPlaneAlignmentContext,
    ) -> bool:
        return (
            context.child_slice_indices == frozenset({None})
            and None not in context.value_slice_indices
            and len(context.value_slice_indices) > 1
        )

    def align(
        self,
        context: ObjectInstanceKeyPlaneAlignmentContext,
    ) -> _ObjectInstanceChildrenByParent:
        value_keys_by_object_id: dict[int, list[ObjectInstanceKey]] = {}
        for value_key in context.values_by_child_id:
            value_keys_by_object_id.setdefault(value_key.object_id, []).append(
                value_key
            )
        return {
            parent_id: tuple(
                value_key
                for child_id in child_ids
                for value_key in value_keys_by_object_id.get(child_id.object_id, ())
            )
            for parent_id, child_ids in context.child_ids_by_parent.items()
        }


class UnscopedValueObjectInstanceKeyPlaneAlignmentStrategy(
    UnmodifiedObjectInstanceKeyPlaneAlignmentStrategy
):
    """Drop relationship plane identity when measured values are unscoped."""

    strategy_key = "unscoped_value"

    def matches(
        self,
        context: ObjectInstanceKeyPlaneAlignmentContext,
    ) -> bool:
        return (
            context.value_slice_indices == frozenset({None})
            and None not in context.child_slice_indices
        )

    def align(
        self,
        context: ObjectInstanceKeyPlaneAlignmentContext,
    ) -> _ObjectInstanceChildrenByParent:
        unscoped_children_by_parent: dict[
            ObjectInstanceKey, list[ObjectInstanceKey]
        ] = {}
        for parent_id, child_ids in context.child_ids_by_parent.items():
            parent_key = ObjectInstanceKey(parent_id.object_id)
            unscoped_children_by_parent.setdefault(parent_key, []).extend(
                ObjectInstanceKey(child_id.object_id) for child_id in child_ids
            )
        return {
            parent_id: tuple(child_ids)
            for parent_id, child_ids in unscoped_children_by_parent.items()
        }


@dataclass(frozen=True, slots=True)
class RelationshipAggregateFeatureContext:
    """Semantic context for deriving parent-row aggregates from child rows."""

    source_name: str
    target_name: str
    feature_name: str
    dialect: MeasurementDialect


@dataclass(frozen=True, slots=True)
class RelationshipAggregateFeatureKeyProjection:
    """Parsed relationship aggregate measurement key."""

    feature: RuntimeMeasurementFeatureKey
    dialect: MeasurementDialect

    def resolution(self) -> "RelationshipAggregateFeatureResolution":
        aggregate_identity = RuntimeAggregateFeatureIdentity.from_parts(
            tuple(part for part in self.feature.feature_name.split("_") if part),
            self.dialect,
        )
        if aggregate_identity is None:
            return RelationshipAggregateFeatureResolution(None, None)
        context = RelationshipAggregateFeatureContext(
            source_name=self.feature.subject.name or "",
            target_name=aggregate_identity.object_name,
            feature_name=aggregate_identity.feature_name,
            dialect=self.dialect,
        )
        semantics = RelationshipAggregateFeatureSemantics.for_context(
            context,
            required=False,
        )
        if semantics is None:
            return RelationshipAggregateFeatureResolution(context, None)
        return RelationshipAggregateFeatureResolution(context, semantics)

    def aggregate_child_feature_name(self) -> str | None:
        return self.resolution().aggregate_child_feature_name()


@dataclass(frozen=True, slots=True)
class RelationshipAggregateFeatureResolution:
    """Relationship aggregate feature context with its owning semantics."""

    context: RelationshipAggregateFeatureContext | None
    semantics: "RelationshipAggregateFeatureSemantics | None"

    @property
    def is_resolved(self) -> bool:
        return self.context is not None and self.semantics is not None

    def aggregate_child_feature_name(self) -> str | None:
        if not self.is_resolved:
            return None
        assert self.context is not None
        assert self.semantics is not None
        return self.semantics.aggregate_child_feature_name(self.context)


class RelationshipAggregateFeatureSemantics(
    MostDerivedContextStrategyMixin[RelationshipAggregateFeatureContext],
    ABC,
):
    """Map child measurement features onto relationship aggregate features."""

    __registry_family__ = RegistryFamily(RegistryKeyAttribute.STRATEGY_KEY)

    strategy_key: ClassVar[str | None] = None

    @abstractmethod
    def matches(self, context: RelationshipAggregateFeatureContext) -> bool:
        """Return whether this semantic strategy owns the feature context."""

    @abstractmethod
    def required_child_feature_names(
        self,
        context: RelationshipAggregateFeatureContext,
    ) -> tuple[str, ...]:
        """Return child-row features needed to synthesize the aggregate."""

    @abstractmethod
    def aggregate_feature_name(
        self,
        context: RelationshipAggregateFeatureContext,
        *,
        aggregate: str = MeasurementStatistic.MEAN.value,
    ) -> str:
        """Return the source-row aggregate feature emitted for a child feature."""

    def aggregate_child_feature_name(
        self,
        context: RelationshipAggregateFeatureContext,
    ) -> str:
        """Return the child feature semantically represented by ``context``."""
        return normalize_runtime_identifier(context.feature_name)

    @staticmethod
    def target_aggregate_feature_name(
        target_name: str,
        child_feature_name: str,
        *,
        aggregate: str = MeasurementStatistic.MEAN.value,
    ) -> str:
        parts = (
            normalize_runtime_identifier(aggregate),
            normalize_runtime_identifier(target_name),
            normalize_runtime_identifier(child_feature_name),
        )
        return "_".join(part for part in parts if part)

    @classmethod
    def aggregate_child_feature_name_from_key(
        cls,
        feature: RuntimeMeasurementFeatureKey,
        dialect: MeasurementDialect,
    ) -> str | None:
        """Return child feature represented by a relationship aggregate key."""
        del cls
        return RelationshipAggregateFeatureKeyProjection(
            feature,
            dialect,
        ).aggregate_child_feature_name()


class GenericRelationshipAggregateFeatureSemantics(
    RelationshipAggregateFeatureSemantics
):
    """Default relationship aggregates preserve the child feature identity."""

    strategy_key = "generic"

    def matches(self, context: RelationshipAggregateFeatureContext) -> bool:
        del context
        return True

    def required_child_feature_names(
        self,
        context: RelationshipAggregateFeatureContext,
    ) -> tuple[str, ...]:
        return (normalize_runtime_identifier(context.feature_name),)

    def aggregate_feature_name(
        self,
        context: RelationshipAggregateFeatureContext,
        *,
        aggregate: str = MeasurementStatistic.MEAN.value,
    ) -> str:
        return self.target_aggregate_feature_name(
            context.target_name,
            context.feature_name,
            aggregate=aggregate,
        )

    def aggregate_child_feature_name(
        self,
        context: RelationshipAggregateFeatureContext,
    ) -> str:
        return normalize_runtime_identifier(context.feature_name)
