"""Relationship-derived runtime measurement projection."""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import ClassVar

from metaclass_registry import RegistryFamily, RegistryKeyAttribute

from openhcs.core.equivalence.keys import (
    RuntimeAggregateFeatureIdentity,
    RuntimeMeasurementFeatureKey,
)
from openhcs.core.measurement_dialect import MeasurementDialect
from openhcs.core.runtime_identifier import normalize_runtime_identifier
from metaclass_registry.strategies import MostDerivedContextStrategyMixin
from openhcs.core.runtime_measurements import (
    MeasurementStatistic,
)

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
