"""Nominal feature-role semantics for runtime measurement equivalence."""

from __future__ import annotations

import math
from abc import ABC, abstractmethod
from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
from typing import TYPE_CHECKING, ClassVar

from metaclass_registry import AutoRegisterMeta, RegistryFamily, RegistryKeyAttribute

from openhcs.core.equivalence.cells import (
    RuntimeCellSignature,
    RuntimeCellValueKind,
    finite_signature_number,
    runtime_cell_signature_counters_equivalent,
    sparse_numeric_counters_equivalent,
)
from openhcs.core.equivalence.keys import (
    RuntimeMeasurementFeatureKey,
)
from openhcs.core.equivalence.policy import (
    RuntimeEquivalencePolicy,
    RuntimeMeasurementDialect,
    normalize_runtime_identifier,
    runtime_measurement_dialect_cache_id,
    runtime_measurement_dialect_for_cache_id,
)
from openhcs.core.equivalence.measurement_facts import (
    RuntimeMeasurementFactCounterMapping,
)
from openhcs.core.registry_strategies import (
    EnumKeyedStrategyMixin,
    MostDerivedContextStrategyMixin,
)
from openhcs.core.runtime_measurements import (
    MeasurementScope,
    MeasurementStatistic,
    ObjectCoreMeasurementFeature,
    ObjectCalculatedFeatureMarker,
    ObjectCountFeatureMarker,
    ObjectIdentifierFeatureMarker,
    ObjectIntensityFeatureMarker,
    ObjectLocationCoordinateProjectionStrategy,
    ObjectLocationFeatureMarker,
    ObjectShapeDescriptorFeatureMarker,
    RuntimeMeasurementFeatureRelation,
    RuntimeMeasurementFeatureSemanticMarker,
    RuntimeMeasurementFeature,
)

if TYPE_CHECKING:
    from openhcs.core.equivalence.measurement_rows import RuntimeMeasurementRowIdentity


@dataclass(frozen=True, slots=True)
class RuntimeMeasurementFeatureSemanticContext:
    """Selection context for runtime measurement feature semantic profiles."""

    key: RuntimeMeasurementFeatureKey
    policy: RuntimeEquivalencePolicy


class RuntimeMeasurementFeatureSemanticProfile(
    MostDerivedContextStrategyMixin[RuntimeMeasurementFeatureSemanticContext],
    ABC,
):
    """Registered semantic behavior for runtime measurement features."""

    __registry_family__ = RegistryFamily(RegistryKeyAttribute.STRATEGY_KEY)
    strategy_key: ClassVar[str | None] = None

    @classmethod
    def for_feature_key(
        cls,
        key: RuntimeMeasurementFeatureKey,
        policy: RuntimeEquivalencePolicy,
    ) -> "RuntimeMeasurementFeatureSemanticProfile":
        """Return the most-derived semantic profile for ``key``."""
        return cls._for_feature_key_payload(
            key.to_cache_payload(),
            runtime_measurement_dialect_cache_id(policy.measurement_dialect),
        )

    @classmethod
    @lru_cache(maxsize=32768)
    def _for_feature_key_payload(
        cls,
        key_payload: object,
        dialect_id: int,
    ) -> "RuntimeMeasurementFeatureSemanticProfile":
        """Return cached most-derived semantic profile for one key/dialect pair."""
        key = RuntimeMeasurementFeatureKey.from_cache_payload(key_payload)
        context = RuntimeMeasurementFeatureSemanticContext(
            key,
            RuntimeEquivalencePolicy(
                measurement_dialect=runtime_measurement_dialect_for_cache_id(dialect_id)
            ),
        )
        strategy = cls.for_context(
            context,
            required=False,
            error_subject=(
                "Runtime measurement feature semantic profile for " f"{key!r}"
            ),
        )
        if strategy is None:
            return DefaultRuntimeMeasurementFeatureSemanticProfile()
        return strategy

    @abstractmethod
    def values_equivalent(
        self,
        key: RuntimeMeasurementFeatureKey,
        left: object,
        right: object,
        policy: RuntimeEquivalencePolicy,
    ) -> bool:
        """Return semantic value equivalence for this feature."""

    def row_identity_stable(
        self,
        key: RuntimeMeasurementFeatureKey,
        row_identity: RuntimeMeasurementRowIdentity,
        policy: RuntimeEquivalencePolicy,
    ) -> bool:
        """Return whether this feature's row identity is stable under policy."""
        del key, row_identity, policy
        return True

    def current_object_vector(
        self,
        key: RuntimeMeasurementFeatureKey,
        label_array: object,
    ) -> object | None:
        """Return a current-object vector for ``key`` when this profile owns one."""
        del key, label_array
        return None

    def matches_marker(
        self,
        key: RuntimeMeasurementFeatureKey,
        marker_type: type[RuntimeMeasurementFeatureSemanticMarker],
        policy: RuntimeEquivalencePolicy,
    ) -> bool:
        """Return whether ``key`` carries ``marker_type`` semantics."""
        del key, marker_type, policy
        return False

    def requires_sparse_boundary_object_count_stability(
        self,
        key: RuntimeMeasurementFeatureKey,
        policy: RuntimeEquivalencePolicy,
    ) -> bool:
        """Return whether sparse-boundary comparison is gated by object count."""
        del key, policy
        return True


class MarkerRuntimeMeasurementFeatureSemanticProfile(
    RuntimeMeasurementFeatureSemanticProfile,
    ABC,
):
    """Registered semantic profile for one nominal feature marker."""

    marker_type: ClassVar[type[RuntimeMeasurementFeatureSemanticMarker]]
    subject_scope: ClassVar[MeasurementScope] = MeasurementScope.OBJECT
    statistic: ClassVar[MeasurementStatistic] = MeasurementStatistic.VALUE
    source_name_allowed: ClassVar[bool] = False

    @classmethod
    def declared_marker_types(
        cls,
    ) -> tuple[type[RuntimeMeasurementFeatureSemanticMarker], ...]:
        """Return marker declarations inherited by this semantic profile."""
        return tuple(
            dict.fromkeys(
                marker_type
                for profile_type in cls.__mro__
                if issubclass(
                    profile_type, MarkerRuntimeMeasurementFeatureSemanticProfile
                )
                and "marker_type" in profile_type.__dict__
                for marker_type in (profile_type.__dict__["marker_type"],)
            )
        )

    def values_equivalent(
        self,
        key: RuntimeMeasurementFeatureKey,
        left: object,
        right: object,
        policy: RuntimeEquivalencePolicy,
    ) -> bool:
        """Return default value equivalence for marker-owned features."""
        del key, policy
        return left == right

    def matches_marker(
        self,
        key: RuntimeMeasurementFeatureKey,
        marker_type: type[RuntimeMeasurementFeatureSemanticMarker],
        policy: RuntimeEquivalencePolicy,
    ) -> bool:
        """Return whether this profile's marker is compatible with ``marker_type``."""
        del key, policy
        if not issubclass(marker_type, RuntimeMeasurementFeatureSemanticMarker):
            raise TypeError(
                "marker_type must inherit RuntimeMeasurementFeatureSemanticMarker."
            )
        return any(
            issubclass(declared_marker_type, marker_type)
            for declared_marker_type in type(self).declared_marker_types()
        )

    def requires_sparse_boundary_object_count_stability(
        self,
        key: RuntimeMeasurementFeatureKey,
        policy: RuntimeEquivalencePolicy,
    ) -> bool:
        """Delegate sparse-boundary gating to the owned marker declaration."""
        del key, policy
        marker_types = type(self).declared_marker_types()
        if not marker_types:
            raise TypeError(
                f"{type(self).__name__} must inherit at least one marker profile."
            )
        return all(
            marker_type.requires_sparse_boundary_object_count_stability()
            for marker_type in marker_types
        )

    def matches(self, context: RuntimeMeasurementFeatureSemanticContext) -> bool:
        """Return whether ``context.key`` carries this marker profile."""
        key = context.key
        if key.subject.scope is not type(self).subject_scope:
            return False
        if key.statistic != type(self).statistic.value:
            return False
        if not type(self).source_name_allowed and key.source_name is not None:
            return False
        return self.matches_feature(context)

    @abstractmethod
    def matches_feature(
        self, context: RuntimeMeasurementFeatureSemanticContext
    ) -> bool:
        """Return whether the already-shaped key is this marker's feature."""


class RuntimeMeasurementDescriptorSemantics(RuntimeMeasurementFeatureSemanticProfile):
    """Registered equivalence profile for indexed descriptor-like features."""

    @abstractmethod
    def descriptor_identity(
        self,
        key: RuntimeMeasurementFeatureKey,
        dialect: RuntimeMeasurementDialect,
    ) -> object:
        """Return an opaque descriptor identity owned by this profile."""

    def descriptor_snapshots_comparable(
        self,
        key: RuntimeMeasurementFeatureKey,
        reference: object,
        candidate: object,
        policy: RuntimeEquivalencePolicy,
    ) -> bool:
        """Return whether two measurement snapshots can compare this descriptor."""
        del key, reference, candidate, policy
        return True


class RuntimeMeasurementIndexedDescriptorEquivalence(ABC):
    """Equivalence behavior for an indexed descriptor declaration."""

    @classmethod
    @abstractmethod
    def descriptor_values_equivalent(
        cls,
        descriptor: object,
        key: RuntimeMeasurementFeatureKey,
        left: object,
        right: object,
        policy: RuntimeEquivalencePolicy,
    ) -> bool:
        """Return value equivalence for this descriptor."""

    @classmethod
    def descriptor_row_identity_stable(
        cls,
        descriptor: object,
        key: RuntimeMeasurementFeatureKey,
        row_identity: RuntimeMeasurementRowIdentity,
        policy: RuntimeEquivalencePolicy,
    ) -> bool:
        """Return whether descriptor row identity is stable under policy."""
        del descriptor, key, row_identity, policy
        return True

    @classmethod
    def descriptor_snapshots_comparable(
        cls,
        descriptor: object,
        key: RuntimeMeasurementFeatureKey,
        reference: object,
        candidate: object,
        policy: RuntimeEquivalencePolicy,
    ) -> bool:
        """Return whether two measurement snapshots can compare this descriptor."""
        del descriptor, key, reference, candidate, policy
        return True


class DefaultRuntimeMeasurementFeatureSemanticProfile(
    RuntimeMeasurementFeatureSemanticProfile
):
    """Fallback semantic profile for ordinary measurement features."""

    strategy_key = "default"

    def matches(self, context: RuntimeMeasurementFeatureSemanticContext) -> bool:
        del context
        return False

    def values_equivalent(
        self,
        key: RuntimeMeasurementFeatureKey,
        left: object,
        right: object,
        policy: RuntimeEquivalencePolicy,
    ) -> bool:
        del key, policy
        return left == right


class ObjectCountFeatureSemanticProfile(MarkerRuntimeMeasurementFeatureSemanticProfile):
    """Core object-count feature semantics."""

    strategy_key = "object_count"
    marker_type = ObjectCountFeatureMarker
    statistic = MeasurementStatistic.COUNT

    def matches_feature(
        self, context: RuntimeMeasurementFeatureSemanticContext
    ) -> bool:
        key = context.key
        return key.feature_name == ObjectCoreMeasurementFeature.OBJECT_COUNT.value


class ObjectIdentifierFeatureSemanticProfile(
    MarkerRuntimeMeasurementFeatureSemanticProfile
):
    """Core object-identifier feature semantics."""

    strategy_key = "object_identifier"
    marker_type = ObjectIdentifierFeatureMarker

    def matches_feature(
        self, context: RuntimeMeasurementFeatureSemanticContext
    ) -> bool:
        key = context.key
        return (
            key.feature_name == ObjectCoreMeasurementFeature.OBJECT_NUMBER.value
            or key.feature_name.endswith(
                f"_{ObjectCoreMeasurementFeature.OBJECT_NUMBER.value}"
            )
        )


class ObjectLocationFeatureSemanticProfile(
    MarkerRuntimeMeasurementFeatureSemanticProfile
):
    """Core object-location feature semantics."""

    strategy_key = "object_location"
    marker_type = ObjectLocationFeatureMarker

    def matches_feature(
        self, context: RuntimeMeasurementFeatureSemanticContext
    ) -> bool:
        key = context.key
        return any(
            key.feature_name == strategy_type.axis_feature.value
            for strategy_type in (
                ObjectLocationCoordinateProjectionStrategy.registered_strategy_types()
            )
        )


class ObjectCalculatedFeatureSemanticProfile(
    MarkerRuntimeMeasurementFeatureSemanticProfile
):
    """Core calculated object-feature namespace semantics."""

    strategy_key = "object_calculated"
    marker_type = ObjectCalculatedFeatureMarker

    def matches_feature(
        self, context: RuntimeMeasurementFeatureSemanticContext
    ) -> bool:
        key = context.key
        feature_parts = tuple(part for part in key.feature_name.split("_") if part)
        return any(
            len(feature_parts) > len(prefix) and feature_parts[: len(prefix)] == prefix
            for prefix in (
                context.policy.measurement_dialect.resolved_calculated_feature_prefixes()
            )
        )


class ObjectCalculatedIdentifierFeatureSemanticProfile(
    ObjectIdentifierFeatureSemanticProfile,
    ObjectCalculatedFeatureSemanticProfile,
):
    """Identifier semantics for calculated object-identifier features."""

    strategy_key = "object_calculated_identifier"

    def matches_feature(
        self, context: RuntimeMeasurementFeatureSemanticContext
    ) -> bool:
        return ObjectIdentifierFeatureSemanticProfile.matches_feature(
            self, context
        ) and ObjectCalculatedFeatureSemanticProfile.matches_feature(self, context)


@dataclass(frozen=True, slots=True)
class TieSensitiveLocationValueFeatureRelation(RuntimeMeasurementFeatureRelation):
    """Location-feature relation gated by a stable value feature."""

    target_feature: RuntimeMeasurementFeature
    source_marker: type[RuntimeMeasurementFeatureSemanticMarker]
    target_marker: type[RuntimeMeasurementFeatureSemanticMarker]

    def __post_init__(self) -> None:
        if not self.target_marker.matches_feature(self.target_feature):
            raise ValueError(
                f"{self.target_feature!r} must carry {self.target_marker.__name__}."
            )

    def source_family_names(
        self,
        source_feature: RuntimeMeasurementFeature,
    ) -> tuple[str, ...]:
        """Return bare and marker-qualified source-family names."""
        if not self.source_marker.matches_feature(source_feature):
            raise ValueError(
                f"{source_feature!r} must carry {self.source_marker.__name__}."
            )
        return (
            source_feature.feature_family(),
            self.source_marker.qualified_family(source_feature),
        )

    def target_family_name(
        self,
        source_feature: RuntimeMeasurementFeature,
        source_family_name: str,
        feature_type: type[RuntimeMeasurementFeature],
    ) -> str | None:
        """Return the matching bare or marker-qualified target family."""
        del feature_type
        normalized_source_family = normalize_runtime_identifier(source_family_name)
        if normalized_source_family == source_feature.feature_family():
            return self.target_feature.feature_family()
        if normalized_source_family == self.source_marker.qualified_family(
            source_feature
        ):
            return self.target_marker.qualified_family(self.target_feature)
        return None


def object_measurement_feature_matches_marker(
    key: RuntimeMeasurementFeatureKey,
    marker_type: type[RuntimeMeasurementFeatureSemanticMarker],
    policy: RuntimeEquivalencePolicy,
) -> bool:
    """Return whether a runtime measurement key carries ``marker_type`` semantics."""
    if not issubclass(marker_type, RuntimeMeasurementFeatureSemanticMarker):
        raise TypeError(
            "marker_type must inherit RuntimeMeasurementFeatureSemanticMarker."
        )
    return _object_measurement_feature_matches_marker_cached(
        key.to_cache_payload(),
        marker_type,
        runtime_measurement_dialect_cache_id(policy.measurement_dialect),
    )


@lru_cache(maxsize=65536)
def _object_measurement_feature_matches_marker_cached(
    key_payload: object,
    marker_type: type[RuntimeMeasurementFeatureSemanticMarker],
    dialect_id: int,
) -> bool:
    key = RuntimeMeasurementFeatureKey.from_cache_payload(key_payload)
    policy = RuntimeEquivalencePolicy(
        measurement_dialect=runtime_measurement_dialect_for_cache_id(dialect_id)
    )
    provider_marker_types = policy.measurement_dialect.measurement_feature_marker_types(
        key
    )
    if any(
        issubclass(provider_marker_type, marker_type)
        for provider_marker_type in provider_marker_types
    ):
        return True
    profile = RuntimeMeasurementFeatureSemanticProfile.for_feature_key(key, policy)
    return profile.matches_marker(key, marker_type, policy)


def object_measurement_feature_requires_sparse_boundary_object_count_stability(
    key: RuntimeMeasurementFeatureKey,
    policy: RuntimeEquivalencePolicy | RuntimeMeasurementDialect,
) -> bool:
    """Return whether sparse-boundary equivalence for ``key`` is gated by object count."""
    if isinstance(policy, RuntimeMeasurementDialect):
        policy = RuntimeEquivalencePolicy(measurement_dialect=policy)
    provider_marker_types = policy.measurement_dialect.measurement_feature_marker_types(
        key
    )
    if provider_marker_types and any(
        marker_type.requires_sparse_boundary_object_count_stability()
        for marker_type in provider_marker_types
    ):
        return True
    profile = RuntimeMeasurementFeatureSemanticProfile.for_feature_key(key, policy)
    return profile.requires_sparse_boundary_object_count_stability(key, policy)


class SparseNumericCounterToleranceProfile(ABC, metaclass=AutoRegisterMeta):
    """Registered sparse numeric comparison tolerance profile."""

    __registry_family__ = RegistryFamily(RegistryKeyAttribute.STRATEGY_LABEL)
    __registry_key__ = "profile_key"
    __skip_if_no_key__ = True

    profile_key: ClassVar[str | None] = None

    @classmethod
    def profile_type(
        cls, profile_key: str
    ) -> type["SparseNumericCounterToleranceProfile"]:
        """Return the registered sparse numeric profile for ``profile_key``."""
        try:
            return cls.__registry__[profile_key]
        except KeyError as exc:
            registered = tuple(cls.__registry__)
            raise ValueError(
                f"Unknown sparse numeric tolerance profile {profile_key!r}; "
                f"registered profiles: {registered!r}."
            ) from exc

    @classmethod
    def profile_type_for_descriptor(
        cls,
        descriptor: object,
    ) -> type["SparseNumericCounterToleranceProfile"]:
        """Return the registered sparse numeric profile that owns ``descriptor``."""
        matches = tuple(
            profile_type
            for profile_type in cls.__registry__.values()
            if profile_type.matches_descriptor(descriptor)
        )
        if len(matches) != 1:
            names = tuple(profile_type.__name__ for profile_type in matches)
            raise ValueError(
                "Sparse numeric descriptor tolerance requires exactly one "
                f"matching profile for {descriptor!r}, got {names!r}."
            )
        return matches[0]

    @classmethod
    def matches_descriptor(cls, descriptor: object) -> bool:
        """Return whether this profile owns sparse tolerance for ``descriptor``."""
        del descriptor
        return False

    @classmethod
    def equivalent(
        cls,
        reference_values: Counter[RuntimeCellSignature],
        candidate_values: Counter[RuntimeCellSignature],
        policy: RuntimeEquivalencePolicy,
        *,
        descriptor: object | None = None,
    ) -> bool:
        """Return whether sparse numeric counters match under this profile."""
        tolerance = cls().tolerance(policy, descriptor=descriptor)
        return sparse_numeric_counters_equivalent(
            reference_values,
            candidate_values,
            policy,
            abs_tolerance=tolerance[0],
            rel_tolerance=tolerance[1],
            max_unstable_values=tolerance[2],
            max_unstable_fraction=tolerance[3],
        )

    @abstractmethod
    def tolerance(
        self,
        policy: RuntimeEquivalencePolicy,
        *,
        descriptor: object | None,
    ) -> tuple[float, float, int, float]:
        """Return sparse numeric tolerance settings."""


class ObjectBoundarySparseNumericTolerance(SparseNumericCounterToleranceProfile):
    """Object-boundary sparse jitter tolerance."""

    profile_key = "object_boundary"

    def tolerance(
        self,
        policy: RuntimeEquivalencePolicy,
        *,
        descriptor: object | None,
    ) -> tuple[float, float, int, float]:
        del descriptor
        return (
            policy.object_boundary_jitter_abs_tolerance,
            policy.object_boundary_jitter_rel_tolerance,
            policy.object_boundary_jitter_max_unstable_values,
            policy.object_boundary_jitter_max_unstable_fraction,
        )


class ShapeDescriptorSparseNumericTolerance(SparseNumericCounterToleranceProfile):
    """Shape-descriptor sparse tolerance."""

    profile_key = "shape_descriptor"

    def tolerance(
        self,
        policy: RuntimeEquivalencePolicy,
        *,
        descriptor: object | None,
    ) -> tuple[float, float, int, float]:
        del descriptor
        return (
            policy.shape_descriptor_abs_tolerance,
            policy.shape_descriptor_rel_tolerance,
            policy.shape_descriptor_max_unstable_values,
            policy.shape_descriptor_max_unstable_fraction,
        )


class BinarySparseNumericTolerance(SparseNumericCounterToleranceProfile):
    """Binary numeric sparse tolerance."""

    profile_key = "binary_numeric"

    def tolerance(
        self,
        policy: RuntimeEquivalencePolicy,
        *,
        descriptor: object | None,
    ) -> tuple[float, float, int, float]:
        del descriptor
        return (
            policy.numeric_abs_tolerance,
            policy.numeric_rel_tolerance,
            policy.object_boundary_jitter_max_unstable_values,
            policy.object_boundary_jitter_max_unstable_fraction,
        )


@dataclass(frozen=True, slots=True)
class SparseObjectBoundaryEquivalence:
    """Sparse object-boundary equivalence for object measurement features."""

    feature: RuntimeMeasurementFeatureKey
    reference: RuntimeMeasurementFactCounterMapping
    candidate: RuntimeMeasurementFactCounterMapping
    policy: RuntimeEquivalencePolicy

    def values_equivalent(self) -> bool:
        if not self.policy.allow_sparse_object_boundary_jitter:
            return False
        if self.feature.subject.scope is not MeasurementScope.OBJECT:
            return False
        if self.feature.statistic not in MeasurementStatistic._value2member_map_:
            return False
        statistic = MeasurementStatistic(self.feature.statistic)
        return SparseObjectBoundaryStatisticEquivalence.for_enum_member(
            statistic
        ).values_equivalent(self)

    def boundary_numeric_counters_equivalent(self) -> bool:
        return ObjectBoundarySparseNumericTolerance.equivalent(
            self.reference[self.feature],
            self.candidate[self.feature],
            self.policy,
        )

    def shape_descriptor_values_equivalent(self) -> bool:
        if _numeric_counters_are_binary(
            self.reference[self.feature],
            self.candidate[self.feature],
        ):
            return BinarySparseNumericTolerance.equivalent(
                self.reference[self.feature],
                self.candidate[self.feature],
                self.policy,
            )
        return self.boundary_numeric_counters_equivalent()

    def identifier_counters_equivalent(
        self,
        reference: Counter[RuntimeCellSignature],
        candidate: Counter[RuntimeCellSignature],
    ) -> bool:
        if reference == candidate:
            return True
        if any(
            signature.kind is not RuntimeCellValueKind.NUMBER for signature in reference
        ):
            return False
        if any(
            signature.kind is not RuntimeCellValueKind.NUMBER for signature in candidate
        ):
            return False

        unstable_cap = max(
            self.policy.object_boundary_jitter_max_unstable_values,
            math.ceil(
                sum(reference.values())
                * self.policy.object_boundary_jitter_max_unstable_fraction
            ),
        )
        missing = sum((reference - candidate).values())
        extra = sum((candidate - reference).values())
        return max(missing, extra) <= unstable_cap


class SparseObjectBoundaryStatisticEquivalence(
    EnumKeyedStrategyMixin[MeasurementStatistic],
    ABC,
    metaclass=AutoRegisterMeta,
):
    """Statistic-specific sparse object-boundary equivalence."""

    __registry_family__ = RegistryFamily(RegistryKeyAttribute.STRATEGY_LABEL)
    __enum_member_attr__ = "statistic"

    statistic: ClassVar[MeasurementStatistic]
    strategy_label: ClassVar[str | None] = None

    @abstractmethod
    def values_equivalent(
        self,
        context: SparseObjectBoundaryEquivalence,
    ) -> bool:
        """Return whether the statistic-specific sparse boundary values match."""


class SparseObjectBoundaryCountEquivalence(SparseObjectBoundaryStatisticEquivalence):
    """Sparse boundary equivalence for object count facts."""

    statistic = MeasurementStatistic.COUNT

    def values_equivalent(
        self,
        context: SparseObjectBoundaryEquivalence,
    ) -> bool:
        return object_measurement_feature_matches_marker(
            context.feature,
            ObjectCountFeatureMarker,
            context.policy,
        ) and _object_count_counters_sparse_equivalent(
            context.reference[context.feature],
            context.candidate[context.feature],
            context.policy,
        )


class SparseObjectBoundaryValueEquivalence(SparseObjectBoundaryStatisticEquivalence):
    """Sparse boundary equivalence for object value facts."""

    statistic = MeasurementStatistic.VALUE

    def values_equivalent(
        self,
        context: SparseObjectBoundaryEquivalence,
    ) -> bool:
        if (
            object_measurement_feature_requires_sparse_boundary_object_count_stability(
                context.feature,
                context.policy,
            )
            and not MeasurementFeatureStabilityPolicy(
                context.feature,
                context.reference,
                context.candidate,
                context.policy,
            ).object_count_values_stable()
        ):
            return False
        if object_measurement_feature_matches_marker(
            context.feature,
            ObjectIdentifierFeatureMarker,
            context.policy,
        ):
            return context.identifier_counters_equivalent(
                context.reference[context.feature],
                context.candidate[context.feature],
            )
        if any(
            object_measurement_feature_matches_marker(
                context.feature,
                marker_type,
                context.policy,
            )
            for marker_type in (
                ObjectLocationFeatureMarker,
                ObjectIntensityFeatureMarker,
                ObjectCalculatedFeatureMarker,
            )
        ):
            return context.boundary_numeric_counters_equivalent()
        if not object_measurement_feature_matches_marker(
            context.feature,
            ObjectShapeDescriptorFeatureMarker,
            context.policy,
        ):
            return False
        return context.shape_descriptor_values_equivalent()


class SparseObjectBoundaryMeanEquivalence(SparseObjectBoundaryStatisticEquivalence):
    """Sparse boundary equivalence for object mean facts."""

    statistic = MeasurementStatistic.MEAN

    def values_equivalent(
        self,
        context: SparseObjectBoundaryEquivalence,
    ) -> bool:
        value_feature = RuntimeMeasurementFeatureKey(
            subject=context.feature.subject,
            feature_name=context.feature.feature_name,
            statistic=MeasurementStatistic.VALUE.value,
            source_name=context.feature.source_name,
        )
        if value_feature not in context.reference:
            return False
        if value_feature not in context.candidate:
            return False
        if not SparseObjectBoundaryStatisticEquivalence.for_enum_member(
            MeasurementStatistic.VALUE
        ).values_equivalent(
            SparseObjectBoundaryEquivalence(
                value_feature,
                context.reference,
                context.candidate,
                context.policy,
            )
        ):
            return False

        mean_policy = RuntimeEquivalencePolicy(
            numeric_decimal_places=context.policy.numeric_decimal_places,
            numeric_abs_tolerance=context.policy.object_boundary_jitter_aggregate_abs_tolerance,
            numeric_rel_tolerance=context.policy.object_boundary_jitter_aggregate_rel_tolerance,
            measurement_feature_name_mode=context.policy.measurement_feature_name_mode,
        )
        return runtime_cell_signature_counters_equivalent(
            context.reference[context.feature],
            context.candidate[context.feature],
            mean_policy,
        )


@dataclass(frozen=True, slots=True)
class MeasurementFeatureStabilityPolicy:
    """Evaluate supporting measurement stability for feature equivalence."""

    feature: RuntimeMeasurementFeatureKey
    reference: RuntimeMeasurementFactCounterMapping
    candidate: RuntimeMeasurementFactCounterMapping
    policy: RuntimeEquivalencePolicy

    def object_count_values_stable(self) -> bool:
        count_feature = RuntimeMeasurementFeatureKey(
            subject=self.feature.subject,
            feature_name=ObjectCoreMeasurementFeature.OBJECT_COUNT.value,
            statistic=MeasurementStatistic.COUNT.value,
        )
        shared_keys = self.reference.keys() & self.candidate.keys()
        if count_feature not in shared_keys:
            return self.feature in shared_keys and sum(
                self.reference[self.feature].values()
            ) == sum(self.candidate[self.feature].values())
        return runtime_cell_signature_counters_equivalent(
            self.reference[count_feature],
            self.candidate[count_feature],
            self.policy,
        )

    def shape_descriptor_geometry_is_stable(self) -> bool:
        stable_features = self.object_measurement_marker_stable_features(
            ObjectLocationFeatureMarker,
        ) | self.object_measurement_marker_exactly_stable_features(
            ObjectShapeDescriptorFeatureMarker,
        )
        return len(stable_features) >= 3

    def object_measurement_marker_stable_features(
        self,
        marker_type: type[RuntimeMeasurementFeatureSemanticMarker],
    ) -> frozenset[RuntimeMeasurementFeatureKey]:
        stable_features: set[RuntimeMeasurementFeatureKey] = set()
        candidate_keys = self.reference.keys() & self.candidate.keys()
        for candidate_key in candidate_keys:
            if not self._candidate_key_matches_marker(candidate_key, marker_type):
                continue
            reference_values = self.reference[candidate_key]
            candidate_values = self.candidate[candidate_key]
            if not self._feature_values_stable(
                candidate_key,
                reference_values,
                candidate_values,
            ):
                continue
            stable_features.add(candidate_key)
        return frozenset(stable_features)

    def object_measurement_marker_exactly_stable_features(
        self,
        marker_type: type[RuntimeMeasurementFeatureSemanticMarker],
    ) -> frozenset[RuntimeMeasurementFeatureKey]:
        stable_features: set[RuntimeMeasurementFeatureKey] = set()
        candidate_keys = self.reference.keys() & self.candidate.keys()
        for candidate_key in candidate_keys:
            if candidate_key == self.feature:
                continue
            if not self._candidate_key_matches_marker(candidate_key, marker_type):
                continue
            reference_values = self.reference[candidate_key]
            candidate_values = self.candidate[candidate_key]
            if not runtime_cell_signature_counters_equivalent(
                reference_values,
                candidate_values,
                self.policy,
            ):
                continue
            stable_features.add(candidate_key)
        return frozenset(stable_features)

    def _feature_values_stable(
        self,
        feature: RuntimeMeasurementFeatureKey | None,
        reference_values: Counter[RuntimeCellSignature],
        candidate_values: Counter[RuntimeCellSignature],
    ) -> bool:
        if runtime_cell_signature_counters_equivalent(
            reference_values,
            candidate_values,
            self.policy,
        ):
            return True
        if feature is None:
            return False
        if not self.policy.allow_sparse_object_boundary_jitter:
            return False
        if feature.subject.scope is not MeasurementScope.OBJECT:
            return False
        if feature.statistic not in MeasurementStatistic._value2member_map_:
            return False
        return SparseObjectBoundaryStatisticEquivalence.for_enum_member(
            MeasurementStatistic(feature.statistic)
        ).values_equivalent(
            SparseObjectBoundaryEquivalence(
                feature,
                self.reference,
                self.candidate,
                self.policy,
            )
        )

    def _candidate_key_matches_marker(
        self,
        candidate_key: RuntimeMeasurementFeatureKey,
        marker_type: type[RuntimeMeasurementFeatureSemanticMarker],
    ) -> bool:
        if candidate_key.subject != self.feature.subject:
            return False
        if candidate_key.source_name is not None:
            return False
        if candidate_key.statistic != MeasurementStatistic.VALUE.value:
            return False
        return object_measurement_feature_matches_marker(
            candidate_key,
            marker_type,
            self.policy,
        )


def _object_count_counters_sparse_equivalent(
    reference: Counter[RuntimeCellSignature],
    candidate: Counter[RuntimeCellSignature],
    policy: RuntimeEquivalencePolicy,
) -> bool:
    if reference == candidate:
        return True
    if any(
        signature.kind is not RuntimeCellValueKind.NUMBER for signature in reference
    ):
        return False
    if any(
        signature.kind is not RuntimeCellValueKind.NUMBER for signature in candidate
    ):
        return False

    unstable_cap = max(
        policy.object_boundary_jitter_max_unstable_values,
        math.ceil(
            sum(reference.values())
            * policy.object_boundary_jitter_max_unstable_fraction
        ),
    )
    missing = sum((reference - candidate).values())
    extra = sum((candidate - reference).values())
    return max(missing, extra) <= unstable_cap


def _numeric_counters_are_binary(
    reference: Counter[RuntimeCellSignature],
    candidate: Counter[RuntimeCellSignature],
) -> bool:
    numbers: set[float] = set()
    for counter in (reference, candidate):
        for signature in counter:
            numeric = finite_signature_number(signature)
            if numeric is None:
                return False
            numbers.add(numeric)
    return numbers.issubset({0.0, 1.0})
