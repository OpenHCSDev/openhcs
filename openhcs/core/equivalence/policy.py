"""Runtime equivalence policy records."""

from __future__ import annotations

from collections.abc import Callable, Iterable
from dataclasses import dataclass, field
from enum import Enum
from typing import Annotated, get_args, get_origin, get_type_hints

from openhcs.core.measurement_dialect import MeasurementDialect, PlainMeasurementDialect
from openhcs.core.runtime_identifier import normalize_runtime_identifier
from openhcs.core.runtime_measurements import MeasurementScope


class RuntimeMeasurementFeatureNameMode(str, Enum):
    """How measurement feature names are canonicalized for semantic comparison."""

    FULL = "full"
    SEMANTIC_CORE = "semantic_core"


@dataclass(frozen=True, slots=True)
class _NonNegativeRuntimePolicyField:
    """Type annotation marker for non-negative numeric policy fields."""


NonNegativeFloat = Annotated[float, _NonNegativeRuntimePolicyField()]
NonNegativeInt = Annotated[int, _NonNegativeRuntimePolicyField()]


class RuntimePolicyNonNegativeFieldValidationMixin:
    """Nominal owner for runtime-policy annotation invariants."""

    def validate_non_negative_policy_fields(self) -> None:
        """Validate numeric invariants declared directly on dataclass annotations."""
        owner_type = type(self)
        for field_name, annotation in get_type_hints(
            owner_type,
            include_extras=True,
        ).items():
            if get_origin(annotation) is not Annotated:
                continue
            if not any(
                isinstance(metadata, _NonNegativeRuntimePolicyField)
                for metadata in get_args(annotation)[1:]
            ):
                continue
            if object.__getattribute__(self, field_name) < 0:
                raise ValueError(
                    f"{owner_type.__name__}.{field_name} cannot be negative."
                )


@dataclass(frozen=True, slots=True)
class RuntimeMeasurementFeatureNumericTolerance(
    RuntimePolicyNonNegativeFieldValidationMixin
):
    """Numeric tolerance scoped to a semantic measurement feature family."""

    feature_name_prefixes: tuple[str, ...] = ()
    feature_name_suffixes: tuple[str, ...] = ()
    feature_names: frozenset[str] = frozenset()
    subject_scope: MeasurementScope | None = None
    statistic: str | None = None
    numeric_abs_tolerance: NonNegativeFloat = 0.0
    numeric_rel_tolerance: NonNegativeFloat = 0.0
    require_object_count_stability: bool = False

    def __post_init__(self) -> None:
        feature_name_prefixes = tuple(
            str(prefix).strip()
            for prefix in self.feature_name_prefixes
            if str(prefix).strip()
        )
        feature_name_suffixes = tuple(
            str(suffix).strip()
            for suffix in self.feature_name_suffixes
            if str(suffix).strip()
        )
        feature_names = frozenset(
            str(feature_name).strip()
            for feature_name in self.feature_names
            if str(feature_name).strip()
        )
        if (
            not feature_name_prefixes
            and not feature_name_suffixes
            and not feature_names
        ):
            raise ValueError(
                "RuntimeMeasurementFeatureNumericTolerance requires at least "
                "one feature name, prefix, or suffix."
            )
        subject_scope = (
            self.subject_scope
            if self.subject_scope is None
            or isinstance(self.subject_scope, MeasurementScope)
            else MeasurementScope(self.subject_scope)
        )
        statistic = (
            normalize_runtime_identifier(self.statistic)
            if self.statistic is not None
            else None
        )
        if statistic == "":
            raise ValueError(
                "RuntimeMeasurementFeatureNumericTolerance.statistic cannot be empty."
            )
        self.validate_non_negative_policy_fields()
        object.__setattr__(self, "feature_name_prefixes", feature_name_prefixes)
        object.__setattr__(self, "feature_name_suffixes", feature_name_suffixes)
        object.__setattr__(self, "feature_names", feature_names)
        object.__setattr__(self, "subject_scope", subject_scope)
        object.__setattr__(self, "statistic", statistic)


@dataclass(frozen=True, slots=True)
class RuntimeEquivalencePolicy(RuntimePolicyNonNegativeFieldValidationMixin):
    """Policy controlling semantic output comparison strictness."""

    numeric_decimal_places: NonNegativeInt = 10
    numeric_abs_tolerance: NonNegativeFloat = 0.0
    numeric_rel_tolerance: NonNegativeFloat = 0.0
    allow_tie_sensitive_location_mismatches: bool = False
    allow_unstable_shape_descriptors: bool = False
    shape_descriptor_abs_tolerance: NonNegativeFloat = 1e-6
    shape_descriptor_rel_tolerance: NonNegativeFloat = 0.0
    shape_descriptor_max_unstable_values: NonNegativeInt = 2
    shape_descriptor_max_unstable_fraction: NonNegativeFloat = 0.01
    threshold_entropy_abs_tolerance: NonNegativeFloat = 0.0
    threshold_sensitive_pair_abs_tolerance: NonNegativeFloat = 0.0
    threshold_sensitive_pair_rel_tolerance: NonNegativeFloat = 0.0
    allow_sparse_object_boundary_jitter: bool = False
    object_boundary_jitter_abs_tolerance: NonNegativeFloat = 25.0
    object_boundary_jitter_rel_tolerance: NonNegativeFloat = 0.0
    object_boundary_jitter_max_unstable_values: NonNegativeInt = 25
    object_boundary_jitter_max_unstable_fraction: NonNegativeFloat = 0.01
    object_boundary_jitter_aggregate_abs_tolerance: NonNegativeFloat = 0.05
    object_boundary_jitter_aggregate_rel_tolerance: NonNegativeFloat = 0.0
    compare_table_values: bool = True
    compare_image_pixels: bool = True
    image_abs_tolerance: NonNegativeFloat = 0.0
    image_rel_tolerance: NonNegativeFloat = 0.0
    image_max_different_fraction: NonNegativeFloat = 0.0
    allow_extra_candidate_measurements: bool = True
    measurement_feature_name_mode: RuntimeMeasurementFeatureNameMode = (
        RuntimeMeasurementFeatureNameMode.SEMANTIC_CORE
    )
    measurement_dialect: MeasurementDialect = field(
        default_factory=PlainMeasurementDialect.shared
    )
    feature_numeric_tolerances: tuple[
        RuntimeMeasurementFeatureNumericTolerance, ...
    ] = ()
    feature_numeric_tolerances_provider: (
        Callable[[], Iterable[RuntimeMeasurementFeatureNumericTolerance]] | None
    ) = None

    def __post_init__(self) -> None:
        self.validate_non_negative_policy_fields()
        object.__setattr__(
            self,
            "measurement_feature_name_mode",
            (
                self.measurement_feature_name_mode
                if isinstance(
                    self.measurement_feature_name_mode,
                    RuntimeMeasurementFeatureNameMode,
                )
                else RuntimeMeasurementFeatureNameMode(
                    self.measurement_feature_name_mode
                )
            ),
        )
        if not isinstance(self.measurement_dialect, MeasurementDialect):
            raise TypeError(
                "RuntimeEquivalencePolicy.measurement_dialect must be "
                f"MeasurementDialect, got {type(self.measurement_dialect).__name__}."
            )
        object.__setattr__(
            self,
            "feature_numeric_tolerances",
            tuple(
                (
                    tolerance
                    if isinstance(
                        tolerance,
                        RuntimeMeasurementFeatureNumericTolerance,
                    )
                    else RuntimeMeasurementFeatureNumericTolerance(**tolerance)
                )
                for tolerance in self.feature_numeric_tolerances
            ),
        )
        if self.feature_numeric_tolerances_provider is not None and not callable(
            self.feature_numeric_tolerances_provider
        ):
            raise TypeError(
                "RuntimeEquivalencePolicy.feature_numeric_tolerances_provider "
                "must be callable."
            )

    def resolved_feature_numeric_tolerances(
        self,
    ) -> tuple[RuntimeMeasurementFeatureNumericTolerance, ...]:
        """Return static and provider-supplied feature numeric tolerances."""
        provider = self.feature_numeric_tolerances_provider
        provided = () if provider is None else provider()
        return tuple(
            (
                tolerance
                if isinstance(tolerance, RuntimeMeasurementFeatureNumericTolerance)
                else RuntimeMeasurementFeatureNumericTolerance(**tolerance)
            )
            for tolerance in (*self.feature_numeric_tolerances, *provided)
        )
