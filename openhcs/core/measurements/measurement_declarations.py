"""Leaf-level measurement type declarations with no SCC-member imports.

Extracted from runtime_measurements.py to break the
runtime_measurements ↔ measurement_dialect import cycle.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Iterable
from dataclasses import dataclass
from enum import Enum
from typing import ClassVar

from openhcs.core.axes.alias_property import AliasProperty
from openhcs.core.payload.runtime_identifier import normalize_runtime_identifier


# ---------------------------------------------------------------------------
# MeasurementScope
# ---------------------------------------------------------------------------

class MeasurementScope(str, Enum):
    """Semantic entity scope for measurement rows."""

    def __new__(
        cls,
        value: str,
        requires_subject_name: bool = False,
    ):
        obj = str.__new__(cls, value)
        obj._value_ = value
        obj._requires_subject_name = requires_subject_name
        return obj

    ARTIFACT = ("artifact", False)
    SAMPLE = ("sample", True)
    OBJECT = ("object", True)
    RELATIONSHIP = ("relationship", True)
    RUN = ("run", False)
    requires_subject_name = AliasProperty[bool]("_requires_subject_name")


# ---------------------------------------------------------------------------
# RuntimeMeasurementFeatureRelation family
# ---------------------------------------------------------------------------

class RuntimeMeasurementFeatureRelation(ABC):
    """Polymorphic relation declared by a runtime measurement feature member."""

    @abstractmethod
    def source_family_names(
        self, source_feature: RuntimeMeasurementFeature
    ) -> tuple[str, ...]:
        """Return feature-family names that select the relation source."""

    @abstractmethod
    def target_family_name(
        self,
        source_feature: RuntimeMeasurementFeature,
        source_family_name: str,
        feature_type: type["RuntimeMeasurementFeature"],
    ) -> str | None:
        """Return the target family for one selected source family."""


@dataclass(frozen=True)
class RuntimeMeasurementFeatureRelationDeclaration:
    """One producer-owned relation declared between measurement feature families."""

    source_feature: RuntimeMeasurementFeature
    relation: RuntimeMeasurementFeatureRelation

    def source_family_names(
        self, relation_type: type[RuntimeMeasurementFeatureRelation]
    ) -> tuple[str, ...]:
        """Return source families when this declaration belongs to ``relation_type``."""
        if not isinstance(self.relation, relation_type):
            return ()
        return self.relation.source_family_names(self.source_feature)

    def target_family_name(
        self,
        relation_type: type[RuntimeMeasurementFeatureRelation],
        source_family_name: str,
    ) -> str | None:
        """Return the target family for one source family and relation type."""
        if not isinstance(self.relation, relation_type):
            return None
        return self.relation.target_family_name(
            self.source_feature, source_family_name, type(self.source_feature)
        )


@dataclass(frozen=True)
class RuntimeMeasurementFeatureRelationDeclarationCollection:
    """Blind query surface over producer-declared feature relations."""

    declarations: tuple[RuntimeMeasurementFeatureRelationDeclaration, ...]

    def __init__(
        self, declarations: Iterable[RuntimeMeasurementFeatureRelationDeclaration]
    ) -> None:
        normalized = tuple(declarations)
        for declaration in normalized:
            if not isinstance(
                declaration, RuntimeMeasurementFeatureRelationDeclaration
            ):
                raise TypeError(
                    "RuntimeMeasurementFeatureRelationDeclarationCollection requires RuntimeMeasurementFeatureRelationDeclaration values."
                )
        object.__setattr__(self, "declarations", normalized)

    def source_family_names(
        self, relation_type: type[RuntimeMeasurementFeatureRelation]
    ) -> tuple[str, ...]:
        """Return all declared source families for one relation type."""
        return tuple(
            (
                family_name
                for declaration in self.declarations
                for family_name in declaration.source_family_names(relation_type)
            )
        )

    def target_family_name(
        self,
        relation_type: type[RuntimeMeasurementFeatureRelation],
        source_family_name: str,
    ) -> str | None:
        """Return the declared target family for one source family."""
        for declaration in self.declarations:
            target_family = declaration.target_family_name(
                relation_type, source_family_name
            )
            if target_family is not None:
                return target_family
        return None


# ---------------------------------------------------------------------------
# RuntimeMeasurementFeatureSemanticMarker family
# ---------------------------------------------------------------------------

class RuntimeMeasurementFeatureSemanticMarker(ABC):
    """Nominal marker carried by a runtime measurement feature member."""

    family_qualifier: ClassVar[str | None] = None

    @classmethod
    def matches_feature(cls, feature: RuntimeMeasurementFeature) -> bool:
        """Return whether ``feature`` carries this semantic marker."""
        return any(
            issubclass(marker_type, cls) for marker_type in feature.semantic_markers
        )

    @classmethod
    def qualified_family(cls, feature: RuntimeMeasurementFeature) -> str:
        """Return a marker-qualified feature family name."""
        if cls.family_qualifier is None:
            raise ValueError(f"{cls.__name__} does not declare family_qualifier.")
        return normalize_runtime_identifier(f"{cls.family_qualifier}_{feature.value}")

    @classmethod
    def requires_sparse_boundary_object_count_stability(cls) -> bool:
        """Return whether sparse-boundary comparison is gated by object count."""
        return True


class ObjectCountFeatureMarker(RuntimeMeasurementFeatureSemanticMarker):
    """Generic marker for object-count measurement features."""

    family_qualifier = "count"
    measurement_dtype: ClassVar[type[object]] = int


class ObjectGroupInvariantFeatureMarker(RuntimeMeasurementFeatureSemanticMarker):
    """Generic marker for object features invariant under invocation grouping."""


class ObjectReferenceFeatureMarker(ObjectGroupInvariantFeatureMarker):
    """Generic marker for measurements whose values reference object identities."""


class ObjectIdentifierFeatureMarker(ObjectReferenceFeatureMarker):
    """Generic marker for an object's own identifier measurement."""

    family_qualifier = "identifier"


class MeasuredObjectAnchorFeatureMarker(RuntimeMeasurementFeatureSemanticMarker):
    """Generic marker for features proving that an object row was measured."""

    family_qualifier = "object"


class ObjectLocationFeatureMarker(ObjectGroupInvariantFeatureMarker):
    """Generic marker for object-location measurement features."""

    family_qualifier = "location"


class ObjectIntensityFeatureMarker(RuntimeMeasurementFeatureSemanticMarker):
    """Generic marker for object-intensity measurement features."""

    family_qualifier = "intensity"


class ObjectCalculatedFeatureMarker(RuntimeMeasurementFeatureSemanticMarker):
    """Generic marker for calculated object measurement features."""

    family_qualifier = "calculated"

    @classmethod
    def requires_sparse_boundary_object_count_stability(cls) -> bool:
        """Calculated object aggregates may gain or lose missing boundary rows."""
        return False


# ---------------------------------------------------------------------------
# RuntimeMeasurementRowIdentityContract
# ---------------------------------------------------------------------------

# Default object identity fields match MeasurementRowAxisField.object_id_field_names():
# (OBJECT_LABEL, OBJECT_NUMBER, OBJECT_ID, LABEL).
_DEFAULT_OBJECT_IDENTITY_FIELDS: tuple[str, ...] = (
    "object_label",
    "object_number",
    "object_id",
    "label",
)

# Default output field matches MeasurementRowAxisField.OBJECT_LABEL.value.
_DEFAULT_OBJECT_IDENTITY_OUTPUT_FIELD: str = "object_label"


@dataclass(frozen=True)
class RuntimeMeasurementRowIdentityContract:
    """Declare row identity precedence, sample numbering and the object-ID field.

    A dialect owns one contract: which fields identify a sample row (primary
    fields win over fallbacks), which field carries the sample number, and
    which fields identify an object.
    """

    primary_sample_fields: frozenset[str] = frozenset({"slice_index"})
    fallback_sample_fields: frozenset[str] = frozenset()
    sample_number_field: str = "sample_number"
    object_identity_fields: tuple[str, ...] = _DEFAULT_OBJECT_IDENTITY_FIELDS
    object_identity_output_field: str = _DEFAULT_OBJECT_IDENTITY_OUTPUT_FIELD

    def __post_init__(self) -> None:
        primary_sample_fields = frozenset(
            normalize_runtime_identifier(field_name)
            for field_name in self.primary_sample_fields
            if str(field_name).strip()
        )
        fallback_sample_fields = frozenset(
            normalize_runtime_identifier(field_name)
            for field_name in self.fallback_sample_fields
            if str(field_name).strip()
        )
        object_identity_fields = tuple(
            dict.fromkeys(
                normalize_runtime_identifier(field_name)
                for field_name in self.object_identity_fields
                if str(field_name).strip()
            )
        )
        overlap = primary_sample_fields & fallback_sample_fields
        if overlap:
            raise ValueError(
                "RuntimeMeasurementRowIdentityContract fields must be disjoint: "
                f"{sorted(overlap)!r}."
            )
        if not object_identity_fields:
            raise ValueError(
                "RuntimeMeasurementRowIdentityContract.object_identity_fields "
                "cannot be empty."
            )
        output_field = normalize_runtime_identifier(self.object_identity_output_field)
        if not output_field:
            raise ValueError("Object identity output field must be non-empty.")
        sample_number_field = normalize_runtime_identifier(self.sample_number_field)
        if not sample_number_field:
            raise ValueError("Sample number field must be non-empty.")
        object.__setattr__(self, "object_identity_output_field", output_field)
        object.__setattr__(self, "primary_sample_fields", primary_sample_fields)
        object.__setattr__(self, "fallback_sample_fields", fallback_sample_fields)
        object.__setattr__(self, "sample_number_field", sample_number_field)
        object.__setattr__(self, "object_identity_fields", object_identity_fields)

    @property
    def sample_identity_fields(self) -> frozenset[str]:
        """Return every field that can identify a sample row."""
        return self.primary_sample_fields | self.fallback_sample_fields

    def selected_sample_identity_fields(
        self,
        normalized_present_fields: frozenset[str],
    ) -> frozenset[str]:
        """Return the identity fields that own a row under this contract."""
        primary_fields = normalized_present_fields & self.primary_sample_fields
        if primary_fields:
            return primary_fields
        return normalized_present_fields & self.fallback_sample_fields
