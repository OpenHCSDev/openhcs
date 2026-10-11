"""Typed CellProfiler measurement-name compatibility over core runtime queries."""

from __future__ import annotations

from abc import ABC
from dataclasses import dataclass
from typing import ClassVar

from metaclass_registry import AutoRegisterMeta

from openhcs.core.runtime_measurements import RuntimeMeasurementFeatureDeclaration
from openhcs.core.runtime_relationships import DirectParentReferenceFeatureMarker
from python_introspect import declared_public_names
from openhcs.core.measurement_feature_queries import measurement_values_for_feature


@dataclass(frozen=True, slots=True)
class DirectParentReferenceMeasurementFeature:
    """Nominal identity encoded by a ``Parent_<object>`` measurement name."""

    parent_object_name: str

    def __post_init__(self) -> None:
        if not isinstance(self.parent_object_name, str) or not self.parent_object_name:
            raise ValueError("Direct parent-reference object name cannot be empty.")


class DirectParentReferenceFeatureDeclaration(RuntimeMeasurementFeatureDeclaration):
    """Parse and render direct parent references at their row-production owner."""

    declaration_key = "direct_parent_reference"
    semantic_marker_types = (DirectParentReferenceFeatureMarker,)
    prefix = "Parent_"

    @classmethod
    def from_feature_name(
        cls,
        feature_name: str,
    ) -> DirectParentReferenceMeasurementFeature | None:
        if not feature_name.startswith(cls.prefix):
            return None
        parent_object_name = feature_name[len(cls.prefix) :]
        if not parent_object_name:
            return None
        return DirectParentReferenceMeasurementFeature(parent_object_name)

    @classmethod
    def feature_name(cls, identity: object) -> str:
        if not isinstance(identity, DirectParentReferenceMeasurementFeature):
            raise TypeError(
                f"{cls.__name__}.feature_name requires "
                "DirectParentReferenceMeasurementFeature."
            )
        return f"{cls.prefix}{identity.parent_object_name}"


class ChildCountFeatureDeclaration(RuntimeMeasurementFeatureDeclaration):
    """Own the child-name grammar shared by export readers and CP producers."""

    declaration_key = "child_count_reference"
    prefix = "Children_"
    suffix = "_Count"

    @classmethod
    def from_feature_name(cls, feature_name: str) -> str | None:
        if not feature_name.startswith(cls.prefix) or not feature_name.endswith(
            cls.suffix
        ):
            return None
        name = feature_name[len(cls.prefix) : -len(cls.suffix)].strip()
        return name or None

    @classmethod
    def feature_name(cls, identity: str) -> str:
        name = identity.strip()
        if not name:
            raise ValueError(
                "Child-count feature requires a non-empty child object name."
            )
        return f"{cls.prefix}{name}{cls.suffix}"



class CellProfilerMeasurementFeatureKind(ABC, metaclass=AutoRegisterMeta):
    """A CellProfiler measurement feature-name convention.

    Each convention is a subclass that parses and renders its names. A kind
    whose names target an object set reads the object name out of them.
    """

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type[CellProfilerMeasurementFeatureKind]]] = {}

    name: ClassVar[str | None] = None
    needs_prior_measurement_rows: ClassVar[bool] = True
    """Its values come from earlier measurement rows, not from object labels."""

    @classmethod
    def object_name_in(cls, feature_name: str) -> str | None:
        """Return the object name ``feature_name`` targets in this convention."""
        return None

    @classmethod
    def feature(cls, object_name: str) -> "CellProfilerMeasurementFeature":
        """Return the feature this convention names for ``object_name``."""
        raise TypeError(f"{cls.__name__} does not name features after object sets.")


class ObjectCountFeatureName(CellProfilerMeasurementFeatureKind):
    """CellProfiler ``Count_<object>`` image-level object counts."""

    name = "object_count"
    needs_prior_measurement_rows = False
    prefix: ClassVar[str] = "Count_"

    @classmethod
    def object_name_in(cls, feature_name: str) -> str | None:
        if not feature_name.startswith(cls.prefix):
            return None
        return feature_name[len(cls.prefix) :].strip() or None

    @classmethod
    def feature(cls, object_name: str) -> "CellProfilerMeasurementFeature":
        normalized = object_name.strip()
        if not normalized:
            raise ValueError("Object-count feature requires a non-empty object name.")
        return CellProfilerMeasurementFeature(
            name=f"{cls.prefix}{normalized}", kind=cls, object_name=normalized
        )


class ChildCountFeatureName(CellProfilerMeasurementFeatureKind):
    """CellProfiler ``Children_<object>_Count`` relationship counts."""

    name = "child_count"

    @classmethod
    def object_name_in(cls, feature_name: str) -> str | None:
        return ChildCountFeatureDeclaration.from_feature_name(feature_name)

    @classmethod
    def feature(cls, object_name: str) -> "CellProfilerMeasurementFeature":
        return CellProfilerMeasurementFeature(
            name=ChildCountFeatureDeclaration.feature_name(object_name),
            kind=cls,
            object_name=object_name.strip(),
        )


class OtherFeatureName(CellProfilerMeasurementFeatureKind):
    """Any other feature name; it names no object set."""

    name = "other"


@dataclass(frozen=True, slots=True)
class CellProfilerMeasurementFeature:
    """Structured view of one CellProfiler measurement feature name."""

    name: str
    kind: type[CellProfilerMeasurementFeatureKind]
    object_name: str | None = None

    @classmethod
    def parse(cls, feature_name: str | None) -> "CellProfilerMeasurementFeature | None":
        """Parse a CellProfiler feature name into its convention and object."""
        if feature_name is None:
            return None
        normalized = feature_name.strip()
        if not normalized:
            return None
        for kind in CellProfilerMeasurementFeatureKind.__registry__.values():
            object_name = kind.object_name_in(normalized)
            if object_name is not None:
                return cls(normalized, kind, object_name)
        return cls(normalized, OtherFeatureName)

    @classmethod
    def child_count_object_names(
        cls,
        feature_names: tuple[object, ...],
    ) -> tuple[str, ...]:
        """Return ordered unique child object names referenced by count features."""
        child_names = (
            ChildCountFeatureName.object_name_in(str(feature_name).strip())
            for feature_name in feature_names
        )
        return tuple(dict.fromkeys(name for name in child_names if name is not None))


def count_feature_object_name(feature_name: str | None) -> str | None:
    """Return the object-set name encoded by a CellProfiler Count_* feature."""
    if feature_name is None:
        return None
    return ObjectCountFeatureName.object_name_in(feature_name.strip())


def child_count_feature_child_name(feature_name: str | None) -> str | None:
    """Return the child object name encoded by Children_<object>_Count."""
    if feature_name is None:
        return None
    return ChildCountFeatureName.object_name_in(feature_name.strip())


__all__ = declared_public_names(
    globals(),
    extra_names=("measurement_values_for_feature",),
)
