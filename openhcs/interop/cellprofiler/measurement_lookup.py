"""Typed CellProfiler measurement-name compatibility over core runtime queries."""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass
from enum import Enum
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



class CellProfilerMeasurementFeatureKind(Enum):
    """CellProfiler measurement feature families with structured semantics."""

    OBJECT_COUNT = "object_count"
    CHILD_COUNT = "child_count"
    OTHER = "other"


@dataclass(frozen=True, slots=True)
class CellProfilerMeasurementFeature:
    """Structured view of one CellProfiler measurement feature name."""

    name: str
    kind: CellProfilerMeasurementFeatureKind
    object_name: str | None = None

    @classmethod
    def parse(cls, feature_name: str | None) -> "CellProfilerMeasurementFeature | None":
        """Parse a CellProfiler feature name into nominal feature semantics."""
        if feature_name is None:
            return None
        normalized = feature_name.strip()
        if not normalized:
            return None
        for parser_type in CellProfilerMeasurementFeatureParser.__registry__.values():
            parsed = parser_type().parse_feature(normalized)
            if parsed is not None:
                return parsed
        return cls(
            normalized,
            CellProfilerMeasurementFeatureKind.OTHER,
        )

    @classmethod
    def object_count(cls, object_name: str) -> "CellProfilerMeasurementFeature":
        return CellProfilerMeasurementFeatureParser.for_kind(
            CellProfilerMeasurementFeatureKind.OBJECT_COUNT
        ).feature_from_object_name(object_name)

    @classmethod
    def child_count(cls, child_object_name: str) -> "CellProfilerMeasurementFeature":
        return CellProfilerMeasurementFeatureParser.for_kind(
            CellProfilerMeasurementFeatureKind.CHILD_COUNT
        ).feature_from_object_name(child_object_name)

    @classmethod
    def child_count_object_names(
        cls,
        feature_names: tuple[object, ...],
    ) -> tuple[str, ...]:
        """Return ordered unique child object names referenced by count features."""
        child_names = tuple(
            parsed.object_name
            for feature_name in feature_names
            for parsed in (cls.parse(str(feature_name)),)
            if (
                parsed is not None
                and parsed.kind is CellProfilerMeasurementFeatureKind.CHILD_COUNT
                and parsed.object_name is not None
            )
        )
        return tuple(dict.fromkeys(child_names))


class CellProfilerMeasurementFeatureParser(ABC, metaclass=AutoRegisterMeta):
    """Registered parser/renderer for one CellProfiler measurement feature family."""

    __registry_key__ = "kind_key"
    __skip_if_no_key__ = True
    kind: ClassVar[CellProfilerMeasurementFeatureKind | None] = None
    kind_key: ClassVar[str | None] = None

    @classmethod
    def for_kind(
        cls,
        kind: CellProfilerMeasurementFeatureKind,
    ) -> "CellProfilerMeasurementFeatureParser":
        parser_type = cls.__registry__.get(kind.value)
        if parser_type is None:
            raise KeyError(f"No CellProfiler measurement parser registered for {kind}.")
        return parser_type()

    @abstractmethod
    def parse_feature(
        self,
        feature_name: str,
    ) -> CellProfilerMeasurementFeature | None:
        """Return parsed feature semantics when this parser owns the name."""

    @abstractmethod
    def feature_from_object_name(
        self,
        object_name: str,
    ) -> CellProfilerMeasurementFeature:
        """Render a feature name for an object-targeted feature family."""


class CellProfilerObjectCountFeatureParser(CellProfilerMeasurementFeatureParser):
    """Parser for CellProfiler ``Count_<object>`` image-level object counts."""

    kind = CellProfilerMeasurementFeatureKind.OBJECT_COUNT
    kind_key = kind.value
    prefix = "Count_"

    def parse_feature(
        self,
        feature_name: str,
    ) -> CellProfilerMeasurementFeature | None:
        if not feature_name.startswith(self.prefix):
            return None
        object_name = feature_name[len(self.prefix) :].strip()
        if not object_name:
            return None
        return CellProfilerMeasurementFeature(
            name=feature_name,
            kind=CellProfilerMeasurementFeatureKind.OBJECT_COUNT,
            object_name=object_name,
        )

    def feature_from_object_name(
        self,
        object_name: str,
    ) -> CellProfilerMeasurementFeature:
        normalized = object_name.strip()
        if not normalized:
            raise ValueError("Object-count feature requires a non-empty object name.")
        return CellProfilerMeasurementFeature(
            name=f"{self.prefix}{normalized}",
            kind=CellProfilerMeasurementFeatureKind.OBJECT_COUNT,
            object_name=normalized,
        )


class CellProfilerChildCountFeatureParser(CellProfilerMeasurementFeatureParser):
    """Parser for CellProfiler ``Children_<object>_Count`` relationships."""

    kind = CellProfilerMeasurementFeatureKind.CHILD_COUNT
    kind_key = kind.value

    def parse_feature(self, feature_name: str) -> CellProfilerMeasurementFeature | None:
        object_name = ChildCountFeatureDeclaration.from_feature_name(feature_name)
        if object_name is None:
            return None
        return CellProfilerMeasurementFeature(
            name=feature_name,
            kind=CellProfilerMeasurementFeatureKind.CHILD_COUNT,
            object_name=object_name,
        )

    def feature_from_object_name(
        self, object_name: str
    ) -> CellProfilerMeasurementFeature:
        feature_name = ChildCountFeatureDeclaration.feature_name(object_name)
        return CellProfilerMeasurementFeature(
            name=feature_name,
            kind=CellProfilerMeasurementFeatureKind.CHILD_COUNT,
            object_name=object_name.strip(),
        )


def count_feature_object_name(feature_name: str | None) -> str | None:
    """Return the object-set name encoded by a CellProfiler Count_* feature."""
    parsed = CellProfilerMeasurementFeature.parse(feature_name)
    if (
        parsed is None
        or parsed.kind is not CellProfilerMeasurementFeatureKind.OBJECT_COUNT
    ):
        return None
    return parsed.object_name


def child_count_feature_child_name(feature_name: str | None) -> str | None:
    """Return the child object name encoded by Children_<object>_Count."""
    parsed = CellProfilerMeasurementFeature.parse(feature_name)
    if (
        parsed is None
        or parsed.kind is not CellProfilerMeasurementFeatureKind.CHILD_COUNT
    ):
        return None
    return parsed.object_name


__all__ = declared_public_names(
    globals(),
    extra_names=("measurement_values_for_feature",),
)
