"""Nominal runtime object label domains semantics."""

from __future__ import annotations
from openhcs.core.runtime_plane_projection import NoPlaneAxis
from openhcs.core.runtime_plane_projection import RuntimeSlicePlaneAxis
from abc import ABC
from abc import abstractmethod
from collections.abc import Iterable
from dataclasses import dataclass
from metaclass_registry import AutoRegisterMeta
from metaclass_registry import RegistryFamily
from metaclass_registry import RegistryKeyAttribute
from metaclass_registry.strategies import NominalTypeKeyedStrategyMixin
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.runtime_plane_projection import RuntimePlaneAxisProjector
from openhcs.core.runtime_plane_projection import RuntimePlaneAxisValueProjection
from openhcs.core.runtime_tabular_values import MeasurementObjectRowIdentity
from typing import TYPE_CHECKING, Any
from typing import ClassVar
import numpy as np

if TYPE_CHECKING:
    from openhcs.core.runtime_object_labels import ObjectLabelValue
    from openhcs.core.source_image_provenance import SourceImageProvenance


DeclaredObjectIds = tuple[int, ...] | list[int] | None


class ObjectLabelDomainScope(ABC, metaclass=AutoRegisterMeta):
    """How declared object-label IDs apply across dense label planes.

    Each scope is a subclass, used as a class; ``name`` is its spelling in
    profiles and error text. A scope owns how its labels project onto
    measurement planes.
    """

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type[ObjectLabelDomainScope]]] = {}

    name: ClassVar[str | None] = None
    ids_per_plane: ClassVar[bool]
    """Each label plane declares its own object IDs."""
    ids_span_payload: ClassVar[bool]
    """One set of object IDs covers the whole label value."""

    @staticmethod
    def require_member(value: object) -> type[ObjectLabelDomainScope]:
        """Return ``value`` when it is an object-label domain scope."""
        if isinstance(value, type) and issubclass(value, ObjectLabelDomainScope):
            return value
        raise ValueError(f"{value!r} is not an object-label domain scope.")

    @staticmethod
    def common(scopes: Any) -> type[ObjectLabelDomainScope]:
        """Return the one scope declared by every merged label value."""
        unique_scopes = tuple(dict.fromkeys(scopes))
        if len(unique_scopes) == 1:
            return unique_scopes[0]
        raise ValueError(
            "Cannot merge object-label values with different domain scopes: "
            f"{unique_scopes!r}."
        )

    @classmethod
    @abstractmethod
    def validate_declared_ids(
        cls,
        *,
        object_count: int | None,
        object_ids: tuple[int, ...],
        plane_id_domains: tuple[tuple[int, ...], ...],
    ) -> None:
        """Reject declared IDs that do not fit this scope."""

    @classmethod
    @abstractmethod
    def plane_domains(
        cls,
        labels: Any,
        *,
        domain: ObjectLabelDomain,
    ) -> tuple[tuple[int, ...], ...]:
        """Return the object-id domain attached to each dense measurement plane."""

    @classmethod
    def identity_domains(
        cls,
        labels: Any,
        *,
        domain: ObjectLabelDomain,
    ) -> tuple[tuple[int, ...], ...]:
        """Return object-id domains for identity rows represented by the payload."""
        return cls.plane_domains(
            labels,
            domain=domain,
        )

    @classmethod
    @abstractmethod
    def measurement_object_row_identity(
        cls,
        declared_identity: MeasurementObjectRowIdentity,
    ) -> MeasurementObjectRowIdentity:
        """Return object-row identity after applying label-domain semantics."""

    @classmethod
    @abstractmethod
    def present_domain(
        cls,
        labels: Any,
        *,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> ObjectLabelDomain:
        """Declare the material IDs produced in an already-selected domain scope."""

    @classmethod
    @abstractmethod
    def measurement_projection(
        cls,
        labels: "ObjectLabelValue",
        projector: RuntimePlaneAxisProjector,
    ) -> RuntimePlaneAxisValueProjection:
        """Resolve the runtime row projection represented by label semantics."""

    @classmethod
    @abstractmethod
    def measurement_axis_values(
        cls,
        labels: "ObjectLabelValue",
        projection: RuntimePlaneAxisValueProjection,
    ) -> tuple[int, ...]:
        """Return exact measurement-row axis values represented by labels."""

    @classmethod
    def required_measurement_axis_values(
        cls,
        labels: "ObjectLabelValue",
        projection: RuntimePlaneAxisValueProjection,
    ) -> tuple[int, ...]:
        """Return row-axis values required by nonempty declared label planes."""

        axis_values = cls.measurement_axis_values(labels, projection)
        plane_domains = cls.plane_domains(
            labels,
            domain=labels.object_label_domain(),
        )
        if len(axis_values) != len(plane_domains):
            raise ValueError(
                "Object-label measurement axis and declared plane domains have "
                f"different cardinalities: {len(axis_values)} != "
                f"{len(plane_domains)}."
            )
        return tuple(
            axis_value
            for axis_value, object_ids in zip(
                axis_values,
                plane_domains,
                strict=True,
            )
            if object_ids
        )

    @classmethod
    @abstractmethod
    def measurement_planes(
        cls,
        labels: "ObjectLabelValue",
        projection: RuntimePlaneAxisValueProjection | None,
    ) -> tuple["ObjectLabelValue", ...]:
        """Return label values in the same order as measurement axis values."""

    @classmethod
    def declared_measurement_planes(
        cls,
        labels: "ObjectLabelValue",
    ) -> tuple["ObjectLabelValue", ...]:
        """Project labels through their own declared plane-domain semantics."""
        return cls.measurement_planes(labels, cls.value_projection(labels))

    @classmethod
    def declared_measurement_axis_values(
        cls,
        labels: "ObjectLabelValue",
    ) -> tuple[int, ...]:
        """Return local row-axis values for every declared measurement plane."""
        return tuple(range(len(cls.declared_measurement_planes(labels))))

    @classmethod
    @abstractmethod
    def measurement_reference_source_provenance(
        cls,
        labels: "ObjectLabelValue",
    ) -> "SourceImageProvenance":
        """Return source lineage in this domain's image-reference topology."""

    @classmethod
    @abstractmethod
    def value_plane_axis(
        cls,
        plane_axis: type[RuntimePlaneAxis],
    ) -> type[RuntimePlaneAxis]:
        """Return the plane axis valid for this declared domain scope."""

    @classmethod
    @abstractmethod
    def value_projection(
        cls,
        labels: "ObjectLabelValue",
    ) -> RuntimePlaneAxisValueProjection | None:
        """Return the exact runtime plane projection declared by a label value."""


class PayloadLabelScope(ObjectLabelDomainScope):
    """Declared IDs describe one indivisible label value."""

    name = "payload"
    ids_per_plane = False
    ids_span_payload = True

    @classmethod
    def validate_declared_ids(
        cls,
        *,
        object_count: int | None,
        object_ids: tuple[int, ...],
        plane_id_domains: tuple[tuple[int, ...], ...],
    ) -> None:
        del object_count, object_ids
        if plane_id_domains:
            raise ValueError(
                "Payload-scoped object-label domains cannot declare per-plane "
                "object-ID domains."
            )

    @classmethod
    def plane_domains(
        cls,
        labels: Any,
        *,
        domain: ObjectLabelDomain,
    ) -> tuple[tuple[int, ...], ...]:
        if domain.scope is not cls:
            raise ValueError(
                "Payload object-label domain strategy requires a payload-scoped "
                f"declaration, got {domain.scope.name!r}."
            )
        if domain.declared_object_id_domains:
            raise ValueError(
                "Payload-scoped object labels cannot declare per-plane object-ID "
                "domains."
            )
        object_ids = domain.require_explicit_id_domain(
            context="Payload-scoped object labels"
        )
        return (object_ids,)

    @classmethod
    def measurement_object_row_identity(
        cls,
        declared_identity: MeasurementObjectRowIdentity,
    ) -> MeasurementObjectRowIdentity:
        """Keep the row identity declared for one indivisible payload."""
        return declared_identity

    @classmethod
    def present_domain(
        cls,
        labels: Any,
        *,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> ObjectLabelDomain:
        if plane_projection is not None:
            raise ValueError(
                "Payload-scoped object-label declaration cannot consume a plane "
                "projection."
            )
        object_ids = ObjectLabelIdDomainStrategy.for_value(labels).present_ids(labels)
        return ObjectLabelDomain.declared(
            scope=cls,
            declared_object_count=0 if not object_ids else None,
            declared_object_ids=object_ids,
        )

    @classmethod
    def measurement_projection(
        cls,
        labels: "ObjectLabelValue",
        projector: RuntimePlaneAxisProjector,
    ) -> RuntimePlaneAxisValueProjection:
        projection = RuntimePlaneAxisValueProjection.require_from_projector(
            projector,
            RuntimeSlicePlaneAxis,
        )
        if projection.preserves_complete_axis and projection.axis_size != 1:
            raise ValueError(
                "Payload-scoped object-label measurement lookup requires one "
                "selected runtime slice, but the invocation preserves "
                f"{projection.axis_size} {projection.axis.name!r} plane(s)."
            )
        return projection

    @classmethod
    def measurement_axis_values(
        cls,
        labels: "ObjectLabelValue",
        projection: RuntimePlaneAxisValueProjection,
    ) -> tuple[int, ...]:
        if projection.selects_one_plane:
            return projection.selected_planes()
        return (0,)

    @classmethod
    def required_measurement_axis_values(
        cls,
        labels: "ObjectLabelValue",
        projection: RuntimePlaneAxisValueProjection,
    ) -> tuple[int, ...]:
        """Payload-scoped measurements need no per-plane row coordinate."""

        del labels, projection
        return ()

    @classmethod
    def measurement_planes(
        cls,
        labels: "ObjectLabelValue",
        projection: RuntimePlaneAxisValueProjection | None,
    ) -> tuple["ObjectLabelValue", ...]:
        del projection
        return (labels,)

    @classmethod
    def measurement_reference_source_provenance(
        cls,
        labels: "ObjectLabelValue",
    ) -> "SourceImageProvenance":
        """Keep volume planes as contributors to one payload-scoped image."""

        return labels.source_provenance.with_runtime_planes_as_contributors()

    @classmethod
    def value_plane_axis(
        cls,
        plane_axis: type[RuntimePlaneAxis],
    ) -> type[RuntimePlaneAxis]:
        del plane_axis
        return NoPlaneAxis

    @classmethod
    def value_projection(
        cls,
        labels: "ObjectLabelValue",
    ) -> None:
        del labels
        return None


class PlaneLabelScope(ObjectLabelDomainScope):
    """Declared IDs map exactly to the declared label-plane stack."""

    name = "plane"
    ids_per_plane = True
    ids_span_payload = False

    @classmethod
    def validate_declared_ids(
        cls,
        *,
        object_count: int | None,
        object_ids: tuple[int, ...],
        plane_id_domains: tuple[tuple[int, ...], ...],
    ) -> None:
        if not plane_id_domains:
            raise ValueError(
                "Plane-scoped object-label domains require one explicit object-ID "
                "domain per plane."
            )
        if object_count is not None or object_ids:
            raise ValueError(
                "Plane-scoped object-label domains cannot also declare a payload-wide "
                "object count or object-ID domain."
            )

    @classmethod
    def plane_domains(
        cls,
        labels: Any,
        *,
        domain: ObjectLabelDomain,
    ) -> tuple[tuple[int, ...], ...]:

        if domain.scope is not cls:
            raise ValueError(
                "Plane object-label domain strategy requires a plane-scoped "
                f"declaration, got {domain.scope.name!r}."
            )
        if domain.declared_object_count is not None or domain.declared_object_ids:
            raise ValueError(
                "Plane-scoped object labels require per-plane object-ID domains, "
                "not a payload-wide count or ID domain."
            )
        plane_count = labels.declared_plane_count()
        if plane_count is None:
            raise ValueError(
                "Plane-scoped object labels require a nominal label-plane "
                "representation."
            )
        if len(domain.declared_object_id_domains) != plane_count:
            raise ValueError(
                "Plane-scoped object-label domains must match the declared label "
                f"plane count: {len(domain.declared_object_id_domains)} domains for "
                f"{plane_count} planes."
            )
        return domain.declared_object_id_domains

    @classmethod
    def measurement_object_row_identity(
        cls,
        declared_identity: MeasurementObjectRowIdentity,
    ) -> MeasurementObjectRowIdentity:
        """Use labels within the runtime-slice/object identity product."""
        del declared_identity
        return MeasurementObjectRowIdentity.LABEL_ID

    @classmethod
    def present_domain(
        cls,
        labels: Any,
        *,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> ObjectLabelDomain:
        from openhcs.core.runtime_object_labels import (
            object_label_project_plane,
            object_label_validate_plane_count,
        )

        if plane_projection is None:
            raise ValueError(
                "Plane-scoped object-label declaration requires an exact runtime "
                "plane projection."
            )
        object_label_validate_plane_count(
            labels,
            plane_count=plane_projection.axis_size,
            context="Object-label present-domain declaration",
        )
        return ObjectLabelDomain.declared(
            scope=cls,
            declared_object_id_domains=tuple(
                ObjectLabelIdDomainStrategy.for_value(plane).present_ids(plane)
                for plane in (
                    object_label_project_plane(
                        labels,
                        index,
                        plane_count=plane_projection.axis_size,
                    )
                    for index in range(plane_projection.axis_size)
                )
            ),
        )

    @classmethod
    def measurement_projection(
        cls,
        labels: "ObjectLabelValue",
        projector: RuntimePlaneAxisProjector,
    ) -> RuntimePlaneAxisValueProjection:
        return RuntimePlaneAxisValueProjection.require_from_projector(
            projector,
            cls.value_plane_axis(labels.plane_axis),
            labels.source_aliases,
        )

    @classmethod
    def measurement_axis_values(
        cls,
        labels: "ObjectLabelValue",
        projection: RuntimePlaneAxisValueProjection,
    ) -> tuple[int, ...]:
        return projection.selected_planes()

    @classmethod
    def measurement_planes(
        cls,
        labels: "ObjectLabelValue",
        projection: RuntimePlaneAxisValueProjection | None,
    ) -> tuple["ObjectLabelValue", ...]:
        from openhcs.core.runtime_object_labels import (
            object_label_project_plane,
        )

        if projection is None:
            raise ValueError(
                "Plane-scoped object-label measurement requires an exact runtime "
                "plane projection."
            )
        plane_count = labels.declared_plane_count()
        if projection.selects_one_plane:
            if plane_count is not None:
                raise ValueError(
                    "Grouped plane-scoped object labels must already be projected "
                    f"to one label value, but {type(labels).__name__} carries "
                    f"{plane_count} planes."
                )
            return (labels,)
        if plane_count is None:
            raise ValueError(
                "Stack-scoped plane object labels require an explicit label-plane "
                "stack."
            )
        if plane_count != projection.axis_size:
            raise ValueError(
                "Plane-scoped object-label count must equal the declared runtime "
                f"axis size: {plane_count} != {projection.axis_size}."
            )
        return tuple(
            labels.with_projected_plane(
                object_label_project_plane(
                    labels.labels,
                    index,
                    plane_count=plane_count,
                ),
                index,
            )
            for index in range(projection.axis_size)
        )

    @classmethod
    def measurement_reference_source_provenance(
        cls,
        labels: "ObjectLabelValue",
    ) -> "SourceImageProvenance":
        """Preserve the projectable source planes declared by plane scope."""

        return labels.source_provenance

    @classmethod
    def value_plane_axis(
        cls,
        plane_axis: type[RuntimePlaneAxis],
    ) -> type[RuntimePlaneAxis]:
        if plane_axis.unstacked:
            raise ValueError(
                "Plane-scoped object labels require a declared runtime plane axis."
            )
        return plane_axis

    @classmethod
    def value_projection(
        cls,
        labels: "ObjectLabelValue",
    ) -> RuntimePlaneAxisValueProjection:
        plane_axis = cls.value_plane_axis(labels.plane_axis)
        return RuntimePlaneAxisValueProjection.preserve(
            axis=plane_axis,
            axis_size=len(labels.object_label_domain().declared_object_id_domains),
            source_aliases=labels.source_aliases,
        )


@dataclass(frozen=True, slots=True)
class ObjectLabelDomain:
    """Declared object-label identity domain metadata."""

    declared_object_count: int | None = None
    declared_object_ids: tuple[int, ...] = ()
    declared_object_id_domains: tuple[tuple[int, ...], ...] = ()
    scope: type[ObjectLabelDomainScope] = PayloadLabelScope

    def __post_init__(self) -> None:
        if self.declared_object_count is not None:
            count = int(self.declared_object_count)
            if count < 0:
                raise ValueError(
                    "ObjectLabelDomain.declared_object_count cannot be negative."
                )
            object.__setattr__(self, "declared_object_count", count)
        object.__setattr__(
            self,
            "declared_object_ids",
            self._normalize_ids(self.declared_object_ids, "declared_object_ids"),
        )
        object.__setattr__(
            self,
            "declared_object_id_domains",
            tuple(
                (
                    self._normalize_ids(domain, "declared_object_id_domains")
                    for domain in self.declared_object_id_domains
                )
            ),
        )
        ObjectLabelDomainScope.require_member(self.scope).validate_declared_ids(
            object_count=self.declared_object_count,
            object_ids=self.declared_object_ids,
            plane_id_domains=self.declared_object_id_domains,
        )

    @staticmethod
    def _normalize_ids(
        ids: tuple[int, ...] | list[int], field_name: str
    ) -> tuple[int, ...]:
        normalized = tuple((int(object_id) for object_id in ids))
        if any((object_id <= 0 for object_id in normalized)):
            raise ValueError(f"ObjectLabelDomain.{field_name} IDs must be positive.")
        return tuple(sorted(dict.fromkeys(normalized)))

    @classmethod
    def declared(
        cls,
        *,
        scope: type[ObjectLabelDomainScope] = PayloadLabelScope,
        declared_object_count: int | None = None,
        declared_object_ids: DeclaredObjectIds = (),
        declared_object_id_domains: tuple[tuple[int, ...], ...] = (),
    ) -> "ObjectLabelDomain":
        """Return a normalized object-label domain declaration."""
        return cls(
            declared_object_count=declared_object_count,
            declared_object_ids=(
                tuple(declared_object_ids) if declared_object_ids is not None else ()
            ),
            declared_object_id_domains=declared_object_id_domains,
            scope=scope,
        )

    def explicit_id_domain(self) -> tuple[int, ...] | None:
        """Return this declaration as IDs, or ``None`` if it is undeclared."""
        if self.declared_object_ids:
            return self.declared_object_ids
        if self.declared_object_count is not None:
            return tuple(range(1, self.declared_object_count + 1))
        return None

    def require_explicit_id_domain(self, *, context: str) -> tuple[int, ...]:
        """Return declared IDs or reject an undeclared semantic domain."""
        object_ids = self.explicit_id_domain()
        if object_ids is None:
            raise ValueError(
                f"{context} requires an explicit object-ID domain; label contents "
                "cannot declare semantic identity."
            )
        return object_ids

    def with_scope(self, scope: type[ObjectLabelDomainScope]) -> "ObjectLabelDomain":
        """Return this object-label declaration with the requested domain scope."""
        normalized_scope = ObjectLabelDomainScope.require_member(scope)
        if (
            normalized_scope.ids_span_payload
            and self.scope.ids_per_plane
            and self.declared_object_id_domains
        ):
            declared_object_ids = tuple(
                sorted(
                    {
                        object_id
                        for domain in self.declared_object_id_domains
                        for object_id in domain
                    }
                )
            )
            return ObjectLabelDomain(
                declared_object_count=self.declared_object_count,
                declared_object_ids=declared_object_ids,
                scope=normalized_scope,
            )
        return ObjectLabelDomain(
            declared_object_count=self.declared_object_count,
            declared_object_ids=self.declared_object_ids,
            declared_object_id_domains=self.declared_object_id_domains,
            scope=normalized_scope,
        )

    def project_slice(self, slice_index: int, slice_count: int) -> "ObjectLabelDomain":
        """Return the object-label domain carried by one PURE_2D slice."""
        normalized_index = int(slice_index)
        normalized_count = int(slice_count)
        if normalized_count <= 0:
            raise ValueError("Object-label slice_count must be positive.")
        if normalized_index < 0 or normalized_index >= normalized_count:
            raise ValueError(
                f"Object-label slice_index {normalized_index} is outside slice_count {normalized_count}."
            )
        if self.scope.ids_span_payload:
            raise ValueError(
                "Runtime-slice projection requires a plane-scoped object-label "
                f"domain, got {self.scope.name!r}."
            )
        if not self.declared_object_id_domains:
            raise ValueError(
                "Plane-scoped object-label projection requires one declared "
                "object-ID domain per runtime slice."
            )
        if len(self.declared_object_id_domains) != normalized_count:
            raise ValueError(
                f"Plane-scoped object-label domains must match PURE_2D slice count: {len(self.declared_object_id_domains)} domains for {normalized_count} slices."
            )
        return self.project_planes((normalized_index,))

    def project_planes(self, plane_indices: Iterable[int]) -> "ObjectLabelDomain":
        """Return the object-label domain carried by selected plane indexes."""
        normalized_indices = tuple((int(index) for index in plane_indices))
        if self.scope.ids_span_payload:
            raise ValueError(
                "Object-label plane projection requires a plane-scoped domain."
            )
        if not self.declared_object_id_domains:
            raise ValueError(
                "Object-label plane projection requires declared per-plane "
                "object-ID domains."
            )
        if not normalized_indices:
            domains: tuple[tuple[int, ...], ...] = ()
        elif any(
            (
                index < 0 or index >= len(self.declared_object_id_domains)
                for index in normalized_indices
            )
        ):
            raise ValueError(
                f"Object-label plane projection index is outside declared domain count {len(self.declared_object_id_domains)}: {normalized_indices!r}."
            )
        else:
            domains = tuple(
                (self.declared_object_id_domains[index] for index in normalized_indices)
            )
        if len(domains) == 1:
            return ObjectLabelDomain.declared(
                scope=PayloadLabelScope,
                declared_object_count=0 if not domains[0] else None,
                declared_object_ids=domains[0],
            )
        return ObjectLabelDomain.declared(
            scope=PlaneLabelScope, declared_object_id_domains=domains
        )


class ObjectLabelDomainMetadata(ABC):
    """Nominal provider for object-label ID domain metadata."""

    @abstractmethod
    def object_label_domain(self) -> ObjectLabelDomain:
        """Return the declared object-label identity domain."""


class ObjectLabelDomainMetadataStrategy(
    NominalTypeKeyedStrategyMixin, ABC, metaclass=AutoRegisterMeta
):
    """Registered extractor for nominal object-label domain metadata."""

    value_type: ClassVar[type[object] | tuple[type[object], ...] | None] = None
    value_type_label: ClassVar[str | None] = None
    __registry_family__ = RegistryFamily(RegistryKeyAttribute.VALUE_TYPE_LABEL)

    @classmethod
    def for_value(cls, value: object) -> "ObjectLabelDomainMetadataStrategy":
        return cls.require_nominal_value(
            value,
            context="Object-label domain metadata",
        )

    @abstractmethod
    def object_label_domain(self, value: object) -> ObjectLabelDomain:
        """Return the declared object-label identity domain for ``value``."""


class NominalObjectLabelDomainMetadataStrategy(ObjectLabelDomainMetadataStrategy):
    """Use the domain declared by a nominal object-label domain provider."""

    value_type = ObjectLabelDomainMetadata

    def object_label_domain(self, value: object) -> ObjectLabelDomain:
        if not isinstance(value, ObjectLabelDomainMetadata):
            raise TypeError(
                f"NominalObjectLabelDomainMetadataStrategy requires ObjectLabelDomainMetadata, got {type(value).__name__}."
            )
        return value.object_label_domain()


class ObjectLabelIdDomainStrategy(
    NominalTypeKeyedStrategyMixin, ABC, metaclass=AutoRegisterMeta
):
    """Registered extractor for materially present positive object-label IDs."""

    value_type: ClassVar[type[object] | None] = None
    value_type_label: ClassVar[str | None] = None
    __registry_family__ = RegistryFamily(RegistryKeyAttribute.VALUE_TYPE_LABEL)

    @classmethod
    def for_value(cls, labels: Any) -> "ObjectLabelIdDomainStrategy":
        strategy = cls.for_nominal_value(labels)
        if strategy is None:
            raise TypeError(
                "Object-label ID extraction requires a registered nominal payload "
                f"type, got {type(labels).__name__}."
            )
        return strategy

    @abstractmethod
    def present_ids(self, labels: Any) -> tuple[int, ...]:
        """Return positive object IDs materially present in the label payload."""

    def max_present_id(self, labels: Any) -> int:
        """Return the largest materially present positive object ID."""
        ids = self.present_ids(labels)
        return max(ids) if ids else 0

    @staticmethod
    def positive_ids_from_array(labels: Any) -> tuple[int, ...]:
        """Return positive IDs from one numeric dense object-label array."""
        import numpy as np

        label_array = np.asarray(labels)
        if not label_array.size or not (
            np.issubdtype(label_array.dtype, np.number)
            or np.issubdtype(label_array.dtype, np.bool_)
        ):
            return ()
        dense_integer_domain = DenseIntegerObjectLabelIdDomain.from_array(label_array)
        if dense_integer_domain is not None:
            return dense_integer_domain.present_ids()
        return tuple(
            (int(object_id) for object_id in np.unique(label_array) if object_id > 0)
        )


@dataclass(frozen=True, slots=True)
class DenseIntegerObjectLabelIdDomain:
    """Exact present-ID extractor for bounded nonnegative dense integer labels."""

    labels: np.ndarray
    max_label: int

    @classmethod
    def from_array(cls, labels: np.ndarray) -> "DenseIntegerObjectLabelIdDomain | None":
        if not (
            np.issubdtype(labels.dtype, np.integer)
            or np.issubdtype(labels.dtype, np.bool_)
        ):
            return None
        if labels.size == 0:
            return None
        min_label = int(labels.min())
        if min_label < 0:
            return None
        max_label = int(labels.max())
        if max_label > labels.size:
            return None
        return cls(labels=labels, max_label=max_label)

    def present_ids(self) -> tuple[int, ...]:
        if self.max_label <= 0:
            return ()
        counts = np.bincount(
            np.asarray(self.labels, dtype=np.int64).ravel(),
            minlength=self.max_label + 1,
        )
        present_ids = np.flatnonzero(counts)
        return tuple((int(label_id) for label_id in present_ids if label_id > 0))


class DenseArrayObjectLabelIdDomainStrategy(ObjectLabelIdDomainStrategy):
    """Extract present object IDs from dense NumPy label arrays."""

    value_type = np.ndarray

    def present_ids(self, labels: Any) -> tuple[int, ...]:
        return self.positive_ids_from_array(labels)


@dataclass(frozen=True, slots=True)
class ConsecutiveObjectLabelIdProjection:
    """Projection from arbitrary positive object IDs to consecutive IDs."""

    positive_label_ids: Any

    @classmethod
    def from_dense_array(
        cls, labels: np.ndarray
    ) -> "ConsecutiveObjectLabelIdProjection":
        label_array = np.asarray(labels)
        positive_ids = np.unique(label_array[label_array > 0])
        return cls(positive_ids.astype(np.int64, copy=False))

    @property
    def object_count(self) -> int:
        return int(len(self.positive_label_ids))

    @property
    def has_objects(self) -> bool:
        return self.object_count > 0

    def relabel_numpy_array(
        self, labels: np.ndarray, *, dtype: Any | None = None
    ) -> np.ndarray:
        """Apply this ID projection to one dense NumPy label array."""
        label_array = np.asarray(labels)
        output_dtype = np.dtype(dtype or label_array.dtype)
        if not self.has_objects:
            return np.zeros_like(label_array, dtype=output_dtype)
        if self.labels_are_already_consecutive:
            return label_array.astype(output_dtype, copy=False)
        if self.lookup_table_is_bounded(label_array):
            return self.lookup_table_relabel(label_array, output_dtype)
        return self.searchsorted_relabel(label_array, output_dtype)

    @property
    def labels_are_already_consecutive(self) -> bool:
        return bool(
            np.array_equal(
                self.positive_label_ids,
                np.arange(1, self.object_count + 1, dtype=np.int64),
            )
        )

    def lookup_table_is_bounded(self, labels: Any) -> bool:
        label_array = np.asarray(labels)
        max_label = int(self.positive_label_ids[-1])
        return max_label <= max(label_array.size * 2, self.object_count * 16)

    def lookup_table_relabel(self, labels: np.ndarray, dtype: Any) -> np.ndarray:
        label_array = np.asarray(labels)
        lookup = np.zeros(int(self.positive_label_ids[-1]) + 1, dtype=dtype)
        lookup[self.positive_label_ids] = np.arange(
            1, self.object_count + 1, dtype=dtype
        )
        return lookup[label_array]

    def searchsorted_relabel(self, labels: np.ndarray, dtype: Any) -> np.ndarray:
        label_array = np.asarray(labels)
        flat = label_array.reshape(-1)
        remapped = np.zeros(flat.shape, dtype=dtype)
        foreground = flat > 0
        positions = np.searchsorted(self.positive_label_ids, flat[foreground])
        remapped[foreground] = positions.astype(dtype, copy=False) + 1
        return remapped.reshape(label_array.shape)


class DenseObjectLabelConsecutiveRelabelingStrategy(
    NominalTypeKeyedStrategyMixin, ABC, metaclass=AutoRegisterMeta
):
    """Registered backend strategy for consecutive dense object-label IDs."""

    value_type: ClassVar[type[object] | None] = None
    value_type_label: ClassVar[str | None] = None
    __registry_family__ = RegistryFamily(RegistryKeyAttribute.VALUE_TYPE_LABEL)

    @classmethod
    def for_labels(
        cls, labels: object
    ) -> "DenseObjectLabelConsecutiveRelabelingStrategy":
        return cls.require_nominal_value(
            labels,
            context="Dense object-label consecutive relabeling",
        )

    @abstractmethod
    def relabel(self, labels: object, *, dtype: Any | None = None) -> object:
        """Return labels with materially present positive IDs remapped to 1..N."""


class NumpyDenseObjectLabelConsecutiveRelabelingStrategy(
    DenseObjectLabelConsecutiveRelabelingStrategy
):
    """Consecutive-ID relabeling for dense NumPy object-label arrays."""

    value_type = np.ndarray

    def relabel(self, labels: object, *, dtype: Any | None = None) -> np.ndarray:
        if not isinstance(labels, np.ndarray):
            raise TypeError(
                f"NumpyDenseObjectLabelConsecutiveRelabelingStrategy requires ndarray, got {type(labels).__name__}."
            )
        projection = ConsecutiveObjectLabelIdProjection.from_dense_array(labels)
        return projection.relabel_numpy_array(labels, dtype=dtype)


def dense_object_label_id_domain(
    labels: Any,
) -> tuple[int, ...]:
    """Return the explicitly declared semantic object-ID domain."""
    payload_domain = ObjectLabelDomainMetadataStrategy.for_value(
        labels
    ).object_label_domain(labels)
    return payload_domain.require_explicit_id_domain(context="Object-label consumers")


def dense_object_label_measurement_row_domain(
    labels: Any, dense_labels: Any
) -> tuple[int, ...]:
    """Return the declared row domain after validating material label IDs."""
    payload_domain = ObjectLabelDomainMetadataStrategy.for_value(
        labels
    ).object_label_domain(labels)
    declared_domain = payload_domain.require_explicit_id_domain(
        context="Object-label measurement rows"
    )
    present_ids = ObjectLabelIdDomainStrategy.for_value(dense_labels).present_ids(
        dense_labels
    )
    undeclared_ids = tuple(
        object_id for object_id in present_ids if object_id not in declared_domain
    )
    if undeclared_ids:
        raise ValueError(
            "Object-label pixels contain IDs outside the declared measurement-row "
            f"domain: {undeclared_ids!r}."
        )
    return declared_domain


class ObjectLabelDomainDeclaration(ABC, metaclass=AutoRegisterMeta):
    """Nominal declaration for transformed object-label identity domains."""

    __registry_key__ = "__name__"
    __skip_if_no_key__ = True

    @abstractmethod
    def declared_domain(self, source: Any, labels: Any) -> ObjectLabelDomain:
        """Return the object-label identity domain for transformed labels."""


@dataclass(frozen=True, slots=True)
class ExplicitObjectLabelDomainDeclaration(ObjectLabelDomainDeclaration):
    """Use an explicitly supplied object-label domain."""

    domain: ObjectLabelDomain

    def declared_domain(self, source: Any, labels: Any) -> ObjectLabelDomain:
        del source, labels
        return self.domain


@dataclass(frozen=True, slots=True)
class PreserveSourceObjectLabelDomainDeclaration(ObjectLabelDomainDeclaration):
    """Preserve source object-label declarations across shape-preserving transforms."""

    def declared_domain(self, source: Any, labels: Any) -> ObjectLabelDomain:
        del labels
        return ObjectLabelDomainMetadataStrategy.for_value(source).object_label_domain(
            source
        )


@dataclass(frozen=True, slots=True)
class PresentObjectLabelIdsDomainDeclaration(ObjectLabelDomainDeclaration):
    """Declare only object IDs materially present in transformed labels."""

    scope: type[ObjectLabelDomainScope] = PayloadLabelScope
    plane_projection: RuntimePlaneAxisValueProjection | None = None

    def declared_domain(self, source: Any, labels: Any) -> ObjectLabelDomain:
        del source
        return self.scope.present_domain(
            labels,
            plane_projection=self.plane_projection,
        )


@dataclass(frozen=True, slots=True)
class DenseObjectLabelExtentDomainDeclaration(ObjectLabelDomainDeclaration):
    """Declare the dense positive extent represented by transformed labels."""

    def declared_domain(self, source: Any, labels: Any) -> ObjectLabelDomain:
        del source
        return ObjectLabelDomain(
            declared_object_count=ObjectLabelIdDomainStrategy.for_value(
                labels
            ).max_present_id(labels)
        )


def dense_object_label_plane_id_domains(
    labels: Any,
) -> tuple[tuple[int, ...], ...]:
    """Return declared object-ID domains for each measurement plane."""
    payload_domain = ObjectLabelDomainMetadataStrategy.for_value(
        labels
    ).object_label_domain(labels)
    return payload_domain.scope.plane_domains(
        labels,
        domain=payload_domain,
    )


def dense_object_label_identity_domains(
    labels: Any,
) -> tuple[tuple[int, ...], ...]:
    """Return object-id domains for object identity rows represented by labels."""
    payload_domain = ObjectLabelDomainMetadataStrategy.for_value(
        labels
    ).object_label_domain(labels)
    return payload_domain.scope.identity_domains(
        labels,
        domain=payload_domain,
    )
