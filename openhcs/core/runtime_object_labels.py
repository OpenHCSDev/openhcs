"""Nominal runtime object-label values and transformations."""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import (
    Callable,
    Hashable,
    Iterable,
    Mapping,
    MutableMapping,
    Sequence,
)
from dataclasses import dataclass, field
from threading import Lock
from types import MappingProxyType
from typing import Any, ClassVar, Self, cast

import numpy as np
from metaclass_registry import AutoRegisterMeta
from numba import njit

from openhcs.core import (
    runtime_array_values,
    runtime_image_values,
)
from openhcs.core.artifacts import (
    NamedArtifactPayload,
    ObjectLabelsArtifactType,
)
from metaclass_registry.strategies import (
    EnumKeyedStrategyMixin,
    NominalTypeStrategyFamilyMixin,
)
from openhcs.core.runtime_object_label_domains import (
    DenseIntegerObjectLabelIdDomain,
    ObjectLabelDomain,
    ObjectLabelDomainDeclaration,
    ObjectLabelDomainMetadata,
    ObjectLabelDomainMetadataStrategy,
    ObjectLabelDomainScope,
    ObjectLabelIdDomainStrategy,
    ObjectLabelPlaneDomainStrategy,
    PreserveSourceObjectLabelDomainDeclaration,
)
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisStrategy,
    RuntimePlaneAxisValueProjection,
    RuntimeSliceIdentityProjectableValue,
)
from openhcs.core.runtime_tabular_values import MeasurementObjectRowIdentity
from openhcs.core.runtime_sparse_labels import SparseIJVLabelRows
from openhcs.core.source_image_provenance import (
    SourceImageProvenance,
    SourceImageProvenanceAddressRequirement,
    SourceImageProvenanceFields,
    SourceImageProvenancePlaneCountRequirement,
    SourcePlaneIndexedProvenanceExpansion,
)
from openhcs.core.source_metadata import (
    SourceVoxelSpacing,
)
from openhcs.core.source_spatial_domain import (
    SourceSpatialDomain,
    SourceSpatialDomainFields,
)

from enum import Enum
from openhcs.core.alias_property import AliasProperty
from openhcs.core.artifacts import ArtifactPayloadShape
from metaclass_registry.strategies import str_enum_member_with_payload

_PRESERVE_PLANE_AXIS = object()


def normalize_source_label_data(data: object, channel_axis: int | None) -> object:
    """Convert a source color label plane into stable positive integer IDs."""

    if channel_axis is None:
        return data
    rgb = np.moveaxis(np.asarray(data), channel_axis, -1)
    flat = rgb[..., :3].reshape(-1, 3)
    labels = np.zeros(flat.shape[0], dtype=np.int32)
    foreground = np.any(flat != 0, axis=1)
    if np.any(foreground):
        _colors, inverse = np.unique(flat[foreground], axis=0, return_inverse=True)
        labels[foreground] = inverse.astype(np.int32, copy=False) + 1
    return labels.reshape(rgb.shape[:-1])


class ObjectLabelRepresentation(str, Enum):
    """Storage representation used by an object-label artifact payload."""

    def __new__(cls, value: str, payload_shape: ArtifactPayloadShape):
        return str_enum_member_with_payload(
            cls, value, payload_attribute="_payload_shape", payload=payload_shape
        )

    DENSE_LABELS = ("dense_labels", ArtifactPayloadShape.ARRAY)
    SPARSE_IJV = ("sparse_ijv", ArtifactPayloadShape.TABLE)
    payload_shape = AliasProperty[ArtifactPayloadShape]("_payload_shape")


class ObjectLabelVariant(ABC, metaclass=AutoRegisterMeta):
    """A named label array carried beside an object set's final labels.

    The kernel declares only the final labels; a domain declares further
    variants (for example labels before editing) as subclasses.
    """

    __registry_key__ = "name"
    __skip_if_no_key__ = True

    name: ClassVar[str]


class FinalLabels(ObjectLabelVariant):
    """The object set's labels after every edit its producer made."""

    name = "final"


ObjectLabelVariants = Mapping[type[ObjectLabelVariant], "ObjectLabelData"]


def ordered_label_variants(
    variants: ObjectLabelVariants,
) -> MappingProxyType:
    """Freeze declared variants in name order, rejecting the final labels."""
    for variant in variants:
        if not (isinstance(variant, type) and issubclass(variant, ObjectLabelVariant)):
            raise TypeError(
                f"Object-label variants are keyed by ObjectLabelVariant classes, got {variant!r}."
            )
        if variant is FinalLabels:
            raise ValueError("Final labels are carried as labels, not as a variant.")
    return MappingProxyType(
        {variant: variants[variant] for variant in sorted(variants, key=lambda v: v.name)}
    )


@dataclass(frozen=True, slots=True)
class ObjectLabelVariantData:
    """Final object labels and the variants a domain declared beside them."""

    labels: ObjectLabelData
    variants: ObjectLabelVariants = field(default_factory=lambda: MappingProxyType({}))

    def __post_init__(self) -> None:
        object.__setattr__(self, "variants", ordered_label_variants(self.variants))

    @property
    def shape(self) -> tuple[int, ...] | None:
        return ObjectLabelStorageStrategy.for_value(self.labels).label_shape(self.labels)

    @property
    def dtype(self) -> Any:
        return self.labels.dtype

    def validate_plane_count(self, plane_count: int, context: str) -> None:
        object_label_validate_plane_count(
            self.labels, plane_count=plane_count, context=context,
        )

    @classmethod
    def compatible_replacement(
        cls,
        source: "ObjectLabelValue",
        labels: ObjectLabelData,
    ) -> "ObjectLabelVariantData":
        """Return replacement labels with source variants that still match."""
        source_variants = source.variant_data
        storage_authority = ObjectLabelStorageStrategy.for_value(source)
        matching = {
            variant: storage_authority.matching_variant(
                source,
                source_variants.variant_labels(variant),
                labels,
            )
            for variant in source_variants.present_variants[1:]
        }
        return cls(
            labels=labels,
            variants={
                variant: data for variant, data in matching.items() if data is not None
            },
        )

    @property
    def present_variants(self) -> tuple[type[ObjectLabelVariant], ...]:
        """Final labels first, then each declared variant in name order."""
        return (FinalLabels, *self.variants)

    def variant_labels(
        self,
        variant: type[ObjectLabelVariant],
    ) -> ObjectLabelData | None:
        """Return one variant's labels, or None when this object set lacks it."""
        if variant is FinalLabels:
            return self.labels
        return self.variants.get(variant)

    def labels_for_variant(
        self,
        variant: type[ObjectLabelVariant],
    ) -> ObjectLabelData:
        """Return one variant's labels, standing in the final labels when absent."""
        labels = self.variant_labels(variant)
        return self.labels if labels is None else labels

    def same_arrays_as(self, other: "ObjectLabelVariantData") -> bool:
        """Return whether both carry the identical array for every variant."""
        return self.present_variants == other.present_variants and all(
            self.variant_labels(variant) is other.variant_labels(variant)
            for variant in self.present_variants
        )

    @classmethod
    def variant_is_present(
        cls,
        variant: type[ObjectLabelVariant],
        payloads: Sequence["ObjectLabelVariantData"],
    ) -> bool:
        """Return whether a variant has material data in any payload."""
        return any(variant in payload.present_variants for payload in payloads)

    def with_labels(self, labels: ObjectLabelData) -> "ObjectLabelVariantData":
        """Return these variants with replacement final labels."""
        return ObjectLabelVariantData(
            labels=labels,
            variants={
                variant: self.variant_labels(variant)
                for variant in self.present_variants[1:]
            },
        )

    def project(
        self,
        projector: Callable[[ObjectLabelData], ObjectLabelData],
    ) -> "ObjectLabelVariantData":
        """Project every present variant through the same label operation."""
        return ObjectLabelVariantData(
            labels=projector(self.labels),
            variants={
                variant: projector(self.variant_labels(variant))
                for variant in self.present_variants[1:]
            },
        )

    def validate_representation(
        self,
        *,
        representation: ObjectLabelRepresentation,
        value_label: str,
    ) -> None:
        """Validate final and optional variants before admitting a label carrier."""
        label_data = self.labels
        if isinstance(label_data, ObjectLabelValue):
            raise TypeError(
                f"{value_label}.labels requires label data, not another "
                "ObjectLabelValue. Pass its variant_data explicitly instead."
            )
        final_authority = ObjectLabelStorageStrategy.for_value(label_data)
        final_authority.validate_representation(
            label_data,
            representation=representation,
            value_label=value_label,
        )
        for variant_type in self.present_variants[1:]:
            variant = self.variant_labels(variant_type)
            variant_name = f"{variant_type.name} labels"
            variant_authority = ObjectLabelStorageStrategy.for_value(variant)
            variant_authority.validate_representation(
                variant,
                representation=representation,
                value_label=f"{value_label} {variant_name}",
            )
            if variant_authority.matching_variant(variant, variant, label_data) is None:
                raise ValueError(
                    f"{value_label} {variant_name} shape "
                    f"{variant_authority.label_shape(variant)!r} does not match "
                    f"final labels shape {final_authority.label_shape(label_data)!r}."
                )

    def in_representation(
        self,
        representation: ObjectLabelRepresentation,
    ) -> "ObjectLabelVariantData":
        """Normalize every present variant through one declared representation."""
        return self.project(
            ObjectLabelSetReplacementStrategy.for_enum_member(
                representation
            ).replacement_labels
        )

    def project_runtime_slice(
        self,
        *,
        slice_index: int,
        slice_count: int,
    ) -> "ObjectLabelVariantData":
        """Project every present variant onto one runtime slice."""
        return self.project_plane(
            plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
            plane_index=slice_index,
            plane_count=slice_count,
        )

    def project_plane(
        self,
        *,
        plane_axis: RuntimePlaneAxis,
        plane_index: int,
        plane_count: int,
    ) -> "ObjectLabelVariantData":
        """Project every present variant onto one declared label plane."""
        return self.project(
            lambda labels: self.project_label_data_plane(
                labels,
                plane_axis=plane_axis,
                plane_index=plane_index,
                plane_count=plane_count,
            )
        )

    def project_planes(
        self, plane_indices: tuple[int, ...], *, plane_count: int,
    ) -> "ObjectLabelVariantData":
        """Project each variant through the same ordered plane selection."""
        return self.project(
            lambda labels: object_label_project_planes(
                labels, plane_indices, plane_count=plane_count,
            )
        )

    @staticmethod
    def project_label_data_plane(
        labels: ObjectLabelData,
        *,
        plane_axis: RuntimePlaneAxis,
        plane_index: int,
        plane_count: int,
    ) -> ObjectLabelData:
        """Project one object-label variant through nominal plane semantics."""
        return object_label_project_plane(
            labels,
            plane_index,
            plane_count=plane_count,
        )


class PlaneStackObjectLabelVariantData(ObjectLabelVariantData):
    """Ordered produced label planes with independent dense variant storage."""

    __slots__ = ("_planes", "_dense_variants", "_memory_type", "_shape", "_lock")

    def __init__(
        self, variants: Sequence[ObjectLabelVariantData], memory_type: str,
    ) -> None:
        from openhcs.core.memory import MemoryType, runtime_slice_stack_geometry

        target = MemoryType(memory_type)
        if target is not MemoryType.NUMPY:
            raise ValueError("Produced label planes require NumPy storage.")
        values = tuple(variants)
        if not values:
            raise ValueError("Object-label slice aggregation requires values.")
        present = (
            FinalLabels,
            *sorted(
                {variant for value in values for variant in value.present_variants[1:]},
                key=lambda variant: variant.name,
            ),
        )
        planes = {
            variant: tuple(value.labels_for_variant(variant) for value in values)
            for variant in present
        }
        geometry = runtime_slice_stack_geometry(planes[FinalLabels])
        for variant_planes in planes.values():
            ObjectLabelStorageStrategy.for_planes(variant_planes)
            if runtime_slice_stack_geometry(variant_planes).shape != geometry.shape:
                raise ValueError("Object-label variants must match final labels shape.")
        object.__setattr__(self, "_planes", planes)
        object.__setattr__(self, "_dense_variants", {})
        object.__setattr__(self, "_memory_type", memory_type)
        object.__setattr__(self, "_shape", geometry.shape)
        object.__setattr__(self, "_lock", Lock())

    def __repr__(self) -> str:
        return f"{type(self).__name__}(shape={self.shape!r}, variants={self.present_variants!r})"

    __hash__ = None

    def _dense_variant(self, variant: type[ObjectLabelVariant]) -> ObjectLabelData:
        with self._lock:
            if variant not in self._dense_variants:
                dense = object_label_stack_planes(self._planes[variant], self._memory_type)
                self._dense_variants[variant] = dense
                self._planes[variant] = tuple(dense[index] for index in range(len(dense)))
            return self._dense_variants[variant]

    @property
    def labels(self) -> ObjectLabelData:
        return self._dense_variant(FinalLabels)

    @property
    def variants(self) -> ObjectLabelVariants:
        return MappingProxyType(
            {variant: self._dense_variant(variant) for variant in self.present_variants[1:]}
        )

    def variant_labels(
        self, variant: type[ObjectLabelVariant],
    ) -> ObjectLabelData | None:
        if variant not in self.present_variants:
            return None
        return self._dense_variant(variant)

    @property
    def shape(self) -> tuple[int, ...]:
        return self._shape

    @property
    def dtype(self) -> Any:
        return np.result_type(*(plane.dtype for plane in self._planes[FinalLabels]))

    @property
    def present_variants(self) -> tuple[type[ObjectLabelVariant], ...]:
        return tuple(self._planes)

    def validate_plane_count(self, plane_count: int, context: str) -> None:
        if len(self.shape) < 3 or self.shape[0] != plane_count:
            raise ValueError(
                f"{context} declares {plane_count} plane(s), but dense label "
                f"storage has shape {self.shape!r}."
            )

    def validate_representation(
        self, *, representation: ObjectLabelRepresentation, value_label: str,
    ) -> None:
        for planes in self._planes.values():
            for plane in planes:
                ObjectLabelStorageStrategy.for_value(plane).validate_representation(
                    plane, representation=representation, value_label=value_label,
                )

    def in_representation(self, representation: ObjectLabelRepresentation) -> ObjectLabelVariantData:
        if representation is ObjectLabelRepresentation.DENSE_LABELS:
            self.validate_representation(representation=representation, value_label=type(self).__name__)
            return self
        return super().in_representation(representation)

    def project_plane(
        self, *, plane_axis: RuntimePlaneAxis, plane_index: int, plane_count: int,
    ) -> ObjectLabelVariantData:
        self.validate_plane_count(plane_count, "Object-label data plane projection")
        if plane_index < 0 or plane_index >= plane_count:
            raise IndexError(plane_index)
        return ObjectLabelPlaneVariantData(self, plane_index)

    def project_planes(
        self, plane_indices: tuple[int, ...], *, plane_count: int,
    ) -> ObjectLabelVariantData:
        self.validate_plane_count(plane_count, "Object-label data plane projection")
        if any(index < 0 or index >= plane_count for index in plane_indices):
            raise IndexError(plane_indices)
        return ProjectedObjectLabelVariantData(self, plane_indices)

    def __getstate__(self) -> dict[str, Any]:
        with self._lock:
            return {
                "variants": {
                    variant: self._dense_variants[variant]
                    if variant in self._dense_variants else planes
                    for variant, planes in self._planes.items()
                },
                "memory_type": self._memory_type,
                "shape": self.shape,
            }

    def __setstate__(self, state: dict[str, Any]) -> None:
        object.__setattr__(self, "_dense_variants", {
            variant: data for variant, data in state["variants"].items()
            if isinstance(data, np.ndarray)
        })
        object.__setattr__(self, "_planes", {
            variant: tuple(data[index] for index in range(len(data)))
            if isinstance(data, np.ndarray) else data
            for variant, data in state["variants"].items()
        })
        object.__setattr__(self, "_memory_type", state["memory_type"])
        object.__setattr__(self, "_shape", state["shape"])
        object.__setattr__(self, "_lock", Lock())


class ProjectedObjectLabelVariantData(PlaneStackObjectLabelVariantData):
    """A declared plane view of the canonical produced variant storage."""

    __slots__ = ("_source", "_indices")

    def __init__(
        self, source: PlaneStackObjectLabelVariantData, indices: tuple[int, ...],
    ) -> None:
        object.__setattr__(self, "_source", source)
        object.__setattr__(self, "_indices", indices)
        object.__setattr__(self, "_dense_variants", {})
        object.__setattr__(self, "_lock", Lock())
        object.__setattr__(self, "_shape", (len(indices), *source.shape[1:]))

    @property
    def present_variants(self) -> tuple[type[ObjectLabelVariant], ...]:
        return self._source.present_variants

    @property
    def dtype(self) -> Any:
        return self._source.dtype

    def _dense_variant(self, variant: type[ObjectLabelVariant]) -> ObjectLabelData:
        with self._lock:
            if variant not in self._dense_variants:
                source = self._source._dense_variant(variant)
                self._dense_variants[variant] = self._project_variant(source)
            return self._dense_variants[variant]

    def _project_variant(self, source: ObjectLabelData) -> ObjectLabelData:
        return object_label_project_planes(
            source, self._indices, plane_count=self._source.shape[0],
        )

    def validate_representation(
        self, *, representation: ObjectLabelRepresentation, value_label: str,
    ) -> None:
        self._source.validate_representation(
            representation=representation, value_label=value_label,
        )

    def __reduce__(self):
        # A transported scalar/subset owns only its selected canonical buffers.
        return (ObjectLabelVariantData, (self.labels, dict(self.variants)))


class ObjectLabelPlaneVariantData(ProjectedObjectLabelVariantData):
    """A scalar plane view retaining canonical per-variant write ownership."""

    __slots__ = ()

    def __init__(self, source: PlaneStackObjectLabelVariantData, index: int) -> None:
        super().__init__(source, (index,))
        object.__setattr__(self, "_shape", source.shape[1:])

    def _project_variant(self, source: ObjectLabelData) -> ObjectLabelData:
        return object_label_project_plane(
            source, self._indices[0], plane_count=self._source.shape[0],
        )


@dataclass(kw_only=True)
class ObjectLabelValue(
    SourceImageProvenanceFields,
    SourceSpatialDomainFields,
    ObjectLabelDomainMetadata,
    runtime_image_values.ImagePayload,
    RuntimeSliceIdentityProjectableValue,
    ABC,
):
    """Nominal object-label carrier with dense labels and domain metadata."""

    variant_data: ObjectLabelVariantData
    representation: ObjectLabelRepresentation
    domain: ObjectLabelDomain
    plane_axis: RuntimePlaneAxis | None
    parent_image_source_voxel_spacing: SourceVoxelSpacing

    def object_label_domain(self) -> ObjectLabelDomain:
        return self.domain

    def measurement_object_row_identity(
        self,
        declared_identity: MeasurementObjectRowIdentity,
    ) -> MeasurementObjectRowIdentity:
        """Project declared row identity through this label value's domain scope."""
        return ObjectLabelPlaneDomainStrategy.for_enum_member(
            self.domain.scope
        ).measurement_object_row_identity(declared_identity)

    def validate_object_label_variants(self) -> None:
        if not isinstance(self.variant_data, ObjectLabelVariantData):
            raise TypeError(
                f"{type(self).__name__}.variant_data requires ObjectLabelVariantData."
            )

    @property
    def labels(self) -> ObjectLabelData:
        return self.variant_data.labels

    @property
    def shape(self) -> Any:
        return self.variant_data.shape

    @property
    def ndim(self) -> int:
        return len(self.shape)

    @property
    def dtype(self) -> Any:
        return self.variant_data.dtype

    def __array__(self, dtype: Any | None = None) -> Any:
        return np.asarray(self.labels, dtype=dtype)

    @property
    def data(self) -> np.ndarray:
        """Return dense categorical pixels for image-domain consumers."""
        return object_label_dense_array(self)

    def array_payload_data(self) -> Any:
        return self.labels

    def with_data(self, data: Any) -> Self:
        return self.with_labels(data)

    def __getitem__(self, key: Any) -> Any:
        return self.labels[key]

    def __len__(self) -> int:
        return len(self.labels)

    def variant_labels(
        self, variant: type[ObjectLabelVariant],
    ) -> ObjectLabelData | None:
        """Return one declared label variant, or None when absent."""
        return self.variant_data.variant_labels(variant)

    @property
    def metadata(self) -> runtime_image_values.ImagePayloadMetadata:
        """Return image-domain metadata carried by this object-label value."""

        return runtime_image_values.ImagePayloadMetadata(
            source_provenance=self.source_provenance,
            source_spatial_domain=self.source_spatial_domain,
            source_voxel_spacing=self.parent_image_source_voxel_spacing,
            plane_axis=self.plane_axis,
        )

    def measurement_reference_image(self) -> runtime_array_values.RuntimeArrayData:
        """Return an image payload in this value's exact object-label domain."""

        labels = object_label_dense_array(self)
        domain_strategy = ObjectLabelPlaneDomainStrategy.for_enum_member(
            self.object_label_domain().scope
        )
        metadata = self.metadata.with_source_provenance(
            domain_strategy.measurement_reference_source_provenance(self)
        )
        return metadata.payload_with(
            np.zeros(labels.shape, dtype=np.float32),
        )

    def declared_plane_projection(self) -> RuntimePlaneAxisValueProjection | None:
        """Return the exact runtime plane axis declared by this label value."""
        domain = self.object_label_domain()
        return ObjectLabelPlaneDomainStrategy.for_enum_member(
            domain.scope
        ).value_projection(self)

    def measurement_planes(self) -> tuple["ObjectLabelValue", ...]:
        """Return values projected through the declared label-plane domain."""
        return ObjectLabelPlaneDomainStrategy.for_enum_member(
            self.object_label_domain().scope
        ).declared_measurement_planes(self)

    def measurement_plane_domains(self) -> tuple[tuple[int, ...], ...]:
        """Return object-ID domains in declared measurement-plane order."""
        domain = self.object_label_domain()
        return ObjectLabelPlaneDomainStrategy.for_enum_member(
            domain.scope
        ).plane_domains(
            self,
            domain=domain,
        )

    def runtime_slice_plane_count(self) -> int | None:
        """Return the declared runtime-slice plane count, when present."""
        projection = self.declared_plane_projection()
        if projection is None or projection.axis is not RuntimePlaneAxis.RUNTIME_SLICE:
            return None
        return projection.axis_size

    # -- RuntimeSliceProjectableValue -------------------------------------

    def runtime_slice_count(self) -> int | None:
        if self.plane_axis is not RuntimePlaneAxis.RUNTIME_SLICE:
            return None
        plane_count = self.declared_plane_count()
        if plane_count is None:
            from openhcs.core.runtime_slice_projection import (
                RuntimeSliceProjectionDeclarationError,
            )

            raise RuntimeSliceProjectionDeclarationError(
                "Runtime-slice object labels have no nominal plane-stack contract."
            )
        return plane_count

    def value_for_slice(
        self, context: RuntimePlaneAxisValueProjection
    ) -> "ObjectLabelValue":
        if self.plane_axis is not context.axis:
            return self
        plane_count = self.declared_plane_count()
        if plane_count is None:
            from openhcs.core.runtime_slice_projection import (
                RuntimeSliceProjectionDeclarationError,
            )

            raise RuntimeSliceProjectionDeclarationError(
                "Object labels have no nominal plane-stack contract for their "
                f"declared {context.axis.value!r} axis."
            )
        if plane_count != context.axis_size:
            raise ValueError(
                "Object-label runtime plane-axis cardinality mismatch: "
                f"declared {plane_count!r}, execution requires {context.axis_size}."
            )
        source_plane_count = self.source_provenance.source_plane_count
        if source_plane_count not in (0, context.axis_size):
            raise ValueError(
                "Object-label source provenance must be absent or exactly match "
                f"the declared plane axis: {source_plane_count} != {context.axis_size}."
            )
        return self.project_source_plane(context.require_plane_index())

    def aligned_value(self, resolver: Any) -> Any:
        slice_count = self.runtime_slice_plane_count()
        projected: ObjectLabelValue = self
        if slice_count is not None:
            if slice_count != resolver.projection_axis.axis_size:
                raise ValueError(
                    "Runtime-slice object-label cardinality must exactly match the "
                    f"declared projection axis: {slice_count} != "
                    f"{resolver.projection_axis.axis_size}."
                )
            projected = self.value_for_slice(resolver.projection_axis)
        return resolver.resolve_source_spatial_value(projected)

    def project_declared_source(self, source_image_name: str) -> "ObjectLabelValue":
        """Object labels keep their context; image-axis projection does not apply."""
        del source_image_name
        return self

    def spatial_adapter(
        self,
        *,
        source_shape_override_yx: tuple[int, int] | None = None,
    ) -> Any:
        """Place every label variant in this value's source domain."""
        from openhcs.core.aligned_image_payload import (
            ObjectLabelPayloadSourceSpatialDomainAdapter,
        )

        return ObjectLabelPayloadSourceSpatialDomainAdapter(
            self, source_shape_override_yx=source_shape_override_yx,
        )

    # -- derived image outputs ------------------------------------------------

    def requires_output_plane_contextualization(
        self,
        output: runtime_image_values.ImagePayload,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> bool:
        """A volume label source binds an output's undeclared plane axis, even at depth one."""
        del output
        return (
            plane_projection is not None
            and plane_projection.plane_index is None
            and self.metadata.plane_axis is None
            and not self.metadata.persists_whole_image()
            and np.ndim(object_label_dense_array(self)) >= 3
        )

    def contextualize_image_output(
        self,
        output: runtime_image_values.ImagePayload,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> runtime_image_values.ImagePayload:
        """Project an image rendered from these labels onto the invocation plane axis."""
        source_metadata = self.metadata
        if source_metadata.persists_whole_image():
            return source_metadata.derive_payload(self, output, plane_projection=None)
        if plane_projection is None or plane_projection.plane_index is not None:
            return source_metadata.derive_payload(
                self, output, plane_projection=plane_projection,
            )
        plane_count = source_metadata.source_provenance.source_plane_count
        if plane_count != plane_projection.axis_size:
            raise ValueError(
                "Object-label image output source-plane provenance must match the "
                "declared runtime plane axis: "
                f"{plane_count} != {plane_projection.axis_size}."
            )
        plane_projection.validate_shape(
            output.geometry.shape,
            value_name="Object-label image output payload",
        )
        contextualized_output = output.metadata.replace_fields(
            plane_axis=plane_projection.axis,
        ).attach_to(output)
        return source_metadata.derive_payload(
            self, contextualized_output, plane_projection=plane_projection,
        )

    def object_label_output(
        self,
        source: Any,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> "ObjectLabelValue":
        """Keep this label domain, filling missing source-image context from ``source``."""
        del plane_projection
        return self.with_source_image_context(source).with_parent_image_context(source)

    def alignment_slices(self) -> tuple[Any, ...]:
        slice_count = self.runtime_slice_plane_count()
        if slice_count is None:
            return (self,)
        projection = RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE, axis_size=slice_count,
        )
        return tuple(
            self.value_for_slice(projection.selected_plane(index))
            for index in range(slice_count)
        )

    def declared_plane_count(self) -> int | None:
        """Return this value's validated plane-scoped label cardinality."""
        if self.domain.scope is not ObjectLabelDomainScope.PLANE:
            return None
        declared_domains = self.domain.declared_object_id_domains
        if not declared_domains:
            raise ValueError(
                f"{type(self).__name__} declares plane-scoped labels without one "
                "object-ID domain per plane."
            )
        plane_count = len(declared_domains)
        self.variant_data.validate_plane_count(plane_count, type(self).__name__)
        return plane_count

    def validate_source_alignment(self, label_name: str) -> None:
        """Validate source-addressable provenance for every declared label plane."""
        if self.domain.scope is ObjectLabelDomainScope.PAYLOAD:
            return
        if self.domain.scope is not ObjectLabelDomainScope.PLANE:
            raise TypeError(
                f"Unsupported object-label domain scope {self.domain.scope!r}."
            )
        plane_count = self.declared_plane_count()
        if plane_count is None:
            raise ValueError(
                f"Plane-scoped object labels {label_name!r} require a declared "
                "object-label plane stack."
            )
        SourceImageProvenancePlaneCountRequirement(
            provenance=self.source_provenance,
            expected_count=plane_count,
            label_name=label_name,
        ).validate()
        for plane_index in range(plane_count):
            SourceImageProvenanceAddressRequirement(
                provenance=self.source_provenance.for_source_plane(plane_index),
                label_name=label_name,
                plane_index=plane_index,
            ).validate()

    @property
    def source_image_name(self) -> str | None:
        """Return the semantic source image name when this carrier has one."""
        return None

    @property
    def source_aliases(self) -> tuple[str, ...]:
        """Return source-binding aliases carried by this object-label value."""
        aliases = tuple(
            dict.fromkeys(alias for alias in self.source_image_names if alias)
        )
        if aliases:
            return aliases
        source_image_name = self.source_image_name
        if source_image_name is not None:
            return (source_image_name,)
        return ()

    @property
    def dimensions(self) -> tuple[str, ...]:
        """Return schema dimensions carried by native object-label values."""
        return ()

    def with_variants(
        self,
        variants: "ObjectLabelVariantData",
        *,
        representation: ObjectLabelRepresentation | None = None,
        domain: ObjectLabelDomain | None = None,
        source_provenance: SourceImageProvenance | None = None,
        source_spatial_domain: SourceSpatialDomain | None = None,
        parent_image_source_voxel_spacing: SourceVoxelSpacing | None = None,
        plane_axis: RuntimePlaneAxis | None | object = _PRESERVE_PLANE_AXIS,
    ) -> Self:
        """Return this nominal carrier with exact replacement label semantics."""
        selected_representation = (
            self.representation if representation is None else representation
        )
        selected_domain = self.domain if domain is None else domain
        selected_plane_axis = (
            ObjectLabelPlaneDomainStrategy.for_enum_member(
                selected_domain.scope
            ).value_plane_axis(self.plane_axis)
            if plane_axis is _PRESERVE_PLANE_AXIS
            else plane_axis
        )
        normalized_variants = variants.in_representation(selected_representation)
        return self.replace_fields(
            variant_data=normalized_variants,
            representation=selected_representation,
            domain=selected_domain,
            source_provenance=(
                self.source_provenance
                if source_provenance is None
                else source_provenance
            ),
            source_spatial_domain=(
                self.source_spatial_domain
                if source_spatial_domain is None
                else source_spatial_domain
            ),
            parent_image_source_voxel_spacing=(
                self.parent_image_source_voxel_spacing
                if parent_image_source_voxel_spacing is None
                else parent_image_source_voxel_spacing
            ),
            plane_axis=selected_plane_axis,
        )

    def with_replacement_labels(
        self,
        labels: ObjectLabelData,
        *,
        representation: ObjectLabelRepresentation | None = None,
        domain: ObjectLabelDomain | None = None,
        source_spatial_domain: SourceSpatialDomain | None = None,
    ) -> Self:
        """Return compatible replacement labels in this nominal carrier."""
        return self.with_variants(
            ObjectLabelVariantData.compatible_replacement(self, labels),
            representation=representation,
            domain=domain,
            source_spatial_domain=source_spatial_domain,
        )

    def with_labels(
        self,
        labels: ObjectLabelData,
        *,
        variants: ObjectLabelVariants = MappingProxyType({}),
    ) -> "ObjectLabelValue":
        """Return this carrier's metadata with replacement labels."""
        return self.with_variants(ObjectLabelVariantData(labels, variants))

    def with_projected_plane(
        self,
        labels: ObjectLabelData,
        plane_index: int,
        *,
        variants: ObjectLabelVariants = MappingProxyType({}),
    ) -> "ObjectLabelValue":
        """Return one selected label plane with projected domain metadata."""
        return self.with_variants(
            ObjectLabelVariantData(labels, variants),
            domain=object_label_domain_for_projected_label_plane(self, plane_index),
            source_provenance=self.source_provenance.for_source_plane(plane_index),
            plane_axis=None,
        )

    def with_measurement_labels(self, labels: ObjectLabelData) -> Self:
        """Return measurement-time labels in this value's declared domain."""
        variants = ObjectLabelVariantData.compatible_replacement(self, labels)
        if self.domain.scope is ObjectLabelDomainScope.PLANE:
            plane_count = self.declared_plane_count()
            if plane_count is None:
                raise ValueError(
                    "Plane-scoped object-label replacement has no declared plane count."
                )
            object_label_validate_plane_count(
                variants.labels,
                plane_count=plane_count,
                context="Object-label measurement replacement",
            )
        if (
            variants.same_arrays_as(self.variant_data)
        ):
            return self
        return self.with_variants(variants)

    def project_source_plane(
        self,
        plane_index: int,
        *,
        labels: ObjectLabelData | None = None,
    ) -> Self:
        """Return measurement labels projected from one declared source plane."""
        plane_count = self.declared_plane_count()
        if plane_count is None:
            raise ValueError(
                "Source-plane measurement projection requires plane-scoped labels."
            )
        if plane_index < 0 or plane_index >= plane_count:
            raise IndexError(plane_index)
        variants = self.variant_data.project_plane(
            plane_axis=self.plane_axis,
            plane_index=plane_index,
            plane_count=plane_count,
        )
        if labels is not None:
            variants = variants.with_labels(labels)
        return self.with_variants(
            variants,
            domain=object_label_domain_for_projected_label_plane(self, plane_index),
            source_provenance=self.source_provenance.for_source_plane(plane_index),
            plane_axis=None,
        )

    def with_runtime_slice_projection(
        self,
        *,
        slice_index: int,
        slice_count: int,
        label_plane_indices: tuple[int, ...] | None,
        source_plane_indices: tuple[int, ...] | None,
    ) -> "ObjectLabelValue":
        """Return this carrier projected onto one runtime slice."""
        if self.plane_axis is None:
            return self
        source_variants = self.variant_data
        variants = (
            (
                source_variants.project_plane(
                    plane_axis=self.plane_axis,
                    plane_index=label_plane_indices[0],
                    plane_count=len(self.domain.declared_object_id_domains),
                )
                if len(label_plane_indices) == 1
                else source_variants.project_planes(
                    label_plane_indices,
                    plane_count=len(self.domain.declared_object_id_domains),
                )
            )
            if label_plane_indices is not None
            else source_variants.project_runtime_slice(
                slice_index=slice_index, slice_count=slice_count,
            )
        )
        projected_domain = self.runtime_slice_domain(
            slice_index=slice_index,
            slice_count=slice_count,
            plane_indices=label_plane_indices,
        )
        projected_plane_count = (
            len(projected_domain.declared_object_id_domains)
            if projected_domain.scope is ObjectLabelDomainScope.PLANE
            else 1
        )
        projected_axis = RuntimePlaneAxisStrategy.for_enum_member(
            self.plane_axis
        ).projected_axis(projected_plane_count)
        slice_metadata = self.metadata.for_grouped_source_plane_projection(
            source_plane_indices=source_plane_indices,
            runtime_plane_index=slice_index,
            runtime_plane_count=slice_count,
        )
        return self.with_variants(
            variants,
            domain=projected_domain,
            source_provenance=slice_metadata.source_provenance,
            source_spatial_domain=slice_metadata.object_label_source_spatial_domain(),
            plane_axis=projected_axis,
        )

    def with_plane_projection(
        self,
        plane_indices: Sequence[int],
    ) -> "ObjectLabelValue":
        """Return the ordered subset of planes selected by component scope."""
        normalized_indices = tuple(int(index) for index in plane_indices)
        if not normalized_indices:
            raise ValueError("Object-label plane projection cannot be empty.")
        plane_count = self.declared_plane_count()
        if plane_count is None:
            raise ValueError("Object-label plane projection requires a plane stack.")
        invalid_indices = tuple(
            index for index in normalized_indices if index < 0 or index >= plane_count
        )
        if invalid_indices:
            raise IndexError(
                "Object-label plane projection indices must be within "
                f"0..{plane_count - 1}; got {invalid_indices!r}."
            )
        if normalized_indices == tuple(range(plane_count)):
            return self
        metadata = self.metadata.for_source_planes(
            normalized_indices
        )
        variants = self.variant_data.project_planes(
            normalized_indices, plane_count=plane_count,
        )
        return self.with_variants(
            variants,
            domain=self.object_label_domain().project_planes(normalized_indices),
            source_provenance=metadata.source_provenance,
        )

    def with_runtime_slice_identity(
        self,
        *,
        slice_index: int,
        slice_count: int,
    ) -> Self:
        """Return this object-label carrier stamped with execution-slice identity."""
        del slice_index, slice_count
        return self

    def normalize_object_label_metadata(
        self,
        value_label: str,
    ) -> ObjectLabelRepresentation:
        """Normalize shared object-label domain and provenance fields."""
        if not isinstance(self.domain, ObjectLabelDomain):
            raise TypeError(
                f"{value_label}.domain requires ObjectLabelDomain, "
                f"got {type(self.domain).__name__}."
            )
        self.representation = ObjectLabelRepresentation(
            self.representation,
        )
        if self.plane_axis is not None:
            self.plane_axis = RuntimePlaneAxis(
                self.plane_axis,
            )
        if self.domain.scope is ObjectLabelDomainScope.PAYLOAD:
            if self.plane_axis is not None:
                raise ValueError(
                    f"{value_label} payload-scoped labels cannot declare a plane axis."
                )
        elif self.domain.scope is ObjectLabelDomainScope.PLANE:
            if self.plane_axis is None:
                raise ValueError(
                    f"{value_label} plane-scoped labels require a declared plane axis."
                )
            declared_domains = self.domain.declared_object_id_domains
            self.variant_data.validate_plane_count(len(declared_domains), value_label)
        else:
            raise TypeError(
                f"{value_label} has unsupported object-label domain scope "
                f"{self.domain.scope!r}."
            )
        self.normalize_source_spatial_domain_fields()
        self.normalize_source_provenance_fields()
        ObjectLabelStorageStrategy.for_value(self).validate_representation(
            self,
            representation=self.representation,
            value_label=value_label,
        )
        return self.representation

    def runtime_slice_domain(
        self,
        *,
        slice_index: int,
        slice_count: int,
        plane_indices: tuple[int, ...] | None = None,
    ) -> ObjectLabelDomain:
        """Return the object-id domain represented by one runtime slice."""
        domain = self.object_label_domain()
        if plane_indices is not None:
            return domain.project_planes(plane_indices)
        return domain.project_slice(slice_index, slice_count)

    def object_label_source_spatial_domain(self) -> SourceSpatialDomain:
        """Return this value's source-image coordinate domain."""
        return self.source_spatial_domain.with_value_name(
            runtime_image_values.OBJECT_LABEL_SOURCE_SPATIAL_VALUE_NAME,
        )

    def apply_source_spatial_coordinate_offset(
        self,
        feature_values: MutableMapping[str, np.ndarray],
        *,
        x_fields: Sequence[str],
        y_fields: Sequence[str],
        local_offset_yx: tuple[int, int] = (0, 0),
    ) -> None:
        """Project local object-coordinate feature arrays into source-image XY."""
        source_origin = self.object_label_source_spatial_domain().origin_yx
        origin_yx = source_origin if source_origin is not None else (0, 0)
        offset_y = int(origin_yx[0]) + int(local_offset_yx[0])
        offset_x = int(origin_yx[1]) + int(local_offset_yx[1])
        if offset_x:
            for field in x_fields:
                if field in feature_values:
                    feature_values[field] = (
                        np.asarray(feature_values[field], dtype=float) + offset_x
                    )
        if offset_y:
            for field in y_fields:
                if field in feature_values:
                    feature_values[field] = (
                        np.asarray(feature_values[field], dtype=float) + offset_y
                    )

    def object_label_semantic_identity(self) -> tuple[tuple[str, Hashable], ...]:
        """Return the declared semantic identity for label-domain batching."""
        source_spatial_domain = self.object_label_source_spatial_domain()
        return (
            ("carrier", (type(self).__module__, type(self).__qualname__)),
            ("representation", self.representation),
            ("domain", self.object_label_domain()),
            ("plane_axis", self.plane_axis),
            ("source_provenance", self.source_provenance.equality_identity),
            (
                "source_spatial_domain",
                (
                    source_spatial_domain.origin_yx,
                    source_spatial_domain.source_shape_yx,
                    repr(source_spatial_domain.fill_value),
                    source_spatial_domain.value_name,
                ),
            ),
        )

    def object_label_dense_projection_identity(
        self,
    ) -> tuple[tuple[str, Hashable], ...]:
        """Return label identity for caches that already hold aligned dense data."""
        return (
            ("carrier", (type(self).__module__, type(self).__qualname__)),
            ("representation", self.representation),
            ("domain", self.object_label_domain()),
            ("plane_axis", self.plane_axis),
            ("source_provenance", self.source_provenance.equality_identity),
        )

    def with_source_image_context(
        self, image: runtime_array_values.RuntimeArrayData
    ) -> Self:
        """Return this object-label value with missing provenance filled from image."""
        metadata = image.metadata
        return self.with_variants(
            self.variant_data,
            source_provenance=object_label_source_context_provenance(self, image),
            source_spatial_domain=(
                self.object_label_source_spatial_domain().with_missing_from(
                    metadata.object_label_source_spatial_domain()
                )
            ),
        )

    def with_parent_image_context(
        self,
        image: runtime_array_values.RuntimeArrayData,
    ) -> "ObjectLabelValue":
        """Return this value with missing CellProfiler parent-image spacing filled."""
        parent_spacing = self.parent_image_source_voxel_spacing.with_missing_from(
            image.metadata.source_voxel_spacing
        )
        return self.with_variants(
            self.variant_data,
            parent_image_source_voxel_spacing=parent_spacing,
        )


def object_label_source_context_provenance(
    label: ObjectLabelValue,
    image: runtime_array_values.RuntimeArrayData,
) -> SourceImageProvenance:
    """Merge image provenance into labels without reviving stale stack axes."""
    label_provenance = label.source_provenance
    image_provenance = image.metadata.source_provenance
    if label.domain.scope is ObjectLabelDomainScope.PLANE:
        plane_count = label.declared_plane_count()
        if plane_count is None:
            raise ValueError(
                "Plane-scoped object-label source context requires a declared "
                "label-plane count."
            )
        if image_provenance.source_plane_count == 0:
            if plane_count == 1:
                image_provenance = runtime_image_values.ImagePayloadMetadata.compose(
                    (image,),
                    mode=(
                        runtime_image_values.ImagePayloadMetadataCompositionMode.STACK
                    ),
                ).source_provenance
            else:
                image_provenance = SourcePlaneIndexedProvenanceExpansion(
                    image_provenance,
                    expected_plane_count=plane_count,
                ).expanded()
        return image_provenance.with_missing_from(
            label_provenance
        ).with_common_scalar_identity_from_planes()
    merged = label_provenance.with_missing_from(image_provenance)
    if not (label_provenance.addressable and label_provenance.source_plane_count == 0):
        return merged
    names = merged.source_image_names
    if len(names) > 1:
        unique_names = tuple(dict.fromkeys(names))
        names = unique_names if len(unique_names) == 1 else ()
    return SourceImageProvenance(
        source_path=merged.source_path,
        source_component_metadata=merged.source_component_metadata,
        source_image_names=names,
    )


@dataclass(slots=True)
class ObjectLabelPayload(ObjectLabelValue):
    """Dense object labels plus optional semantic label variants."""

    representation: ObjectLabelRepresentation = ObjectLabelRepresentation.DENSE_LABELS
    domain: ObjectLabelDomain = field(default_factory=ObjectLabelDomain)
    plane_axis: RuntimePlaneAxis | None = None
    parent_image_source_voxel_spacing: SourceVoxelSpacing = field(
        default_factory=SourceVoxelSpacing
    )

    def __post_init__(self, *source_provenance_values: object) -> None:
        self.validate_object_label_variants()
        self.absorb_explicit_source_provenance(source_provenance_values)
        self.normalize_object_label_metadata("ObjectLabelPayload")


ObjectLabelData = np.ndarray | SparseIJVLabelRows

ObjectLabelValueBuildSource = (
    ObjectLabelValue | ObjectLabelDomainMetadata | ObjectLabelData
)

ObjectLabelMeasurementSource = ObjectLabelValue | ObjectLabelData


class ObjectLabelDataDomainMetadataStrategy(ObjectLabelDomainMetadataStrategy):
    """Dense and sparse label data declares no independent identity domain."""

    value_type = (np.ndarray, SparseIJVLabelRows)

    def object_label_domain(self, value: object) -> ObjectLabelDomain:
        del value
        return ObjectLabelDomain()


@dataclass(slots=True, kw_only=True)
class ObjectLabelSet(ObjectLabelValue, NamedArtifactPayload):
    """Native OpenHCS object-label value."""

    name: str
    dimensions: tuple[str, ...] = ()
    source_image_name: str | None = None
    representation: ObjectLabelRepresentation = ObjectLabelRepresentation.DENSE_LABELS
    domain: ObjectLabelDomain = field(default_factory=ObjectLabelDomain)
    plane_axis: RuntimePlaneAxis | None = None
    parent_image_source_voxel_spacing: SourceVoxelSpacing = field(
        default_factory=SourceVoxelSpacing
    )

    def project_declared_source(self, source_image_name: str) -> "ObjectLabelSet":
        """A named label set resolves only its own declared source name."""
        if self.name != source_image_name:
            raise ValueError(
                f"Object-label payload {self.name!r} cannot resolve declared "
                f"source {source_image_name!r}."
            )
        return self

    @classmethod
    def from_payload(
        cls,
        name: str,
        payload: ObjectLabelValue,
        *,
        dimensions: tuple[str, ...] = (),
        source_image_name: str | None = None,
        source_image_payload: runtime_array_values.RuntimeArrayData | None = None,
        parent_image_payload: runtime_array_values.RuntimeArrayData | None = None,
        source_image_names: tuple[str, ...] = (),
    ) -> Self:
        """Admit a named label value with its resolved source and parent context."""
        variants = payload.variant_data
        provenance = payload.source_provenance
        spatial_domain = payload.source_spatial_domain
        plane_axis = payload.plane_axis
        if source_image_payload is not None:
            metadata = source_image_payload.metadata
            provenance = object_label_source_context_provenance(
                payload, source_image_payload
            )
            spatial_domain = (
                payload.object_label_source_spatial_domain().with_missing_from(
                    metadata.object_label_source_spatial_domain()
                )
            )
            plane_axis = ObjectLabelPlaneDomainStrategy.for_enum_member(
                payload.domain.scope
            ).value_plane_axis(payload.plane_axis)
            variants = variants.in_representation(payload.representation)
            if isinstance(payload, ObjectLabelSet):
                payload.validate_artifact_name()
                if payload.source_image_name == "":
                    raise ValueError("ObjectLabelSet.source_image_name cannot be empty.")
            variants.validate_representation(
                representation=ObjectLabelRepresentation(payload.representation),
                value_label=type(payload).__name__,
            )
        spacing = payload.parent_image_source_voxel_spacing
        if parent_image_payload is not None:
            spacing = spacing.with_missing_from(
                parent_image_payload.metadata.source_voxel_spacing
            )
        fallback_names = source_image_names
        if not fallback_names and source_image_payload is not None:
            fallback_names = source_image_payload.metadata.source_image_names
        if fallback_names:
            provenance = provenance.with_source_image_names(
                provenance.source_image_names or fallback_names
            )
        return cls(
            name=name,
            dimensions=dimensions,
            source_image_name=source_image_name,
            variant_data=variants,
            representation=payload.representation,
            domain=payload.domain,
            plane_axis=plane_axis,
            source_spatial_domain=spatial_domain,
            parent_image_source_voxel_spacing=spacing,
            source_provenance=provenance,
        )

    def __post_init__(self, *source_provenance_values: object) -> None:
        self.validate_object_label_variants()
        self.absorb_explicit_source_provenance(source_provenance_values)
        self.validate_artifact_name()
        if self.source_image_name == "":
            raise ValueError("ObjectLabelSet.source_image_name cannot be empty.")
        self.normalize_object_label_metadata(f"ObjectLabelSet '{self.name}'")

    def source_alias_plane_index(
        self,
        source_aliases: tuple[str, ...],
        axis_size: int,
    ) -> int | None:
        """Resolve source aliases only when this label set declares that axis."""
        if self.plane_axis is not RuntimePlaneAxis.SOURCE_BINDING:
            return None
        return self.source_provenance.source_alias_plane_index(
            source_aliases,
            axis_size,
        )

    def object_label_semantic_identity(self) -> tuple[tuple[str, Hashable], ...]:
        """Return native object-label identity fields in addition to payload metadata."""
        return (
            *ObjectLabelValue.object_label_semantic_identity(self),
            ("object_name", self.name),
            ("dimensions", self.dimensions),
            ("source_image_name", self.source_image_name),
        )

    def object_label_dense_projection_identity(
        self,
    ) -> tuple[tuple[str, Hashable], ...]:
        """Return native dense-projection identity fields for label caches."""
        return (
            *ObjectLabelValue.object_label_dense_projection_identity(self),
            ("object_name", self.name),
            ("dimensions", self.dimensions),
            ("source_image_name", self.source_image_name),
        )


class ObjectLabelValueIdDomainStrategy(ObjectLabelIdDomainStrategy):
    """Extract present object IDs from nominal object-label values."""

    value_type = ObjectLabelValue

    def present_ids(self, labels: Any) -> tuple[int, ...]:
        label_value = cast(ObjectLabelValue, labels)
        return ObjectLabelIdDomainStrategy.for_value(label_value.labels).present_ids(
            label_value.labels
        )


class ObjectLabelStorageStrategy(
    NominalTypeStrategyFamilyMixin,
    ABC,
    metaclass=AutoRegisterMeta,
):
    """Single nominal authority for object-label storage behavior."""

    @classmethod
    def for_value(cls, labels: object) -> "ObjectLabelStorageStrategy":
        return cls.require_nominal_value(
            labels,
            context="Object-label storage",
        )

    @classmethod
    def for_planes(cls, labels: Sequence[ObjectLabelData]) -> "ObjectLabelStorageStrategy":
        """Admit one homogeneous semantic plane family before stacking."""
        if not labels:
            raise ValueError("Object-label plane stacking requires values.")
        authority = cls.for_value(labels[0])
        if any(type(value) is not type(labels[0]) for value in labels[1:]):
            raise TypeError("Object-label plane stacking requires one nominal storage type.")
        return authority

    @abstractmethod
    def storage_representation(
        self,
        labels: object,
    ) -> ObjectLabelRepresentation:
        """Return the representation owned by the label storage."""

    @abstractmethod
    def dense_data(
        self,
        labels: object,
        *,
        source_spatial_shape_yx: tuple[int, int] | None,
    ) -> np.ndarray:
        """Materialize dense labels from this storage."""

    def rendering_layers(
        self, labels: object, *, source_spatial_shape_yx: tuple[int, int] | None,
    ) -> tuple[np.ndarray, ...]:
        """Return nonoverlapping dense layers for image rendering consumers."""
        return (self.dense_data(labels, source_spatial_shape_yx=source_spatial_shape_yx),)

    @abstractmethod
    def sparse_ijv_rows(self, labels: object) -> SparseIJVLabelRows:
        """Materialize sparse-IJV rows from this storage."""

    @abstractmethod
    def stack_planes(
        self,
        labels: Sequence[object],
        memory_type: str,
    ) -> ObjectLabelData:
        """Stack homogeneous semantic planes in this storage representation."""

    def axis_centers(
        self,
        labels: object,
        *,
        domain: Sequence[int],
    ) -> tuple[tuple[np.ndarray, ...], np.ndarray]:
        """Reduce object coordinates without erasing storage representation."""
        sparse_labels = self.sparse_ijv_rows(labels)
        array = sparse_labels.as_array()
        object_ids = array[:, sparse_labels.label_column].astype(
            np.int64,
            copy=False,
        )
        max_domain_label = max(domain, default=0)
        max_label = max(int(object_ids.max(initial=0)), max_domain_label)
        counts = np.bincount(object_ids, minlength=max_label + 1)
        coordinate_columns = (
            (
                sparse_labels.slice_column,
                sparse_labels.y_column,
                sparse_labels.x_column,
            )
            if sparse_labels.has_slice_index
            else (sparse_labels.y_column, sparse_labels.x_column)
        )
        return self.coordinate_centers(
            counts,
            (
                np.bincount(
                    object_ids,
                    weights=array[:, coordinate_column],
                    minlength=max_label + 1,
                )
                for coordinate_column in coordinate_columns
            ),
            maximum_label=max_label,
        )

    @staticmethod
    def coordinate_centers(
        counts: np.ndarray,
        coordinate_sums: Iterable[np.ndarray],
        *,
        maximum_label: int,
    ) -> tuple[tuple[np.ndarray, ...], np.ndarray]:
        """Allocate and divide each coordinate sum in its declared ID domain."""
        axis_centers: list[np.ndarray] = []
        for sums in coordinate_sums:
            centers = np.full(maximum_label + 1, np.nan, dtype=np.float64)
            np.divide(sums, counts, out=centers, where=counts > 0)
            axis_centers.append(centers)
        return tuple(axis_centers), counts

    def validate_representation(
        self,
        labels: object,
        *,
        representation: ObjectLabelRepresentation,
        value_label: str,
    ) -> None:
        """Validate storage and variants against a declared representation."""
        if representation is not self.storage_representation(labels):
            raise TypeError(
                f"{value_label} requires {representation.value} payload, got "
                f"{type(labels).__name__}."
            )

    @abstractmethod
    def validate_plane_count(
        self,
        labels: object,
        *,
        plane_count: int,
        context: str,
    ) -> None:
        """Validate storage against an already-declared semantic plane count."""

    @abstractmethod
    def project_planes(
        self,
        labels: object,
        plane_indices: tuple[int, ...],
    ) -> ObjectLabelData:
        """Return selected semantic planes in requested order."""

    @abstractmethod
    def project_plane(
        self,
        labels: object,
        plane_index: int,
    ) -> ObjectLabelData:
        """Return one semantic plane."""

    @abstractmethod
    def matching_variant(
        self,
        payload: object,
        variant: object | None,
        labels: object,
    ) -> object | None:
        """Return a variant when compatible with replacement labels."""

    @abstractmethod
    def label_shape(self, labels: object) -> tuple[int, ...] | None:
        """Return a shape when this storage has dense shape semantics."""


class DenseArrayObjectLabelStorageStrategy(ObjectLabelStorageStrategy):
    """Nominal storage behavior for dense object-label arrays."""

    value_type = np.ndarray

    def storage_representation(self, labels: object) -> ObjectLabelRepresentation:
        del labels
        return ObjectLabelRepresentation.DENSE_LABELS

    def dense_data(
        self,
        labels: object,
        *,
        source_spatial_shape_yx: tuple[int, int] | None,
    ) -> np.ndarray:
        del source_spatial_shape_yx
        return cast(np.ndarray, labels)

    def sparse_ijv_rows(self, labels: object) -> SparseIJVLabelRows:
        return SparseIJVLabelRows.from_dense_stack(cast(np.ndarray, labels))

    @classmethod
    def prepare_coordinates(cls) -> None:
        """Prepare C/F/strided signatures with both input mutability policies."""
        plane = np.array([[0, 1], [1, 0]], dtype=np.int32)
        volume = np.stack((plane, plane))
        for labels in (volume, np.asfortranarray(volume), volume.copy()[..., ::-1]):
            for writeable in (True, False):
                labels.flags.writeable = writeable
                _dense_label_coordinate_moments_numba(labels, 1)
        for labels in (plane, np.asfortranarray(plane), plane.copy()[:, ::-1]):
            for writeable in (True, False):
                labels.flags.writeable = writeable
                dense_label_centers_2d_numba(labels, 1)

    def axis_centers(
        self, labels: object, *, domain: Sequence[int]
    ) -> tuple[tuple[np.ndarray, ...], np.ndarray]:
        array = np.asarray(labels)
        if (
            array.dtype != np.dtype(np.int32)
            or array.ndim not in (2, 3)
            or any(size > np.iinfo(np.int32).max for size in array.shape)
        ):
            return super().axis_centers(labels, domain=domain)
        coordinate_planes = array[None, ...] if array.ndim == 2 else array
        positive_parts = tuple(plane[plane > 0] for plane in coordinate_planes)
        coordinate_domain = DenseIntegerObjectLabelIdDomain.from_array(
            np.concatenate(positive_parts or (np.empty(0, dtype=np.int32),))
        )
        del positive_parts
        if coordinate_domain is None:
            return super().axis_centers(labels, domain=domain)
        coordinate_columns = tuple(range(3 - array.ndim, 3))
        sums, pixel_counts = _dense_label_coordinate_moments_numba(
            coordinate_planes, coordinate_domain.max_label,
        )
        del coordinate_domain
        # Like sparse conversion, the moments snapshot precedes domain callbacks.
        object_ids = np.flatnonzero(pixel_counts)
        max_domain_label = max(domain, default=0)
        maximum_label = max(int(object_ids.max(initial=0)), max_domain_label)
        counts = np.bincount(object_ids, minlength=maximum_label + 1)
        counts[object_ids] = pixel_counts[object_ids]
        return self.coordinate_centers(
            counts,
            (
                np.bincount(
                    object_ids,
                    weights=sums[object_ids, coordinate_column],
                    minlength=maximum_label + 1,
                )
                for coordinate_column in coordinate_columns
            ),
            maximum_label=maximum_label,
        )

    def stack_planes(
        self,
        labels: Sequence[object],
        memory_type: str,
    ) -> ObjectLabelData:
        from openhcs.core.memory import stack_runtime_slices

        return stack_runtime_slices(
            tuple(cast(np.ndarray, value) for value in labels),
            memory_type,
            0,
        )

    def validate_plane_count(
        self,
        labels: object,
        *,
        plane_count: int,
        context: str,
    ) -> None:
        array = cast(np.ndarray, labels)
        if array.ndim < 3 or int(array.shape[0]) != plane_count:
            raise ValueError(
                f"{context} declares {plane_count} plane(s), but dense label "
                f"storage has shape {array.shape!r}."
            )

    def project_planes(
        self,
        labels: object,
        plane_indices: tuple[int, ...],
    ) -> ObjectLabelData:
        return cast(np.ndarray, labels)[np.asarray(plane_indices, dtype=np.intp)]

    def project_plane(
        self,
        labels: object,
        plane_index: int,
    ) -> ObjectLabelData:
        return cast(np.ndarray, labels)[plane_index]

    def matching_variant(
        self,
        payload: object,
        variant: object | None,
        labels: object,
    ) -> object | None:
        del payload
        if variant is None:
            return None
        replacement_shape = ObjectLabelStorageStrategy.for_value(labels).label_shape(
            labels
        )
        if replacement_shape is None or self.label_shape(variant) == replacement_shape:
            return variant
        return None

    def label_shape(self, labels: object) -> tuple[int, ...]:
        return tuple(cast(np.ndarray, labels).shape)


class SparseIJVObjectLabelStorageStrategy(ObjectLabelStorageStrategy):
    """Nominal storage behavior for sparse-IJV label rows."""

    value_type = SparseIJVLabelRows

    def storage_representation(self, labels: object) -> ObjectLabelRepresentation:
        del labels
        return ObjectLabelRepresentation.SPARSE_IJV

    def dense_data(
        self,
        labels: object,
        *,
        source_spatial_shape_yx: tuple[int, int] | None,
    ) -> np.ndarray:
        return cast(SparseIJVLabelRows, labels).to_dense(
            source_spatial_shape_yx=source_spatial_shape_yx,
        )

    def rendering_layers(
        self, labels: object, *, source_spatial_shape_yx: tuple[int, int] | None,
    ) -> tuple[np.ndarray, ...]:
        return cast(SparseIJVLabelRows, labels).nonoverlapping_dense_layers(
            source_spatial_shape_yx=source_spatial_shape_yx,
        )

    def sparse_ijv_rows(self, labels: object) -> SparseIJVLabelRows:
        return cast(SparseIJVLabelRows, labels)

    def stack_planes(
        self,
        labels: Sequence[object],
        memory_type: str,
    ) -> ObjectLabelData:
        del memory_type
        return SparseIJVLabelRows.from_slices(
            tuple(cast(SparseIJVLabelRows, value) for value in labels)
        )

    def validate_plane_count(
        self,
        labels: object,
        *,
        plane_count: int,
        context: str,
    ) -> None:
        sparse_labels = cast(SparseIJVLabelRows, labels)
        observed_count = (
            sparse_labels.label_data_runtime_slice_count()
            if sparse_labels.has_slice_index
            else 1
        )
        if observed_count != plane_count:
            raise ValueError(
                f"{context} declares {plane_count} plane(s), but sparse label "
                f"storage carries {observed_count}."
            )

    def project_planes(
        self,
        labels: object,
        plane_indices: tuple[int, ...],
    ) -> ObjectLabelData:
        sparse_labels = cast(SparseIJVLabelRows, labels)
        if not sparse_labels.has_slice_index:
            if plane_indices != (0,):
                raise IndexError(plane_indices)
            return sparse_labels
        return SparseIJVLabelRows.from_slices(
            tuple(sparse_labels.slice(plane_index) for plane_index in plane_indices)
        )

    def project_plane(
        self,
        labels: object,
        plane_index: int,
    ) -> ObjectLabelData:
        sparse_labels = cast(SparseIJVLabelRows, labels)
        if not sparse_labels.has_slice_index:
            if plane_index != 0:
                raise IndexError(plane_index)
            return sparse_labels
        return sparse_labels.slice(plane_index)

    def matching_variant(
        self,
        payload: object,
        variant: object | None,
        labels: object,
    ) -> object | None:
        del payload
        if variant is None:
            return None
        replacement_authority = ObjectLabelStorageStrategy.for_value(labels)
        if (
            replacement_authority.storage_representation(labels)
            is ObjectLabelRepresentation.SPARSE_IJV
        ):
            return variant
        return None

    def label_shape(self, labels: object) -> None:
        del labels
        return None


class ObjectLabelValueStorageStrategy(ObjectLabelStorageStrategy):
    """ObjectLabelValue delegates storage behavior to its label-data authority."""

    value_type = ObjectLabelValue

    @staticmethod
    def label_data(labels: object) -> ObjectLabelData:
        label_value = cast(ObjectLabelValue, labels)
        if isinstance(label_value.labels, ObjectLabelValue):
            raise TypeError(
                f"{type(label_value).__name__}.labels requires label data, not "
                "another ObjectLabelValue. Pass its variant_data explicitly instead."
            )
        return label_value.labels

    def storage_representation(self, labels: object) -> ObjectLabelRepresentation:
        label_data = self.label_data(labels)
        return ObjectLabelStorageStrategy.for_value(label_data).storage_representation(
            label_data
        )

    def dense_data(
        self,
        labels: object,
        *,
        source_spatial_shape_yx: tuple[int, int] | None,
    ) -> np.ndarray:
        del source_spatial_shape_yx
        label_value = cast(ObjectLabelValue, labels)
        label_data = self.label_data(label_value)
        return ObjectLabelStorageStrategy.for_value(label_data).dense_data(
            label_data,
            source_spatial_shape_yx=label_value.source_spatial_domain.source_shape_yx,
        )

    def rendering_layers(
        self, labels: object, *, source_spatial_shape_yx: tuple[int, int] | None,
    ) -> tuple[np.ndarray, ...]:
        del source_spatial_shape_yx
        value = cast(ObjectLabelValue, labels)
        data = self.label_data(value)
        return ObjectLabelStorageStrategy.for_value(data).rendering_layers(
            data, source_spatial_shape_yx=value.source_spatial_shape_yx,
        )

    def sparse_ijv_rows(self, labels: object) -> SparseIJVLabelRows:
        label_data = self.label_data(labels)
        return ObjectLabelStorageStrategy.for_value(label_data).sparse_ijv_rows(
            label_data
        )

    def axis_centers(
        self, labels: object, *, domain: Sequence[int]
    ) -> tuple[tuple[np.ndarray, ...], np.ndarray]:
        label_data = self.label_data(labels)
        return ObjectLabelStorageStrategy.for_value(label_data).axis_centers(
            label_data, domain=domain
        )

    def stack_planes(
        self,
        labels: Sequence[object],
        memory_type: str,
    ) -> ObjectLabelData:
        label_data = tuple(self.label_data(value) for value in labels)
        if not label_data:
            raise ValueError("Object-label plane stacking requires values.")
        return ObjectLabelStorageStrategy.for_value(label_data[0]).stack_planes(
            label_data,
            memory_type,
        )

    def validate_representation(
        self,
        labels: object,
        *,
        representation: ObjectLabelRepresentation,
        value_label: str,
    ) -> None:
        label_value = cast(ObjectLabelValue, labels)
        label_value.variant_data.validate_representation(
            representation=representation,
            value_label=value_label,
        )

    def validate_plane_count(
        self,
        labels: object,
        *,
        plane_count: int,
        context: str,
    ) -> None:
        label_data = self.label_data(labels)
        ObjectLabelStorageStrategy.for_value(label_data).validate_plane_count(
            label_data,
            plane_count=plane_count,
            context=context,
        )

    def project_planes(
        self,
        labels: object,
        plane_indices: tuple[int, ...],
    ) -> ObjectLabelData:
        label_data = self.label_data(labels)
        return ObjectLabelStorageStrategy.for_value(label_data).project_planes(
            label_data,
            plane_indices,
        )

    def project_plane(
        self,
        labels: object,
        plane_index: int,
    ) -> ObjectLabelData:
        label_data = self.label_data(labels)
        return ObjectLabelStorageStrategy.for_value(label_data).project_plane(
            label_data,
            plane_index,
        )

    def matching_variant(
        self,
        payload: object,
        variant: object | None,
        labels: object,
    ) -> object | None:
        del payload
        if variant is None:
            return None
        return ObjectLabelStorageStrategy.for_value(variant).matching_variant(
            variant,
            variant,
            labels,
        )

    def label_shape(self, labels: object) -> tuple[int, ...] | None:
        return cast(ObjectLabelValue, labels).variant_data.shape


def object_label_dense_array(
    payload: object,
    *,
    dtype: object | None = None,
    copy: bool | None = None,
) -> np.ndarray:
    """Materialize object-label dense data through its nominal storage authority."""
    dense_data = ObjectLabelStorageStrategy.for_value(payload).dense_data(
        payload,
        source_spatial_shape_yx=None,
    )
    if copy is None:
        return np.asarray(dense_data, dtype=dtype)
    return np.array(dense_data, dtype=dtype, copy=copy)


def object_label_sparse_ijv_rows(payload: object) -> SparseIJVLabelRows:
    """Materialize sparse-IJV rows through the nominal storage authority."""
    return ObjectLabelStorageStrategy.for_value(payload).sparse_ijv_rows(payload)


def object_label_stack_planes(
    labels: Sequence[ObjectLabelData],
    memory_type: str,
) -> ObjectLabelData:
    """Stack homogeneous label planes through their nominal storage authority."""
    values = tuple(labels)
    authority = ObjectLabelStorageStrategy.for_planes(values)
    return authority.stack_planes(values, memory_type)


def object_label_axis_centers(
    payload: object,
    *,
    domain: Sequence[int],
) -> tuple[tuple[np.ndarray, ...], np.ndarray]:
    """Reduce object coordinates through the nominal storage authority."""
    return ObjectLabelStorageStrategy.for_value(payload).axis_centers(
        payload,
        domain=domain,
    )


@njit(cache=True)
def _dense_label_coordinate_moments_numba(
    labels: np.ndarray,
    maximum_label: int,
) -> tuple[np.ndarray, np.ndarray]:
    """Reduce dense positive labels once in their declared row-major geometry."""
    sums = np.zeros((maximum_label + 1, 3), dtype=np.float64)
    counts = np.zeros(maximum_label + 1, dtype=np.int64)
    plane_count, height, width = labels.shape
    for plane in range(plane_count):
        for y in range(height):
            for x in range(width):
                label_id = int(labels[plane, y, x])
                if label_id > 0 and label_id <= maximum_label:
                    sums[label_id, 0] += plane
                    sums[label_id, 1] += y
                    sums[label_id, 2] += x
                    counts[label_id] += 1
    return sums, counts


@njit(cache=True)
def dense_label_centers_2d_numba(
    labels: np.ndarray, label_count: int
) -> np.ndarray:
    """Validate compiled two-dimensional geometry and return its y/x centers."""
    height, width = labels.shape
    sums, counts = _dense_label_coordinate_moments_numba(
        labels[None, :height, :width], label_count
    )
    centers = np.empty((label_count + 1, 2), dtype=np.float64)
    for label_id in range(label_count + 1):
        for axis in range(2):
            centers[label_id, axis] = (
                np.nan if counts[label_id] == 0
                else sums[label_id, axis + 1] / counts[label_id]
            )
    return centers


def object_label_storage_is_sparse_ijv(payload: object) -> bool:
    """Return whether the nominal storage authority owns sparse-IJV rows."""
    authority = ObjectLabelStorageStrategy.for_value(payload)
    return (
        authority.storage_representation(payload)
        is ObjectLabelRepresentation.SPARSE_IJV
    )


def object_label_validate_plane_count(
    labels: ObjectLabelData,
    *,
    plane_count: int,
    context: str,
) -> None:
    """Validate label storage against a declared semantic plane count."""
    ObjectLabelStorageStrategy.for_value(labels).validate_plane_count(
        labels,
        plane_count=plane_count,
        context=context,
    )


def object_label_project_planes(
    labels: ObjectLabelData,
    plane_indices: tuple[int, ...],
    *,
    plane_count: int,
) -> ObjectLabelData:
    """Return an ordered plane subset through the storage authority."""
    authority = ObjectLabelStorageStrategy.for_value(labels)
    authority.validate_plane_count(
        labels,
        plane_count=plane_count,
        context="Object-label data plane projection",
    )
    return authority.project_planes(labels, plane_indices)


def object_label_project_plane(
    labels: ObjectLabelData,
    plane_index: int,
    *,
    plane_count: int,
) -> ObjectLabelData:
    """Return one exact plane through the storage authority."""
    authority = ObjectLabelStorageStrategy.for_value(labels)
    authority.validate_plane_count(
        labels,
        plane_count=plane_count,
        context="Object-label data plane projection",
    )
    return authority.project_plane(labels, plane_index)


def object_label_value_with_dense_labels(
    source: ObjectLabelValueBuildSource,
    labels: ObjectLabelData,
    *,
    domain_declaration: ObjectLabelDomainDeclaration = (
        PreserveSourceObjectLabelDomainDeclaration()
    ),
    representation: ObjectLabelRepresentation | None = None,
    source_spatial_domain: SourceSpatialDomain | None = None,
) -> ObjectLabelValue:
    """Build transformed object labels preserving the source value category."""
    declared_domain = domain_declaration.declared_domain(source, labels)
    if isinstance(source, ObjectLabelValue):
        return source.with_replacement_labels(
            labels,
            representation=representation,
            domain=declared_domain,
            source_spatial_domain=source_spatial_domain,
        )
    if not isinstance(
        source, ObjectLabelDomainMetadata
    ) and not ObjectLabelsArtifactType.payload_shape.accepts(source):
        raise TypeError(
            "Object-label replacement requires nominal object-label domain "
            "metadata or declared label data, got "
            f"{type(source).__name__}."
        )
    return ObjectLabelPayload(
        variant_data=ObjectLabelVariantData(labels=labels),
        domain=declared_domain,
        representation=(
            ObjectLabelRepresentation.DENSE_LABELS
            if representation is None
            else representation
        ),
    )


class ObjectLabelSetReplacementStrategy(
    EnumKeyedStrategyMixin[ObjectLabelRepresentation],
    ABC,
    metaclass=AutoRegisterMeta,
):
    """Registered replacement policy for ObjectLabelSet label representations."""

    representation: ClassVar[ObjectLabelRepresentation | None] = None
    representation_label: ClassVar[str | None] = None
    __registry_key__ = "representation_label"
    __skip_if_no_key__ = True
    __enum_member_attr__ = "representation"

    @abstractmethod
    def replacement_labels(self, labels: object) -> object:
        """Return labels compatible with this representation."""


class DenseObjectLabelSetReplacementStrategy(ObjectLabelSetReplacementStrategy):
    """Dense replacements convert through the nominal storage authority."""

    representation = ObjectLabelRepresentation.DENSE_LABELS

    def replacement_labels(self, labels: object) -> np.ndarray:
        return object_label_dense_array(labels)


class SparseIJVObjectLabelSetReplacementStrategy(ObjectLabelSetReplacementStrategy):
    """Sparse-IJV replacements use the sparse rows carried by nominal label sets."""

    representation = ObjectLabelRepresentation.SPARSE_IJV

    def replacement_labels(self, labels: object) -> object:
        return object_label_sparse_ijv_rows(labels)


def object_label_domain_for_projected_label_plane(
    source: ObjectLabelValue,
    plane_index: int,
) -> ObjectLabelDomain:
    """Return the payload-domain object IDs carried by one selected plane."""
    domain = source.object_label_domain()
    if domain.scope is ObjectLabelDomainScope.PAYLOAD:
        return domain
    plane_domain = domain.project_planes((plane_index,))
    return ObjectLabelDomain.declared(
        scope=ObjectLabelDomainScope.PAYLOAD,
        declared_object_count=plane_domain.declared_object_count,
        declared_object_ids=plane_domain.declared_object_ids,
    )


def object_label_variant_matching_labels(
    variant: object | None,
    labels: object,
) -> object | None:
    """Return a variant only when it is compatible with replacement labels."""
    if variant is None:
        return None
    return ObjectLabelStorageStrategy.for_value(variant).matching_variant(
        variant,
        variant,
        labels,
    )
