"""Construction of object-label values from source-image context."""

from __future__ import annotations

from dataclasses import dataclass, field
from types import MappingProxyType

import numpy as np

from openhcs.core import runtime_image_values
from openhcs.core.runtime_object_label_domains import (
    ObjectLabelDomain,
    ObjectLabelDomainScope,
    PresentObjectLabelIdsDomainDeclaration,
)
from openhcs.core.runtime_object_labels import (
    ObjectLabelPayload,
    ObjectLabelRepresentation,
    ObjectLabelSet,
    ObjectLabelVariantData,
    ObjectLabelVariants,
)
from openhcs.core.runtime_plane_projection import RuntimePlaneAxisValueProjection
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.runtime_array_values import array_geometry


@dataclass(frozen=True, slots=True)
class SourceImageObjectLabelBuildRequest:
    """Build object-label runtime values from one source-image context."""

    image: runtime_image_values.ImagePayload
    labels: object
    domain_scope: ObjectLabelDomainScope | None = None
    plane_projection: RuntimePlaneAxisValueProjection | None = None
    declared_object_count: int | None = None
    declared_object_ids: tuple[int, ...] = ()
    variants: ObjectLabelVariants = field(default_factory=lambda: MappingProxyType({}))
    parent_image_source_voxel_spacing: SourceVoxelSpacing | None = None

    def __post_init__(self) -> None:
        # Builders receive the source image as a payload or as bare pixels.
        object.__setattr__(
            self, "image", runtime_image_values.ImagePayload.of(self.image)
        )

    @property
    def metadata(self) -> runtime_image_values.ImagePayloadMetadata:
        return self.image.metadata

    def payload(
        self,
        *,
        representation: ObjectLabelRepresentation = ObjectLabelRepresentation.DENSE_LABELS,
    ) -> ObjectLabelPayload:
        metadata = self.metadata
        source_spatial_domain = metadata.object_label_source_spatial_domain()
        source_shape_yx = metadata.spatial_shape_yx(self.image)
        if source_shape_yx is not None:
            source_spatial_domain = source_spatial_domain.with_missing_from(
                SourceSpatialDomain(
                    origin_yx=(0, 0),
                    source_shape_yx=source_shape_yx,
                )
            )
        semantics = self.plane_semantics()
        if semantics is None:
            if self.declared_object_count is not None or self.declared_object_ids:
                label_domain = ObjectLabelDomain.declared(
                    declared_object_count=self.declared_object_count,
                    declared_object_ids=self.declared_object_ids,
                )
            else:
                label_domain = PresentObjectLabelIdsDomainDeclaration().declared_domain(
                    self.image,
                    self.labels,
                )
            plane_axis = None
        else:
            if self.declared_object_count is not None or self.declared_object_ids:
                raise ValueError(
                    "Plane-scoped source-image object labels require per-plane "
                    "domains; payload-wide object counts or IDs are invalid."
                )
            label_domain = PresentObjectLabelIdsDomainDeclaration(
                scope=ObjectLabelDomainScope.PLANE,
                plane_projection=semantics,
            ).declared_domain(self.image, self.labels)
            plane_axis = semantics.axis
        return ObjectLabelPayload(
            variant_data=ObjectLabelVariantData(
                labels=self.labels,
                variants=self.variants,
            ).in_representation(representation),
            representation=representation,
            domain=label_domain,
            source_provenance=metadata.source_provenance,
            source_spatial_domain=source_spatial_domain,
            parent_image_source_voxel_spacing=(
                metadata.source_voxel_spacing
                if self.parent_image_source_voxel_spacing is None
                else self.parent_image_source_voxel_spacing
            ),
            plane_axis=plane_axis,
        )

    def label_set(
        self,
        *,
        name: str,
        source_image_name: str | None = None,
        representation: ObjectLabelRepresentation = ObjectLabelRepresentation.DENSE_LABELS,
    ) -> ObjectLabelSet:
        return ObjectLabelSet.from_payload(
            name,
            self.payload(representation=representation),
            source_image_name=source_image_name,
        )

    def plane_semantics(self) -> RuntimePlaneAxisValueProjection | None:
        """Validate the object-domain projection declared by this producer.

        Source-image storage axes retain acquisition provenance; they do not
        declare whether object IDs identify a whole volume or separate planes.
        Saved label-image admission supplies its projection at the ingress owner.
        """
        if self.domain_scope is ObjectLabelDomainScope.PAYLOAD:
            if self.plane_projection is not None:
                raise ValueError(
                    "Payload-scoped object-label output cannot declare a plane "
                    "projection."
                )
            return None
        if (
            self.domain_scope is not None
            and self.domain_scope is not ObjectLabelDomainScope.PLANE
        ):
            raise TypeError(
                "Source-image object-label domain_scope must be payload, plane, "
                f"or None; got {self.domain_scope!r}."
            )
        projection = self.plane_projection
        if projection is None:
            if self.domain_scope is ObjectLabelDomainScope.PLANE:
                raise ValueError(
                    "Plane-scoped object-label output requires an exact plane "
                    "projection."
                )
            return None
        metadata = self.metadata
        projection.validate_source_declaration(
            metadata.plane_axis, metadata.source_provenance,
        )
        label_array = np.asarray(self.labels)
        projection.validate_shape(
            label_array.shape,
            value_name="Source-image object labels",
        )
        projection.validate_shape(
            array_geometry(self.image).shape,
            value_name="Object-label source image",
        )
        source_shape_yx = metadata.spatial_shape_yx(self.image)
        if source_shape_yx is None:
            raise ValueError(
                "Declared source-image plane axis requires a source spatial domain."
            )
        if tuple(label_array.shape[-2:]) != tuple(source_shape_yx):
            raise ValueError(
                "Object-label spatial shape must match the declared source-image "
                f"domain: {tuple(label_array.shape[-2:])!r} != {tuple(source_shape_yx)!r}."
            )
        return projection
