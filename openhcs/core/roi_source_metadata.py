"""Persist the existing image-source declaration in native ROI metadata."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass, replace
from math import prod
from typing import ClassVar

from polystore.roi import ROI
from zmqruntime.viewer_protocol import ViewerWireValue

from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_slice_projection import RuntimeProjectionPlaneMetadata
from openhcs.core.source_image_provenance import SourceComponentMetadata
from openhcs.serialization.json import to_jsonable
from openhcs.core.axes import AxisFamily


@dataclass(frozen=True, slots=True)
class ROIPlaneMetadata:
    """The original ROI-local plane indices, independent of image pixel axes."""

    metadata: Mapping[str, object]

    @classmethod
    def from_shape_payload(cls, shape: Mapping[str, object]) -> ROIPlaneMetadata:
        metadata = shape.get("metadata")
        return cls(metadata if isinstance(metadata, Mapping) else {})

    def has_plane_metadata(self) -> bool:
        present = ("plane_indices" in self.metadata, "plane_shape" in self.metadata)
        if any(present) and not all(present):
            raise ValueError("ROI plane metadata requires both indices and shape.")
        return all(present)

    def indices(self) -> tuple[int, ...]:
        return self.projection().plane_indices

    def shape(self) -> tuple[int, ...]:
        return self.projection().plane_shape

    def projection(self) -> RuntimeProjectionPlaneMetadata:
        return RuntimeProjectionPlaneMetadata(
            plane_indices=self._tuple_field("plane_indices"),
            plane_shape=self._tuple_field("plane_shape"),
        )

    def _tuple_field(self, field: str) -> tuple[int, ...]:
        value = self.metadata.get(field)
        if not isinstance(value, Sequence) or isinstance(value, (str, bytes)):
            raise ValueError(f"ROI plane metadata field {field!r} must be a sequence.")
        return tuple(int(item) for item in value)

    @classmethod
    def common_shape(cls, metadata_items: Sequence[Mapping[str, object]]) -> tuple[int, ...]:
        planes = tuple(cls(metadata) for metadata in metadata_items)
        indexed = tuple(plane for plane in planes if plane.has_plane_metadata())
        if not indexed:
            return ()
        if len(indexed) != len(planes):
            raise ValueError("ROI payload mixes plane-indexed and unindexed shapes.")
        shapes = tuple(plane.shape() for plane in indexed)
        if any(shape != shapes[0] for shape in shapes[1:]):
            raise ValueError(f"ROI payload has inconsistent plane_shape metadata: {shapes!r}.")
        return shapes[0]

    @classmethod
    def source_component_domain(
        cls, rois: Sequence[ROI], metadata: ImagePayloadMetadata,
    ) -> tuple[SourceComponentMetadata, ...] | None:
        shape = cls.common_shape(tuple(roi.metadata for roi in rois))
        if not shape:
            return None
        domain = metadata.source_provenance.source_image_provenance_planes.component_metadata
        if len(domain) != prod(shape) or any(plane is None for plane in domain):
            raise ValueError("Plane-indexed ROI requires its complete source-plane domain.")
        values = cls.component_values(metadata)
        if tuple(len(value) for value in values.values()) != shape and not (
            shape == (1,) and not values
        ):
            raise ValueError("ROI plane shape conflicts with its represented component domain.")
        return tuple(domain)

    @staticmethod
    def component_values(metadata: ImagePayloadMetadata) -> dict[str, tuple[object, ...]]:

        return {
            component: tuple(dict.fromkeys(values))
            for component, values in metadata.source_provenance.varying_plane_component_values(
                AxisFamily.active().axes
            ).items()
        }


class ROIArchiveSourceMetadata:
    """Native ROI sidecar projection, not a second source-metadata schema."""

    FIELD: ClassVar[str] = "openhcs_image_payload_metadata"

    @classmethod
    def source_component_domain(
        cls, rois: Sequence[ROI], metadata: ImagePayloadMetadata,
    ) -> tuple[SourceComponentMetadata, ...] | None:
        from openhcs.core.roi_point_metadata import ROIFractionalZ

        point_domain = ROIFractionalZ.source_component_domain(rois, metadata)
        return (
            point_domain if point_domain is not None
            else ROIPlaneMetadata.source_component_domain(rois, metadata)
        )

    @classmethod
    def stream_item_fields(
        cls, rois: Sequence[ROI], metadata: ImagePayloadMetadata | None,
        image_fields: Mapping[str, ViewerWireValue],
    ) -> dict[str, ViewerWireValue]:
        from zmqruntime.viewer_protocol import ViewerWireField

        fields = dict(image_fields)
        if metadata is not None and ROIPlaneMetadata.source_component_domain(rois, metadata) is not None:
            values = ROIPlaneMetadata.component_values(metadata)
            if values:
                fields[ViewerWireField.PLANE_COMPONENT_VALUES.value] = values
        return fields

    @classmethod
    def bind(cls, rois: Sequence[ROI], metadata: ImagePayloadMetadata) -> list[ROI]:
        encoded = to_jsonable(metadata)
        return [
            replace(roi, metadata={**roi.metadata, cls.FIELD: encoded}) for roi in rois
        ]

    @classmethod
    def decode(cls, rois: Sequence[ROI]) -> ImagePayloadMetadata | None:
        """Decode once; external ROI archives may have no OpenHCS source binding."""
        encoded = [roi.metadata.get(cls.FIELD) for roi in rois]
        if not any(value is not None for value in encoded):
            return None
        if any(value is None or value != encoded[0] for value in encoded):
            raise ValueError(
                "ROI archive contains missing or conflicting source metadata."
            )
        return ImagePayloadMetadata.from_mapping(encoded[0])

    @classmethod
    def geometry(cls, rois: Sequence[ROI]) -> list[ROI]:
        """Keep transport-only source declarations out of the ROI feature table."""
        return [
            replace(roi, metadata=cls.feature_metadata(roi.metadata))
            for roi in rois
        ]

    @classmethod
    def feature_metadata(cls, metadata: Mapping[str, object]) -> dict[str, object]:
        """Project features without discarding the transported source record."""
        return {key: value for key, value in metadata.items() if key != cls.FIELD}
