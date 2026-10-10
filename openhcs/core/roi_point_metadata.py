"""Exact fractional Z retained beside ImageJ's integer-plane point ROI."""

from __future__ import annotations

from dataclasses import dataclass, replace
from math import isfinite
from typing import ClassVar, Mapping

from polystore.roi import ROI

from openhcs.core.axes import AxisFamily, StackAxis
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.source_image_provenance import SourceComponentMetadata
from openhcs.core.source_matching import source_component_metadata_items
from openhcs.core.source_metadata import SourceVoxelSpacing


@dataclass(frozen=True, slots=True)
class ROIFractionalZ:
    """The Z coordinate ImageJ's 2D point shape cannot represent."""

    value: float
    FIELD: ClassVar[str] = "openhcs_fractional_z"

    def __post_init__(self) -> None:
        if isinstance(self.value, bool) or not isfinite(self.value):
            raise ValueError("ROI fractional Z must be a finite real coordinate.")

    def bind(self, roi: ROI) -> ROI:
        return replace(roi, metadata={**roi.metadata, self.FIELD: float(self.value)})

    @classmethod
    def decode(cls, metadata: Mapping[str, object]) -> ROIFractionalZ | None:
        value = metadata.get(cls.FIELD)
        if value is None:
            return None
        if isinstance(value, bool) or not isinstance(value, (int, float)):
            raise ValueError("ROI fractional Z must be numeric.")
        return cls(float(value))

    @classmethod
    def source_component_domain(
        cls,
        rois: list[ROI],
        metadata: ImagePayloadMetadata,
    ) -> tuple[SourceComponentMetadata, ...] | None:
        """Derive the point route's ordered Z domain from source-plane provenance."""
        coordinates = tuple(cls.decode(roi.metadata) for roi in rois)
        if not any(coordinate is not None for coordinate in coordinates):
            return None
        if any(coordinate is None for coordinate in coordinates):
            raise ValueError("Point ROI archive mixes 3D and 2D point metadata.")
        planes = metadata.source_provenance.source_image_provenance_planes
        domain = planes.component_metadata
        if not domain or any(plane is None for plane in domain):
            raise ValueError("3D point ROI requires an exact source-plane Z domain.")
        stack_axis = AxisFamily.active().one(StackAxis)
        z_field = stack_axis.name
        if any(z_field not in plane for plane in domain):
            raise ValueError("3D point ROI source planes require z_index metadata.")
        z_values = tuple(plane[z_field] for plane in domain)
        if any(
            isinstance(value, bool) or not isinstance(value, (str, int))
            for value in z_values
        ):
            raise ValueError("3D point ROI source z_index values must be integers.")
        try:
            integer_z = tuple(int(value) for value in z_values)
        except ValueError as exc:
            raise ValueError(
                "3D point ROI source z_index values must be integers."
            ) from exc
        if any(
            str(value).strip() != str(index) and not str(value).strip().isdigit()
            for value, index in zip(z_values, integer_z, strict=True)
        ):
            raise ValueError("3D point ROI source z_index values must be integers.")
        if integer_z != tuple(range(integer_z[0], integer_z[0] + len(domain))):
            raise ValueError(
                "3D point ROI source Z planes must be consecutive and ordered."
            )
        if any(
            coordinate.value < 0 or coordinate.value > len(domain) - 1
            for coordinate in coordinates
        ):
            raise ValueError(
                "3D point ROI Z coordinate lies outside its source planes."
            )
        components = tuple(
            dict(source_component_metadata_items(plane)) for plane in domain
        )
        common_keys = set(components[0]) - {stack_axis}
        if any(
            set(plane) - {stack_axis} != common_keys
            for plane in components
        ):
            raise ValueError("3D point ROI source planes have inconsistent components.")
        if any(
            any(plane[key] != components[0][key] for key in common_keys)
            for plane in components
        ):
            raise ValueError("3D point ROI source planes vary outside Z.")
        spacing = SourceVoxelSpacing.from_source_metadata(domain[0])
        if any(
            SourceVoxelSpacing.from_source_metadata(plane) != spacing
            for plane in domain
        ):
            raise ValueError("3D point ROI source planes have inconsistent calibration.")
        return tuple(domain)
