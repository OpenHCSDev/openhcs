"""Image results that explicitly project their invocation's source identity."""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass, replace

from openhcs.core.axes import AxisFamily
from openhcs.core.runtime_array_values import (
    DataBackedRuntimeArrayPayload,
    RuntimeArrayData,
)
from openhcs.core.runtime_image_values import ImagePayload
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxisValueProjection,
    RuntimeSliceInvariantValue,
)


class SourceProjectedImageOutput(
    DataBackedRuntimeArrayPayload, RuntimeSliceInvariantValue, ABC,
):
    """A result whose declaration proves its source-context transformation."""

    @abstractmethod
    def resolve_source_context(
        self,
        source: RuntimeArrayData,
        projection: RuntimePlaneAxisValueProjection | None,
    ) -> RuntimeArrayData:
        """Validate and attach the source context declared by this result."""


class SourcePlaneSelectionImageOutput(SourceProjectedImageOutput):
    """A projection that retains an exact ordered subset of source planes."""

    @abstractmethod
    def selected_source_plane_indices(self) -> tuple[int, ...]:
        """Return the exact ordered source planes represented by this result."""

    def __post_init__(self) -> None:
        indices = self.selected_source_plane_indices()
        if not indices or len(set(indices)) != len(indices):
            raise ValueError("Selected source planes must be nonempty and distinct.")
        if any(type(index) is not int or index < 0 for index in indices):
            raise ValueError(
                "Selected source planes must be nonnegative integer indices."
            )
        plane_rank = AxisFamily.active().payload_spatial_rank
        if len(self.data.shape) != plane_rank + 1 or self.data.shape[0] != len(indices):
            raise ValueError(
                "Selected image output must contain one plane per source index."
            )

    def resolve_source_context(
        self,
        source: ImagePayload,
        projection: RuntimePlaneAxisValueProjection | None,
    ) -> ImagePayload:
        """Attach selected provenance, consuming an explicitly singleton axis."""
        projection = RuntimePlaneAxisValueProjection.require_complete_projection(
            projection, value_name="Selecting source planes"
        )
        indices = self.selected_source_plane_indices()
        if any(index >= projection.axis_size for index in indices):
            raise ValueError("Selected source plane is outside the input stack.")
        source_metadata = source.metadata
        metadata = source_metadata.for_source_planes(indices)
        # A spatial crop owns new pixel geometry; source plane identity survives.
        metadata = metadata.without_spatial_domain().replace_fields(
            plane_axis=projection.axis,
            source_image_provenance_planes=source_metadata.source_image_provenance_planes.select(
                indices
            ),
        )
        if len(indices) == 1:
            return metadata.for_leading_source_plane(0).payload_with(self.data[0])
        return metadata.payload_with(self.data, None)


@dataclass(frozen=True)
class SelectedPlaneImageOutput(SourcePlaneSelectionImageOutput):
    """A cropped array retaining an explicit ordered subset of source planes."""

    data: RuntimeArrayData
    source_indices: tuple[int, ...]

    def with_data(self, data: RuntimeArrayData) -> "SelectedPlaneImageOutput":
        return replace(self, data=data)

    def selected_source_plane_indices(self) -> tuple[int, ...]:
        """Provide this declaration's exact source-selection proof."""
        return self.source_indices
