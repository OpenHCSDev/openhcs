"""Image results that explicitly project their invocation's source identity."""

from abc import ABC, abstractmethod
from dataclasses import dataclass, replace

from openhcs.core.runtime_array_values import (
    DataBackedRuntimeArrayPayload,
    RuntimeArrayData,
)
from openhcs.core.runtime_image_values import image_payload_metadata
from openhcs.core.runtime_plane_projection import RuntimePlaneAxisValueProjection


class SourceProjectedImageOutput(DataBackedRuntimeArrayPayload, ABC):
    """A result whose declaration proves its source-context transformation."""

    @abstractmethod
    def resolve_source_context(
        self,
        source: RuntimeArrayData,
        projection: RuntimePlaneAxisValueProjection | None,
    ) -> RuntimeArrayData:
        """Validate and attach the selected source context to this result."""


@dataclass(frozen=True)
class SelectedPlaneImageOutput(SourceProjectedImageOutput):
    """A cropped array retaining an explicit ordered subset of source planes."""

    data: RuntimeArrayData
    source_indices: tuple[int, ...]

    def __post_init__(self) -> None:
        if not self.source_indices or len(set(self.source_indices)) != len(
            self.source_indices
        ):
            raise ValueError("Selected source planes must be nonempty and distinct.")
        if any(type(index) is not int or index < 0 for index in self.source_indices):
            raise ValueError(
                "Selected source planes must be nonnegative integer indices."
            )
        if len(self.data.shape) != 3 or self.data.shape[0] != len(self.source_indices):
            raise ValueError(
                "Selected image output must contain one plane per source index."
            )

    def with_data(self, data: RuntimeArrayData) -> "SelectedPlaneImageOutput":
        return replace(self, data=data)

    def resolve_source_context(
        self,
        source: RuntimeArrayData,
        projection: RuntimePlaneAxisValueProjection | None,
    ) -> RuntimeArrayData:
        if projection is None or projection.plane_index is not None:
            raise ValueError(
                "Selecting source planes requires a complete input stack projection."
            )
        if any(index >= projection.axis_size for index in self.source_indices):
            raise ValueError("Selected source plane is outside the input stack.")
        source_metadata = image_payload_metadata(source)
        metadata = source_metadata.for_source_planes(self.source_indices)
        # A spatial crop owns new pixel geometry; source plane identity survives.
        metadata = metadata.without_spatial_domain().replace_fields(
            plane_axis=projection.axis,
            source_image_provenance_planes=source_metadata.source_image_provenance_planes.select(
                self.source_indices
            ),
        )
        return metadata.payload_with(self.data, None)
