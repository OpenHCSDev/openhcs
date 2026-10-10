"""Source-file metadata construction for runtime image payloads."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np

from openhcs.core.image_file_serialization import (
    ImageFileSourceMetadata,
    image_file_source_metadata,
)
from openhcs.core.axes import ColourAxis
from openhcs.core.payload_axes import PayloadAxes
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    ImagePayload,
)
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_image_provenance import (
    SourceImageIdentity,
    SourceImageProvenancePlanes,
    SourcePlaneIndexedMetadata,
)
from openhcs.core.source_bindings import NamedSourceBinding
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.vfs_protocol import FileManagerLike


@dataclass(frozen=True, slots=True)
class ImagePayloadSourceMetadataContext:
    """Source-file identity and I/O context for loaded image metadata."""

    source_identity: SourceImageIdentity
    read_backend: str | None = None
    filemanager: FileManagerLike | None = None
    source_address: str | None = None

    def __post_init__(self) -> None:
        if (self.read_backend is None) != (self.filemanager is None):
            raise ValueError(
                "Image source metadata requires read_backend and filemanager together."
            )

    @property
    def source_path(self) -> str:
        if self.source_identity.path is None:
            raise ValueError("ImagePayloadSourceMetadataContext requires source path.")
        return self.source_identity.path

    def payload(self, image: Any) -> ImagePayload:
        """Keep loader metadata, deriving source facts only for bare pixels."""
        image = ImagePayload.of(image)
        metadata = image.metadata
        if not metadata.has_values:
            metadata = self.metadata(image)
        return metadata.payload_with(image.data, image.mask)

    def metadata(
        self,
        image: Any,
        *,
        source_binding: NamedSourceBinding | None = None,
    ) -> ImagePayloadMetadata:
        """Return source-file metadata for pixels loaded through this I/O context."""
        image = ImagePayload.of(image)
        existing_metadata = image.metadata
        resolved_source_path = self.resolved_source_path()
        source_metadata = image_file_source_metadata(resolved_source_path)
        source_dtype = source_metadata.source_dtype
        source_voxel_spacing = SourceVoxelSpacing.from_source_metadata(
            self.source_identity.component_metadata
        )
        image_data = image.data
        colour_axis_position = self.colour_axis_position(image, source_metadata)
        if source_binding is not None:
            colour_axis_position = source_binding.source_channel_axis_for_shape(
                tuple(int(value) for value in np.shape(image_data)),
                observed_axis=colour_axis_position,
            )
        colour_axes = PayloadAxes.colour_samples(colour_axis_position)
        source_spatial_shape_yx = ImagePayloadMetadata(
            axes=colour_axes
        ).spatial_shape_yx(image_data)
        spatial_origin_yx = (0, 0) if source_spatial_shape_yx is not None else None
        source_identity_path = self.source_path
        source_component_metadata = self.source_identity.component_metadata
        source_image_provenance_planes = SourceImageProvenancePlanes()
        plane_axis = None
        if source_component_metadata is not None:
            indexed_metadata = SourcePlaneIndexedMetadata.from_declared_source_metadata(
                source_component_metadata
            )
            if indexed_metadata is not None:
                plane_axis = RuntimePlaneAxis.RUNTIME_SLICE
                source_image_provenance_planes = (
                    SourceImageProvenancePlanes.from_components(
                        paths=(source_identity_path,)
                        * indexed_metadata.source_plane_count,
                        component_metadata=indexed_metadata.component_metadata(),
                    )
                )
        if source_dtype is None:
            array_metadata = ImagePayloadMetadata.for_array(
                image.data,
                source_path=source_identity_path,
            )
            metadata = array_metadata.replace_fields(
                source_component_metadata=source_component_metadata,
                source_image_provenance_planes=source_image_provenance_planes,
                source_spatial_domain=SourceSpatialDomain(
                    origin_yx=spatial_origin_yx,
                    source_shape_yx=source_spatial_shape_yx,
                ),
                source_voxel_spacing=source_voxel_spacing,
                axes=colour_axes,
                plane_axis=plane_axis,
            )
        else:
            metadata = ImagePayloadMetadata(
                intensity_scale=source_metadata.intensity_scale,
                source_dtype=str(source_dtype),
                source_path=source_identity_path,
                source_component_metadata=source_component_metadata,
                source_image_provenance_planes=source_image_provenance_planes,
                source_spatial_domain=SourceSpatialDomain(
                    origin_yx=spatial_origin_yx,
                    source_shape_yx=source_spatial_shape_yx,
                ),
                source_voxel_spacing=source_voxel_spacing,
                axes=colour_axes,
                plane_axis=plane_axis,
            )
        metadata = metadata.replace_fields(
            source_spatial_domain=existing_metadata.source_spatial_domain.with_native_image_context(
                metadata.source_spatial_domain,
                image_shape_yx=source_spatial_shape_yx,
            )
        )
        metadata = metadata.with_source_context_from(
            existing_metadata
        ).with_missing_intensity_from(existing_metadata)
        if source_binding is not None:
            # A declared absent colour axis must not be refilled from the
            # previous payload while merging missing source context.
            metadata.axes = colour_axes
        return metadata

    @staticmethod
    def colour_axis_position(
        image: ImagePayload,
        source_metadata: ImageFileSourceMetadata,
    ) -> int | None:
        """Return the colour axis the pixels declare, else the file's own."""
        position = image.metadata.axis_position(ColourAxis)
        if position is not None:
            image.metadata.axis_index(ColourAxis, image)
            return position
        return source_metadata.pixel_semantics.validated_channel_axis(image)

    def resolved_source_path(self) -> Path | None:
        """Resolve this source through the declared I/O backend, when present."""
        address = self.source_address or self.source_path
        if self.read_backend is not None and self.filemanager is not None:
            source_path = self.filemanager.physical_source_path(
                address,
                self.read_backend,
                base_path=Path(address).parent,
            )
            return None if source_path is None else Path(source_path)
        path = Path(address)
        return path if path.exists() else None
