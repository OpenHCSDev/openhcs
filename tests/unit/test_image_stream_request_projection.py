"""Request-owned display projection uses declarations, never array-rank guesses."""

from types import SimpleNamespace
from dataclasses import replace

import numpy as np
import pytest
from polystore.virtual_workspace import SourcePixelRef

from openhcs.core.config import NapariStreamingConfig
from openhcs.core.runtime_image_values import (
    image_payload_data,
    image_payload_mask,
    image_payload_metadata,
    ImagePayloadMetadata,
)
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_projection import OpenHCSPlaneAddress, SourcePlaneProjection
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.source_workspace_projection import VirtualWorkspaceSourceProjection
from openhcs.core.steps.stream_component_semantics import (
    StreamImagePayloadMetadataProjector,
)
from openhcs.core.viewer_streaming_service import (
    FullWindowImageStreamingRequest,
    ImageStreamingRequest,
    ViewerStreamingSource,
)


def image_with_declaration(axis, count=1, *, color=False, masked=False):
    shape = (count, 5, 6, 3) if color else (count, 5, 6)
    data = np.arange(np.prod(shape), dtype=np.uint16).reshape(shape)
    planes = SourceImageProvenancePlanes.from_components(
        paths=tuple(f"/input/channel-{index + 2}.tif" for index in range(count)),
        component_metadata=tuple(
            {
                "well": "A01",
                "site": 1,
                "channel": index + 2,
                "z_index": 1,
                "timepoint": 1,
            }
            for index in range(count)
        ),
    )
    metadata = ImagePayloadMetadata(
        plane_axis=axis,
        source_channel_axis=-1 if color else None,
        source_image_names=("FITC",) if count == 1 else ("FITC", "TRITC"),
        source_image_provenance_planes=planes,
        source_voxel_spacing=SourceVoxelSpacing((1.3556, 1.3556)),
        source_spatial_domain=SourceSpatialDomain((0, 0), (5, 6)),
    )
    mask = (data[..., 0] if color else data) % 2 == 0 if masked else None
    return metadata.payload_with(data, mask)


def request(request_type=ImageStreamingRequest):
    return request_type(
        viewer=SimpleNamespace(port=5992),
        config=NapariStreamingConfig(enabled=True),
        status_callback=lambda _message: None,
        error_callback=lambda _message: None,
        filenames=("image.tif",),
        read_backend="disk",
    )


@pytest.mark.parametrize("axis", tuple(RuntimePlaneAxis))
@pytest.mark.parametrize("color,masked", ((False, False), (False, True), (True, True)))
def test_declared_singleton_projection_retains_color_mask_and_source_context(
    axis, color, masked
):
    original = image_with_declaration(axis, color=color, masked=masked)
    projected = request().project_image(original)
    np.testing.assert_array_equal(
        image_payload_data(projected), image_payload_data(original)[0]
    )
    metadata = image_payload_metadata(projected)
    assert metadata.plane_axis is None
    assert metadata.source_channel_axis == (-1 if color else None)
    assert metadata.source_component_metadata["channel"] == 2
    assert metadata.source_image_names == ("FITC",)
    assert metadata.source_voxel_spacing == SourceVoxelSpacing((1.3556, 1.3556))
    assert (
        metadata.source_spatial_domain
        == image_payload_metadata(original).source_spatial_domain
    )
    if masked:
        np.testing.assert_array_equal(
            image_payload_mask(projected), image_payload_mask(original)[0]
        )


@pytest.mark.parametrize("axis", tuple(RuntimePlaneAxis))
def test_multi_plane_stack_is_not_collapsed(axis):
    original = image_with_declaration(axis, count=2)
    assert request().project_image(original) is original
    fields = StreamImagePayloadMetadataProjector.item_fields(
        image_payload_metadata(original), ("channel",)
    )
    assert fields["plane_component_values"] == {"channel": ("2", "3")}


@pytest.mark.parametrize("shape", ((5, 6), (1, 5, 6), (2, 5, 6)))
def test_unbound_arrays_are_never_reinterpreted_as_source_planes(shape):
    original = ImagePayloadMetadata(
        source_voxel_spacing=SourceVoxelSpacing((1.3556, 1.3556))
    ).payload_with(np.zeros(shape))
    assert request().project_image(original) is original


@pytest.mark.parametrize("axis", tuple(RuntimePlaneAxis))
def test_singleton_declaration_rejects_mismatched_native_shape(axis):
    original = image_with_declaration(axis)
    metadata = image_payload_metadata(original)
    conflicting = metadata.payload_with(np.zeros((2, 5, 6)))
    with pytest.raises(ValueError, match="axis of size 1"):
        request().project_image(conflicting)


def test_declared_axis_without_runtime_provenance_is_not_fabricated():
    original = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.SOURCE_BINDING
    ).payload_with(np.zeros((1, 5, 6)))
    assert request().project_image(original) is original


def test_independent_capabilities_cooperate_with_full_native_window_admission(tmp_path):
    events = []

    class PhysicalCalibration:
        def require_image_window(self, source, filename, image, projection):
            super().require_image_window(source, filename, image, projection)
            spacing = image_payload_metadata(image).source_voxel_spacing
            events.append(
                ("physical", SourceVoxelSpacing.require_physical_pixel_size((spacing,)))
            )

    class ObservedProjection:
        def image_plane_projection(self, image):
            projection = super().image_plane_projection(image)
            events.append(("projection", projection.require_plane_index()))
            return projection

    class CalibratedFullWindow(
        ObservedProjection, PhysicalCalibration, FullWindowImageStreamingRequest
    ):
        pass

    image = image_with_declaration(RuntimePlaneAxis.SOURCE_BINDING, masked=True)
    metadata = image_payload_metadata(image)
    filename = "image.tif"
    declaration = SourcePlaneProjection(
        address=OpenHCSPlaneAddress.from_values("A01", 1, 2, 1, 1),
        ref=SourcePixelRef("disk", filename),
        image_metadata=metadata,
    )
    projection = VirtualWorkspaceSourceProjection(
        source_refs_by_virtual_path={filename: declaration.ref},
        source_metadata_by_path={},
        source_projections_by_virtual_path={filename: declaration},
        workspace_root=str(tmp_path),
    )
    source = ViewerStreamingSource(
        filemanager=object(), microscope_handler=object(), plate_path=tmp_path
    )
    instance = request(CalibratedFullWindow)
    instance.require_image_window(source, filename, image, projection)
    projected = instance.project_image(image)
    assert events == [("physical", 1.3556), ("projection", 0)]
    np.testing.assert_array_equal(
        image_payload_data(projected), image_payload_data(image)[0]
    )
    np.testing.assert_array_equal(
        image_payload_mask(projected), image_payload_mask(image)[0]
    )
    # The original full-window leaf still rejects a crop before any projection.
    cropped = metadata.replace_fields(
        source_spatial_domain=SourceSpatialDomain((1, 1), (10, 10))
    ).payload_with(image_payload_data(image))
    cropped_projection = replace(
        projection,
        source_projections_by_virtual_path={
            filename: replace(
                declaration, image_metadata=image_payload_metadata(cropped)
            )
        },
    )
    with pytest.raises(ValueError, match="explicit source binding"):
        instance.require_image_window(source, filename, cropped, cropped_projection)
    assert events == [("physical", 1.3556), ("projection", 0)]
