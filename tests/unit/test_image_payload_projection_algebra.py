"""Physical source-plane projection preserves composition and mutable isolation."""

from dataclasses import fields

import numpy as np
import pytest

from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    ImagePayloadSliceProjector,
    ImageUnitIntervalIntensityMetadata,
    image_payload_mask,
    image_payload_metadata,
)
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_image_provenance import (
    RuntimeSourceImageProvenancePlane,
    SourceImageIdentity,
    SourceImageProvenanceContributor,
    SourceImageProvenancePlanes,
)


def _metadata(axis, channel_axis):
    return ImagePayloadMetadata(
        source_path="/tmp/parent.tif",
        source_component_metadata={"well": "A01", "extension": ".tif"},
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/tmp/first.tif", "/tmp/second.tif"),
            component_metadata=({"site": "1"}, {"site": "2"}),
        ),
        intensity_scale=255.0,
        source_dtype="uint8",
        source_plane_intensity_scales=(255.0, 65535.0),
        source_plane_dtypes=("uint8", "uint16"),
        unit_interval_intensity=ImageUnitIntervalIntensityMetadata(
            scale=255, source_plane_scales=(255, 65535)
        ),
        source_image_names=("DNA", "RNA"),
        source_channel_axis=channel_axis,
        plane_axis=axis,
    )


@pytest.mark.parametrize("axis", tuple(RuntimePlaneAxis))
@pytest.mark.parametrize("channel_axis", (None, 1, 3, -1))
@pytest.mark.parametrize("plane", (0, 1))
def test_physical_projection_agrees_with_separate_semantic_operations(
    axis, channel_axis, plane
):
    metadata = _metadata(axis, channel_axis)
    sequential = metadata.for_source_plane(plane).without_leading_plane_axis()
    projected = metadata.for_leading_source_plane(plane)
    for member in fields(ImagePayloadMetadata):
        assert getattr(projected, member.name) == getattr(sequential, member.name)
    assert projected.source_path == ("/tmp/first.tif", "/tmp/second.tif")[plane]
    assert projected.source_component_metadata["well"] == "A01"
    assert projected.source_component_metadata["site"] == str(plane + 1)
    assert projected.unit_interval_intensity.scale == (255, 65535)[plane]
    assert projected.source_plane_intensity_scales == ()
    assert projected.source_plane_dtypes == ()
    assert projected.plane_axis is None
    projected.source_provenance.source_identity.path = "/tmp/changed.tif"
    assert metadata.source_path == "/tmp/parent.tif"
    assert metadata.source_image_provenance_planes.paths[plane] != "/tmp/changed.tif"


def test_physical_projection_constructs_only_the_final_metadata(monkeypatch):
    metadata = _metadata(RuntimePlaneAxis.RUNTIME_SLICE, None)
    calls = []
    original = ImagePayloadMetadata.__post_init__

    def observe(self, *values):
        calls.append(self)
        original(self, *values)

    monkeypatch.setattr(ImagePayloadMetadata, "__post_init__", observe)
    projected = metadata.for_leading_source_plane(1)
    assert calls == [projected]


def test_physical_projection_rejects_leading_channel_axis():
    metadata = _metadata(RuntimePlaneAxis.RUNTIME_SLICE, 0)
    with pytest.raises(ValueError, match="both plane and channel"):
        metadata.for_leading_source_plane(1)


def test_physical_projection_requires_declared_plane_axis():
    metadata = _metadata(None, None)
    with pytest.raises(ValueError, match="declared plane axis"):
        metadata.for_leading_source_plane(1)


@pytest.mark.parametrize("channel_axis", (False, True, "1", 1.5))
def test_physical_projection_preserves_invalid_mutated_channel_error(channel_axis):
    metadata = _metadata(RuntimePlaneAxis.RUNTIME_SLICE, None)
    metadata.source_channel_axis = channel_axis
    with pytest.raises(TypeError, match="must be int or None"):
        metadata.for_source_plane(1).without_leading_plane_axis()
    with pytest.raises(TypeError, match="must be int or None"):
        metadata.for_leading_source_plane(1)


def test_physical_projection_preserves_invalid_mutated_plane_error():
    metadata = _metadata(RuntimePlaneAxis.RUNTIME_SLICE, None)
    metadata.plane_axis = "invalid-axis"
    with pytest.raises(ValueError):
        metadata.for_source_plane(1).without_leading_plane_axis()
    with pytest.raises(ValueError):
        metadata.for_leading_source_plane(1)


def test_projection_preserves_selected_spacing_and_nested_contributors():
    contributor = SourceImageProvenanceContributor(
        SourceImageIdentity("/tmp/contributor.tif", {"site": "3"}),
        source_image_name="Original",
    )
    metadata = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.SOURCE_BINDING,
        source_image_provenance_planes=SourceImageProvenancePlanes(
            (
                RuntimeSourceImageProvenancePlane(
                    SourceImageIdentity(
                        "/tmp/selected.tif",
                        {"OpenHCSSourceVoxelSpacingZYX": "4,2,1"},
                    ),
                    contributors=(contributor,),
                    source_image_name="DNA",
                ),
            )
        ),
    )
    sequential = metadata.for_source_plane(0).without_leading_plane_axis()
    projected = metadata.for_leading_source_plane(0)
    for member in fields(ImagePayloadMetadata):
        assert getattr(projected, member.name) == getattr(sequential, member.name)
    assert projected.source_image_provenance_planes.planes == (contributor,)


def test_projection_observes_mask_and_metadata_mutation():
    metadata = _metadata(RuntimePlaneAxis.RUNTIME_SLICE, None)
    mask = np.ones((2, 3, 4), dtype=bool)
    projector = ImagePayloadSliceProjector(mask, metadata)
    data = np.zeros((3, 4))
    first = projector.payload_for_slice(data, 1)
    assert image_payload_metadata(first).intensity_scale == 65535.0
    metadata.source_plane_intensity_scales = (1.0, 2.0)
    mask[1, 0, 0] = False
    second = projector.payload_for_slice(data, 1)
    assert image_payload_metadata(second).intensity_scale == 2.0
    assert not image_payload_mask(second)[0, 0]
    mask.resize((2, 2, 6), refcheck=False)
    with pytest.raises(ValueError, match="cannot be projected"):
        projector.payload_for_slice(data, 1)
