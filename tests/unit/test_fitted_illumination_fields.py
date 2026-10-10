"""Real source-owner projection of one field fitted from all observations."""

import numpy as np
import pytest

from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_payload_metadata,
)
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisValueProjection,
)
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.processing.backends.enhance.flatfield import FittedIlluminationFieldOutput


def observation_source(components):
    count = len(components)
    metadata = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        intensity_scale=65535.0,
        source_dtype="uint16",
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=tuple(f"/synthetic/input/observation_{i}.tif" for i in range(count)),
            component_metadata=tuple(components),
        ),
    )
    return metadata.payload_with(np.zeros((count, 8, 9), dtype=np.uint16))


def cross_site_source():
    return observation_source(
        [
            {"well": "A01", "site": str(i), "channel": "1", "z_index": "1"}
            for i in range(3)
        ]
    )


def test_field_collapses_pixels_not_contributor_history():
    source = cross_site_source()
    field = FittedIlluminationFieldOutput(np.full((8, 9), 1.25, dtype=np.float32), 3)
    result = field.resolve_source_context(
        source,
        RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE,
            axis_size=3,
        ),
    )
    metadata = image_payload_metadata(result)
    assert result.shape == (8, 9)
    assert metadata.plane_axis is None
    assert len(metadata.source_image_paths) == 3
    assert metadata.source_image_provenance_planes.contributor_count == 3
    assert metadata.source_component_metadata == {
        "well": "A01",
        "channel": "1",
        "z_index": "1",
    }
    assert metadata.intensity_scale is None
    assert metadata.source_dtype is None
    np.testing.assert_array_equal(np.asarray(result), np.full((8, 9), 1.25))


@pytest.mark.parametrize("changing", ["z_index", "channel", "timepoint"])
def test_non_observation_axis_variation_is_rejected_before_fit(changing):
    components = [
        {"well": "A01", "site": str(i), "channel": "1", "z_index": "1"}
        for i in range(3)
    ]
    for index, component in enumerate(components):
        component[changing] = str(index)
    with pytest.raises(ValueError, match="every other source component fixed"):
        FittedIlluminationFieldOutput.validate_observation_domain(
            observation_source(components)
        )


def test_z_only_stack_is_not_an_observation_ensemble():
    source = observation_source(
        [
            {"well": "A01", "site": "1", "channel": "1", "z_index": str(i)}
            for i in range(3)
        ]
    )
    with pytest.raises(ValueError, match=r"independent TileAxis observations \(site\)"):

        FittedIlluminationFieldOutput.validate_observation_domain(source)


@pytest.mark.parametrize(
    "projection",
    [
        None,
        RuntimePlaneAxisValueProjection.from_selected_plane(
            axis=RuntimePlaneAxis.RUNTIME_SLICE,
            plane_index=0,
            axis_size=3,
        ),
    ],
)
def test_field_rejects_one_plane_as_aggregate_source(projection):
    field = FittedIlluminationFieldOutput(np.ones((8, 9), dtype=np.float32), 3)
    with pytest.raises(ValueError, match="complete input stack projection"):
        field.resolve_source_context(cross_site_source(), projection)


def test_field_keeps_observation_count_through_real_array_conversion():
    field = FittedIlluminationFieldOutput(np.ones((8, 9), dtype=np.float32), 3)
    converted = field.with_data(np.asarray(field, dtype=np.float64))
    assert converted.observation_count == 3
    assert converted.dtype == np.float64
    np.testing.assert_array_equal(np.asarray(converted), np.asarray(field))


def test_field_rejects_wrong_grid_or_observation_count():
    source = cross_site_source()
    projection = RuntimePlaneAxisValueProjection.preserve(
        axis=RuntimePlaneAxis.RUNTIME_SLICE,
        axis_size=3,
    )
    with pytest.raises(ValueError, match="spatial grid"):
        FittedIlluminationFieldOutput(np.zeros((4, 9)), 3).resolve_source_context(
            source, projection
        )
    with pytest.raises(ValueError, match="observation count"):
        FittedIlluminationFieldOutput(np.zeros((8, 9)), 4).resolve_source_context(
            source, projection
        )
