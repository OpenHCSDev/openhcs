"""Real ViewerModel and typed payload sampling; no GUI or runtime process."""

from dataclasses import replace

import numpy as np
import pytest

from test_viewer_feature_measurement import native_route

from openhcs.agent.dto.execution import ExecutionConnectionSpec
from openhcs.agent.dto.viewer import ViewerWindowImageSampleRequest
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.runtime.napari_viewer_server import NapariViewerPayloadProjection
from openhcs.runtime.viewer_controls import (
    ViewerImageSpatialSampleControls,
    ViewerPayloadControlOptions,
    ViewerPayloadProjectionOptions,
)
from openhcs.core.payload_axes import PayloadAxes


def _native_sample(*, rgb, y, x, height, width, limit=4096):
    server, layer, gray = native_route()
    server.napari_window_title = "Native spatial sample fixture"
    data = np.stack((gray, gray + 1000, gray + 2000), axis=-1) if rgb else gray
    metadata = ImagePayloadMetadata(axes=PayloadAxes.colour_samples(2 if rgb else None))
    if rgb:
        server.viewer.layers.remove(layer)
        layer = server.viewer.add_image(
            np.stack((data, data + 3000)),
            rgb=True,
            axis_labels=("channel", "y", "x"),
        )
        server.layer_route_state.set_layer("source", layer)
    items = server.component_groups.items_for("source")
    items[0] = replace(items[0], data=data, image_metadata=metadata)
    request = ViewerWindowImageSampleRequest.from_fields(
        connection=ExecutionConnectionSpec(port=5584),
        route_key="source",
        axis_indices={"channel": 0},
        y=y,
        x=x,
        height=height,
        width=width,
        include_array_values=True,
        max_array_elements=limit,
    )
    projection = NapariViewerPayloadProjection(
        server=server,
        viewer=server.viewer,
        request=request.payload_request().payload_projection,
    )
    reply = projection.to_wire_mapping()
    (record,) = reply["layers"][0]["payloads"]
    return record, data, request


@pytest.mark.parametrize("rgb", [False, True])
@pytest.mark.parametrize(
    "crop", [(16, 0, 16, 64), (3, 9, 5, 7), (60, 62, 12, 8), (70, 4, 3, 9)]
)
def test_semantic_yx_matches_exact_native_gray_and_rgb_values(rgb, crop):
    y, x, height, width = crop
    record, data, request = _native_sample(
        rgb=rgb, y=y, x=x, height=height, width=width
    )
    summary = record["array_value_summary"]
    expected = data[y : y + height, x : x + width]
    assert summary["included"]
    assert summary["shape"] == expected.shape
    assert summary["slice_ranges"][:2] == (
        (min(y, 64), min(y + height, 64)),
        (min(x, 64), min(x + width, 64)),
    )
    assert summary["requested_slice_ranges"] == request.array_slices
    # Empty nested tuples cannot encode shape; shape is separately asserted.
    if expected.size:
        np.testing.assert_array_equal(np.asarray(record["array_values"]), expected)
    if rgb:
        assert summary["shape"][-1] == 3
        assert summary["slice_ranges"][-1] == (0, 3)


def test_native_spatial_sample_keeps_original_element_omission_policy():
    record, _, _ = _native_sample(rgb=True, y=3, x=9, height=5, width=7, limit=100)
    summary = record["array_value_summary"]
    assert not summary["included"]
    assert summary["shape"] == (5, 7, 3) and summary["size"] == 105
    assert summary["omitted_reason"] == "max_array_elements_exceeded"
    assert summary["max_array_elements"] == 100
    assert record["array_values"] == ()


def test_raw_array_slices_keep_trailing_dimension_contract_in_same_native_projection():
    server, _, gray = native_route()
    server.napari_window_title = "Native raw array fixture"
    rgb = np.stack((gray, gray + 1000, gray + 2000), axis=-1)
    items = server.component_groups.items_for("source")
    items[0] = replace(
        items[0], data=rgb, image_metadata=ImagePayloadMetadata(axes=PayloadAxes.colour_samples(2))
    )
    projection = NapariViewerPayloadProjection(
        server=server,
        viewer=server.viewer,
        request=ViewerPayloadProjectionOptions(
            controls=ViewerPayloadControlOptions(
                route_key="source",
                axis_indices={"channel": 0},
                include_array_values=True,
                array_slices=((16, 32), (0, 64)),
            )
        ),
    )
    (record,) = projection.to_wire_mapping()["layers"][0]["payloads"]
    assert record["array_value_summary"]["shape"] == (64, 16, 3)
    np.testing.assert_array_equal(np.asarray(record["array_values"]), rgb[:, 16:32, :])


def _sample(controls, data, **context):
    projection = NapariViewerPayloadProjection(
        server=None,
        viewer=None,
        request=ViewerPayloadProjectionOptions(controls=controls),
    )
    return projection.array_value_sample(data, **context)


def test_layout_new_case_only_declares_original_metadata_hook():
    class MiddleColorMetadata(ImagePayloadMetadata):
        def spatial_axes_yx(self, data):
            return (0, 2)

    data = np.arange(8 * 3 * 10).reshape(8, 3, 10)
    controls = ViewerImageSpatialSampleControls(array_slices=((2, 5), (4, 9)))
    sample, summary = _sample(controls, data, image_metadata=MiddleColorMetadata())
    np.testing.assert_array_equal(sample, data[2:5, :, 4:9])
    assert summary["slice_ranges"] == ((2, 5), (0, 3), (4, 9))


def test_spatial_axes_project_through_original_leading_aggregate_selection():
    source = np.arange(2 * 8 * 10 * 3).reshape(2, 8, 10, 3)
    controls = ViewerImageSpatialSampleControls(array_slices=((2, 5), (4, 9)))
    sample, summary = _sample(
        controls,
        source[1],
        image_metadata=ImagePayloadMetadata(axes=PayloadAxes.colour_samples(3)),
        source_data=source,
        removed_leading_axes=1,
    )
    np.testing.assert_array_equal(sample, source[1, 2:5, 4:9, :])
    assert summary["slice_ranges"] == ((2, 5), (4, 9), (0, 3))


def test_undeclared_layout_fails_explicitly_without_raw_slice_guess():
    controls = ViewerImageSpatialSampleControls(array_slices=((0, 1), (0, 1)))
    with pytest.raises(ValueError, match="image metadata"):
        _sample(controls, np.ones((2, 2)))
    with pytest.raises(ValueError, match="does not declare"):
        _sample(controls, np.ones((3,)), image_metadata=ImagePayloadMetadata())


def test_slice_validation_is_cooperative_with_existing_control_ancestor():
    with pytest.raises(ValueError, match="nonnegative"):
        ViewerImageSpatialSampleControls(
            array_slices=((0, 1), (0, 1)), max_array_elements=-1
        )
    with pytest.raises(ValueError, match="exactly Y/X"):
        ViewerImageSpatialSampleControls(array_slices=((0, 1),))
