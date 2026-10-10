"""448: preserve original channel carriers while presenting native spatial YX."""

import numpy as np
import pytest

from openhcs.core.config import NapariDisplayConfig
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.runtime.napari_streaming_handlers import (
    NapariImageLayerPresentationPolicy,
    NapariLayerRouteStateStore,
    NapariSourceChannelImageLayerPresentationPolicy,
)
from openhcs.runtime.napari_viewer_server import (
    NapariImageLayerDisplayHandler,
    NapariLayerDisplayPipeline,
    NapariLayerDisplayRequest,
)
from tests.unit.test_napari_streaming_handlers import (
    _axis_presentation,
    _FakeNapariServer,
    _FakeViewer,
    _layer_item,
)
from openhcs.core.payload_axes import PayloadAxes
from openhcs.core.axes import ColourAxis


def _display(channels, channel_axis, site_count):
    route = "independent-source-channel-carrier"
    server = _FakeNapariServer()
    server.layer_route_state = NapariLayerRouteStateStore.empty()
    server.layer_route_state.set_title(route, "Named source carrier")
    server.viewer = _FakeViewer()
    items = []
    for site in range(site_count):
        # Exact Engineering03 C2 values for singleton, independent lanes otherwise.
        yxc = (
            np.arange(64 * channels, dtype=np.float32).reshape(8, 8, channels)
            + np.float32(64 + site)
        ) / np.float32(65535)
        data = np.moveaxis(yxc, -1, channel_axis)
        metadata = ImagePayloadMetadata(
            axes=PayloadAxes.colour_samples(channel_axis),
            source_voxel_spacing=SourceVoxelSpacing((0.5, 0.5)),
            source_spatial_domain=SourceSpatialDomain(
                origin_yx=(0, 0), source_shape_yx=(8, 8)
            ),
            source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
                paths=(f"/synthetic/A01_s{site + 1:03}_w2.tif",),
                component_metadata=({"well": "A01", "channel": "2"},),
            ),
        )
        items.append(
            _layer_item({"site": site + 1}, data=data, image_metadata=metadata)
        )
    presentation = _axis_presentation(
        layer_key=route,
        projected_axis_components=("site",),
        component_values={"site": list(range(1, site_count + 1))},
    )
    originals = tuple(item.data.copy() for item in items)
    NapariImageLayerDisplayHandler().handle(
        NapariLayerDisplayRequest(
            pipeline=NapariLayerDisplayPipeline(server),
            presentation=presentation,
            items=items,
            display_config=NapariDisplayConfig(),
        )
    )
    return server, items, originals


@pytest.mark.parametrize("channels", (1, 2, 5, 7))
@pytest.mark.parametrize("channel_axis", (-1, 0, 2))
@pytest.mark.parametrize("site_count", (1, 2))
def test_non_rgb_carrier_reopens_with_native_yx(channels, channel_axis, site_count):
    server, items, originals = _display(channels, channel_axis, site_count)
    kind, native, name, kwargs = server.viewer.calls[-1]
    assert kind == "image" and name == "Named source carrier"
    assert native.shape == (site_count, channels, 8, 8)
    assert native.dtype == np.float32
    assert kwargs["rgb"] is False
    assert kwargs["axis_labels"] == ("site", "source_channel", "y", "x")
    assert kwargs["scale"] == (1.0, 1.0, 0.5, 0.5)
    assert kwargs["translate"] == (0.0, 0.0, 0.0, 0.0)
    assert kwargs["units"] == (
        "dimensionless",
        "dimensionless",
        "micrometer",
        "micrometer",
    )
    for index, (item, original) in enumerate(zip(items, originals, strict=True)):
        np.testing.assert_array_equal(
            native[index], np.moveaxis(original, channel_axis, 0)
        )
        np.testing.assert_array_equal(item.data, original)
        assert item.image_metadata.axis_position(ColourAxis) == channel_axis
        assert item.image_metadata.source_image_provenance_planes.paths == (
            f"/synthetic/A01_s{index + 1:03}_w2.tif",
        )


@pytest.mark.parametrize("channels", (3, 4))
@pytest.mark.parametrize("site_count", (1, 2))
def test_rgb_rgba_stay_trailing_color_carriers(channels, site_count):
    server, items, originals = _display(channels, -1, site_count)
    native, kwargs = server.viewer.calls[-1][1], server.viewer.calls[-1][3]
    assert native.shape == (site_count, 8, 8, channels)
    assert kwargs["rgb"] is True
    assert kwargs["axis_labels"] == ("site", "y", "x")
    assert kwargs["scale"] == (1.0, 0.5, 0.5)
    for index, (item, original) in enumerate(zip(items, originals, strict=True)):
        np.testing.assert_array_equal(native[index], original)
        np.testing.assert_array_equal(item.data, original)


def test_undeclared_extra_axis_is_not_guessed_as_rgb():
    from openhcs.runtime.napari_streaming_handlers import (
        NapariImagePayloadAxisLabelPolicy,
    )

    with pytest.raises(ValueError, match="component-axis binding"):
        NapariImagePayloadAxisLabelPolicy.axis_labels(
            np.ones((8, 8, 3)), ImagePayloadMetadata()
        )


@pytest.mark.parametrize(
    "shape,axis", (((8, 8, 1), 3), ((8, 8, 1), -4), ((8, 8, 0), -1))
)
def test_invalid_channel_declarations_fail_closed(shape, axis):
    with pytest.raises(ValueError):
        NapariImageLayerPresentationPolicy.for_payload(
            np.ones(shape), ImagePayloadMetadata(axes=PayloadAxes.colour_samples(axis))
        )


@pytest.mark.parametrize("channels", (3, 4))
def test_rgb_nontrailing_guard_is_retained(channels):
    with pytest.raises(ValueError, match="to be last"):
        _display(channels, 0, 1)


def test_scalar_width_three_is_explicitly_non_rgb():
    data = np.ones((8, 3))
    policy = NapariImageLayerPresentationPolicy.for_payload(
        data, ImagePayloadMetadata()
    )
    assert policy.present_data(data) is data
    assert policy.payload_axis_labels == ()
    assert policy.layer_kwargs(None) == {
        "blending": "additive",
        "rgb": False,
        "colormap": "gray",
    }


def test_independent_band_capability_cooperates_without_consumer_edits():
    class DefaultBandColormap:
        def color_kwargs(self, colormap):
            return super().color_kwargs("magma" if colormap is None else colormap)

    class IndependentBandPresentation(
        DefaultBandColormap, NapariSourceChannelImageLayerPresentationPolicy
    ):
        pass

    # A legitimate seven-band carrier follows the same consumer algorithm.
    data = np.arange(8 * 8 * 7, dtype=np.float32).reshape(8, 8, 7)
    policy = IndependentBandPresentation(relative_channel_axis=-1)
    native = policy.present_data(data)
    assert policy.payload_axis_labels == ("source_channel",)
    assert native.shape == (7, 8, 8)
    assert np.shares_memory(native, data)
    np.testing.assert_array_equal(native[6], data[:, :, 6])
    assert policy.layer_kwargs(None) == {
        "blending": "additive",
        "rgb": False,
        "colormap": "magma",
    }
    assert policy.layer_kwargs("green")["colormap"] == "green"
