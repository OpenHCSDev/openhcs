"""Original display admission and detached native presentation boundaries."""

from dataclasses import dataclass

import pytest

from openhcs.agent.dto.plate import PlateFileStreamRequest
from openhcs.agent.services.plate_streaming_service import PlateStreamingService
from openhcs.core.config import (
    FijiStreamingConfig, NapariDisplayConfig, NapariDimensionMode, NapariStreamingConfig,
)


def test_stream_admits_original_display_declaration_without_changing_endpoint():
    display = NapariDisplayConfig(channel_mode=NapariDimensionMode.LAYER, colormap="green")
    request = PlateFileStreamRequest.from_fields(
        plate_path="/synthetic", display_config=display, port=6004,
    )
    config = PlateStreamingService._streaming_config(request)
    assert config.channel_mode is NapariDimensionMode.LAYER
    assert config.colormap == "green"
    assert config.port == 6004
    assert request.as_tool_arguments()["display_config"]["channel_mode"] == "layer"
    assert isinstance(config, NapariDisplayConfig)


def test_missing_display_preserves_default_and_wrong_viewer_fails_closed():
    config = NapariStreamingConfig()
    assert config.with_display_config(None) is config
    with pytest.raises(TypeError, match="selected viewer"):
        FijiStreamingConfig().with_display_config(NapariDisplayConfig())


def test_new_display_leaf_uses_existing_admission_without_consumer_edits():
    @dataclass(frozen=True)
    class IndependentPalette:
        palette_label: str = "new palette"

    @dataclass(frozen=True)
    class NewDisplay(NapariDisplayConfig, IndependentPalette):
        pass

    @dataclass(frozen=True)
    class NewStreaming(NapariStreamingConfig, NewDisplay):
        pass

    config = NewStreaming(port=6004).with_display_config(NewDisplay(palette_label="new"))
    assert config.palette_label == "new"
    assert config.port == 6004
    assert config.component_modes()["channel"] == "stack"


def test_channel_carrier_title_describes_identity_not_rgb_cardinality():
    from openhcs.runtime.napari_viewer_server import NapariImagePayloadLayoutRole

    role = NapariImagePayloadLayoutRole.COLOR_PLANE
    assert role.title("selected_images") == "selected_images source channels"
    assert role.route_key("selected_images") == "selected_images_color_plane"
    assert NapariImagePayloadLayoutRole.SCALAR_PLANE.title("raw") == "raw"
