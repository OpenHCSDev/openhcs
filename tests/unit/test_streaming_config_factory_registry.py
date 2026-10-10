"""Each streaming viewer is one ViewerFamily class; everything else is derived."""

import pytest

from openhcs.core.config import StreamingConfig
from openhcs.core.streaming_config_declarations import (
    NapariViewer,
    ViewerFamily,
    ViewerType,
)
from openhcs.runtime.viewer_protocol import ManagedViewerLifecycleMixin

VIEWER_FAMILIES = ViewerFamily.families()


@pytest.mark.parametrize("family", VIEWER_FAMILIES, ids=lambda item: item.wire_value)
def test_viewer_family_owns_visualizer_config_and_boundary_name(family) -> None:
    visualizer_type = family.visualizer_type()

    assert visualizer_type.detached_server_entrypoint.viewer_family is family
    assert ManagedViewerLifecycleMixin.__registry__[family.wire_value] is visualizer_type
    assert StreamingConfig.config_type_for_key(family.config_key).viewer_family is family
    assert ViewerFamily.named(family.viewer_type()) is family
    assert family.viewer_type().family is family


def test_viewer_names_derive_from_the_family_declaration() -> None:
    assert NapariViewer.config_key == "napari_streaming_config"
    assert NapariViewer.step_plan_output_key == "napari_streaming_paths"
    assert NapariViewer.display_name == "Napari"
    assert NapariViewer.title == "OpenHCS Napari Visualization"
    assert set(StreamingConfig.__registry__) == set(VIEWER_FAMILIES)
    assert {member.value for member in ViewerType} == {
        family.wire_value for family in VIEWER_FAMILIES
    }


def test_viewer_names_parse_only_at_the_wire_boundary() -> None:
    assert ViewerFamily.named("fiji").viewer_type() is ViewerType.FIJI
    with pytest.raises(ValueError):
        ViewerFamily.named("FijiViewer")


@pytest.mark.parametrize("viewer_type", tuple(ViewerType), ids=lambda item: item.value)
def test_viewer_listen_interface_is_independent_of_connection_host(viewer_type):
    config_type = StreamingConfig.config_type_for_viewer(viewer_type)
    config = config_type(host="remote.example", listen_host="127.0.0.1")
    runtime = config.viewer_runtime_config()
    assert runtime.transport_endpoint.host == "remote.example"
    assert runtime.process_launch.listen_host == "127.0.0.1"

    exposed = config_type(host="127.0.0.1", listen_host="*")
    assert exposed.viewer_runtime_config().process_launch.listen_host == "*"
