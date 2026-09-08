"""Route-local navigation must use the same shared slots as layer placement."""

import pytest

from openhcs.runtime.napari_streaming_handlers import NapariAxisPresentation
from openhcs.runtime.viewer_component_system import (
    ViewerComponentAxisSemanticsAuthority,
    ViewerComponentLayout,
    ViewerLayerAxisProjection,
)
from zmqruntime.viewer_protocol import ViewerComponentMode


@pytest.mark.parametrize(
    "display_axes", [("channel",), ("site", "channel"), ("site", "z_index", "channel")]
)
@pytest.mark.parametrize("viewer_origin", [0, 1])
def test_navigation_inverts_route_placement_with_inserted_singleton_axes(
    display_axes, viewer_origin
):
    semantics = ViewerComponentAxisSemanticsAuthority.empty()
    presentation = NapariAxisPresentation(
        entries=semantics.entries,
        layout=ViewerComponentLayout.from_parts(
            component_modes={axis: ViewerComponentMode.STACK for axis in display_axes},
            component_order=display_axes,
        ),
        route_key="processed-channel",
        projection=ViewerLayerAxisProjection(
            projected_axis_components=("channel",),
            component_values={"channel": [2]},
            routed_component_values={"channel": [2]},
            axis_offsets=(1,),
            scalar_component_values={},
        ),
    )
    display_index = presentation.viewer_axis_index(0)
    step = presentation.viewer_step(0, display_index, viewer_axis_origin=viewer_origin)
    assert step + viewer_origin == presentation.translate()[display_index]
    assert presentation.label_index(step, 0, viewer_axis_origin=viewer_origin) == 0
