"""Native frame completion against the installed Napari layer slicing API."""

from __future__ import annotations

from types import SimpleNamespace

import numpy as np
import pytest

napari_components = pytest.importorskip("napari.components")

from openhcs.runtime.napari_viewer_server import NapariLayerDisplayPipeline  # noqa: E402


def _pipeline_for(viewer) -> SimpleNamespace:
    return SimpleNamespace(
        server=SimpleNamespace(require_viewer=lambda: viewer),
        _native_frame_mutation_depth=0,
    )


def test_native_frame_applied_compares_slices_from_real_napari_layers():
    viewer = napari_components.ViewerModel()
    layer = viewer.add_image(np.zeros((3, 8, 8), dtype=np.uint16))
    pipeline = _pipeline_for(viewer)

    assert NapariLayerDisplayPipeline.native_frame_applied(pipeline)

    applied_slice = layer._slice_input
    viewer.dims.set_current_step(0, 2)
    assert layer._slice_input != applied_slice
    layer._slicing_state._slice_input = applied_slice
    assert not NapariLayerDisplayPipeline.native_frame_applied(pipeline)
