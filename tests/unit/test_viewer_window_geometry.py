"""The MCP viewer observation reports the live canvas, not a cached window size."""

from types import SimpleNamespace

import pytest

from openhcs.runtime.viewer_protocol import ViewerWindowGeometry


def test_window_geometry_rejects_invalid_dimensions():
    with pytest.raises(ValueError, match="canvas_size"):
        ViewerWindowGeometry(window_size=(800, 600), canvas_size=(-1, 400))
    with pytest.raises(ValueError, match="window_size"):
        ViewerWindowGeometry(window_size=(True, 600), canvas_size=(700, 400))


def test_napari_window_geometry_reads_each_resize():
    server_module = pytest.importorskip("openhcs.runtime.napari_viewer_server")

    class Widget:
        def __init__(self, width: int, height: int):
            self.w = width
            self.h = height

        def width(self) -> int:
            return self.w

        def height(self) -> int:
            return self.h

    window = Widget(1200, 800)
    canvas = Widget(900, 650)
    qt_viewer = SimpleNamespace(
        window=lambda: window, canvas=SimpleNamespace(native=canvas)
    )
    viewer = SimpleNamespace(window=SimpleNamespace(qt_viewer=qt_viewer))

    first = server_module._napari_window_geometry(viewer)
    assert first == ViewerWindowGeometry((1200, 800), (900, 650))

    window.w = 1000
    canvas.w = 700
    second = server_module._napari_window_geometry(viewer)
    assert second == ViewerWindowGeometry((1000, 800), (700, 650))
    assert second != first
