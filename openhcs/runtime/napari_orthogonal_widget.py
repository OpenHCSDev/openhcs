"""Bundled native plane selector: a consumer of the managed navigation owner."""

from __future__ import annotations

from itertools import combinations
from typing import TYPE_CHECKING
from weakref import ref

from napari import Viewer
from qtpy.QtWidgets import QComboBox, QLabel, QPushButton, QVBoxLayout, QWidget

from openhcs.runtime.viewer_controls import ViewerNavigationControlOptions

if TYPE_CHECKING:
    from openhcs.runtime.napari_viewer_server import NapariViewerServer


class OpenHCSOrthogonalWidget(QWidget):
    """Project mounted semantic routes into the shared typed native command."""

    def __init__(self, server: NapariViewerServer):
        super().__init__()
        self._server = ref(server)
        self.routes = QComboBox(self)
        self.planes = QComboBox(self)
        self.apply_button = QPushButton("Apply spatial plane", self)
        self.status = QLabel(self)
        self.status.setWordWrap(True)
        layout = QVBoxLayout(self)
        for widget in (self.routes, self.planes, self.apply_button, self.status):
            layout.addWidget(widget)
        self.routes.currentIndexChanged.connect(self.refresh_planes)
        self.apply_button.clicked.connect(self.apply_plane)
        server.viewer.dims.events.order.connect(self.read_native_state)
        server.viewer.dims.events.ndisplay.connect(self.read_native_state)
        self.refresh()

    @property
    def server(self) -> NapariViewerServer:
        server = self._server()
        if server is None or server.viewer is None:
            raise RuntimeError("The managed OpenHCS viewer is no longer available.")
        return server

    def refresh(self) -> None:
        selected = self.routes.currentData()
        self.routes.blockSignals(True)
        self.routes.clear()
        for route, state in self.server.layer_route_state.mounted_dimension_states():
            if state.presentation is not None:
                self.routes.addItem(
                    self.server.layer_route_state.layer_titles[route], route
                )
        previous = self.routes.findData(selected)
        if previous >= 0:
            self.routes.setCurrentIndex(previous)
        self.routes.blockSignals(False)
        self.refresh_planes()

    def refresh_planes(self, *_args) -> None:
        self.planes.clear()
        route = self.routes.currentData()
        if route is not None:
            presentation = self.server.layer_route_state.dimension_state_for(
                route
            ).presentation
            if presentation is not None:
                for pair in combinations(presentation.spatial_axis_labels, 2):
                    self.planes.addItem(" / ".join(pair), pair)
        self.apply_button.setEnabled(self.planes.count() > 0)
        self.read_native_state()

    def read_native_state(self, *_args) -> None:
        dims = self.server.viewer.dims
        axes = tuple(str(dims.axis_labels[axis]) for axis in dims.displayed)
        self.status.setText(
            f"Actual native view: {' / '.join(axes)} ({dims.ndisplay}D)"
        )

    def apply_plane(self) -> None:
        from openhcs.runtime.napari_viewer_server import (
            NapariNavigationControlMessageAction,
        )

        route, pair = self.routes.currentData(), self.planes.currentData()
        if route is None or pair is None:
            return
        reply = NapariNavigationControlMessageAction().handle(
            self.server,
            {
                "payload": ViewerNavigationControlOptions(
                    route_key=route, display_axes=pair
                )
            },
        )
        self.read_native_state()
        if reply["status"] != "success":
            self.status.setText(str(reply["message"]))


def make_orthogonal_widget(napari_viewer: Viewer) -> OpenHCSOrthogonalWidget:
    """Bind through the existing Qt owner graph; never infer unmanaged routes."""
    widgets = napari_viewer.window.qt_viewer.window().findChildren(
        OpenHCSOrthogonalWidget
    )
    if not widgets:
        raise ValueError(
            "OpenHCS orthogonal review requires an OpenHCS managed viewer."
        )
    return OpenHCSOrthogonalWidget(widgets[0].server)
