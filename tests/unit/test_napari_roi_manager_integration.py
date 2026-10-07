"""Integration tests for the first-party native Napari ROI Manager."""

from pathlib import Path
import tomllib

import numpy as np
from packaging.requirements import Requirement
import pytest
import yaml

REPOSITORY_ROOT = Path(__file__).resolve().parents[2]


@pytest.mark.unit
def test_existing_openhcs_manifest_owns_roi_manager_widget() -> None:
    manifest = yaml.safe_load(
        (REPOSITORY_ROOT / "openhcs" / "napari.yaml").read_text(encoding="utf-8")
    )

    assert manifest["name"] == "openhcs"
    commands = {
        command["id"]: command for command in manifest["contributions"]["commands"]
    }
    command = commands["openhcs.make_roi_manager_widget"]
    assert command["python_name"] == "openhcs.napari_roi_manager:QRoiManager"
    assert manifest["contributions"]["widgets"] == [
        {
            "command": "openhcs.make_roi_manager_widget",
            "display_name": "OpenHCS ROI Manager",
        }
    ]


@pytest.mark.unit
def test_roi_manager_has_no_mandatory_external_distribution() -> None:
    project = tomllib.loads(
        (REPOSITORY_ROOT / "pyproject.toml").read_text(encoding="utf-8")
    )["project"]

    requirements = {
        Requirement(requirement).name
        for extra in ("napari", "viz", "all")
        for requirement in project["optional-dependencies"][extra]
    }
    assert "napari-roi-manager" not in requirements
    assert "openhcs-napari-roi-manager" not in requirements
    assert project["license-files"] == ["LICENSE", "THIRD_PARTY_LICENSES/*"]
    notice = REPOSITORY_ROOT / "THIRD_PARTY_LICENSES" / "napari-roi-manager-LICENSE"
    assert "Copyright (c) 2024, Hanjin Liu" in notice.read_text(encoding="utf-8")


@pytest.mark.unit
def test_roi_feature_json_round_trip_preserves_native_values() -> None:
    pytest.importorskip("napari")
    from napari.layers.shapes._shapes_constants import ShapeType

    import openhcs.napari_roi_manager as roi_manager
    from openhcs.napari_roi_manager._dataclasses import RoiData

    assert not hasattr(roi_manager, "__version__")

    rois = RoiData(
        data=[np.array(((0.0, 0.0), (1.0, 1.0)))],
        shape_type=[ShapeType.LINE],
        names=["axon"],
        features={"area": [np.float32(4.5)], "position": [np.int64(7)]},
    )

    restored = RoiData.from_json_dict(rois.to_json_dict())

    assert restored.names == ["axon"]
    assert restored.features == {"area": [4.5], "position": [7]}


@pytest.mark.unit
def test_result_binding_reuses_one_mounted_roi_manager_for_native_layers() -> None:
    napari_viewer_server = pytest.importorskip("openhcs.runtime.napari_viewer_server")

    events: list[object] = []

    class RoiManagerDock:
        def show(self) -> None:
            events.append("manager_show")

    class RoiManagerWidget:
        def connect_layer(self, layer) -> None:
            events.append(("manager_bind", layer))

    manager_dock = RoiManagerDock()
    manager_widget = RoiManagerWidget()

    class ResultSelectionController:
        @staticmethod
        def bind(layer) -> None:
            events.append(("selection_bind", layer))

    server = napari_viewer_server.NapariViewerServer.__new__(
        napari_viewer_server.NapariViewerServer
    )
    server.viewer = object()
    server.result_selection_controller = ResultSelectionController()
    server.result_selection_surface = napari_viewer_server.NapariResultSelectionSurface(
        dock=manager_dock,
        manager=manager_widget,
    )
    first_layer = object()
    second_layer = object()

    server.bind_result_selection_layer(first_layer)
    server.bind_result_selection_layer(second_layer)

    assert events == [
        ("selection_bind", first_layer),
        ("manager_bind", first_layer),
        "manager_show",
        ("selection_bind", second_layer),
        ("manager_bind", second_layer),
        "manager_show",
    ]


@pytest.mark.unit
def test_installed_manager_binds_and_selects_native_shapes_without_copying(
    qtbot,
) -> None:
    napari = pytest.importorskip("napari")
    pytest.importorskip("openhcs.napari_roi_manager")
    napari_viewer_server = pytest.importorskip("openhcs.runtime.napari_viewer_server")
    viewer = napari.Viewer(show=False)
    qtbot.addWidget(viewer.window._qt_window)
    layer = viewer.add_shapes(
        [
            np.array([[0, 0], [0, 4], [4, 4]], dtype=float),
            np.array([[8, 8], [8, 12], [12, 12]], dtype=float),
        ],
        shape_type=("polygon", "polygon"),
        features={"name": ("first", "second"), "area": (8.0, 8.0)},
        name="Native ROIs",
    )

    class ResultSelectionController(napari_viewer_server.NapariResultSelectionController):
        @staticmethod
        def bind(_layer) -> None:
            return None

    server = napari_viewer_server.NapariViewerServer.__new__(
        napari_viewer_server.NapariViewerServer
    )
    server.viewer = viewer
    server.result_selection_controller = ResultSelectionController(server)
    server.result_selection_surface = None
    original_layers = tuple(viewer.layers)

    server.bind_result_selection_layer(layer)

    surface = server.require_result_selection_surface()
    manager = surface.manager
    assert tuple(viewer.layers) == original_layers
    assert manager._layer is layer
    assert manager._roilist.rowCount() == 2
    from openhcs.napari_roi_manager.widgets._roi_manager import RoiTableColumn

    assert manager._roilist._roi_model.column_values(RoiTableColumn.NAME) == [
        "first",
        "second",
    ]

    manager._roilist.selectRow(1)
    assert layer.selected_data == {1}

    second_layer = viewer.add_shapes(
        [np.array([[16, 16], [16, 20], [20, 20]], dtype=float)],
        shape_type="polygon",
        features={"name": ("third",)},
        name="Second ROI set",
    )
    original_manager = manager
    server.bind_result_selection_layer(second_layer)

    assert server.require_result_selection_surface().manager is original_manager
    assert manager._layer is second_layer
    assert manager._roilist._roi_model.column_values(RoiTableColumn.NAME) == ["third"]
    viewer.close()


@pytest.mark.unit
@pytest.mark.parametrize("destroy", [
    "napari_close", "manager", "immediate_manager", "window",
    "manager_then_dock", "manager_then_window",
])
def test_result_surface_native_destruction_releases_and_remounts(qtbot, destroy):
    napari = pytest.importorskip("napari")
    module = pytest.importorskip("openhcs.runtime.napari_viewer_server")
    from qtpy import sip
    from qtpy.QtCore import QCoreApplication, QEvent
    from qtpy.QtWidgets import QToolBar
    from napari.settings import get_settings

    viewer = napari.Viewer(show=False)
    if destroy not in ("window", "manager_then_window"):
        qtbot.addWidget(viewer.window._qt_window)
    server = module.NapariViewerServer.__new__(module.NapariViewerServer)
    server.viewer = viewer
    server.result_selection_surface = None
    server.layer_route_state = module.NapariLayerRouteStateStore.empty()
    server.result_selection_controller = module.NapariResultSelectionController(server)
    controller = server.result_selection_controller
    layer = viewer.add_shapes(
        [np.array([[0, 0], [0, 4], [4, 4]], dtype=float)],
        shape_type="polygon", features={"name": ["first"]}, name="First result",
    )
    server.layer_route_state.set_layer("first", layer)
    server.bind_result_selection_layer(layer)
    original = server.require_result_selection_surface()
    toolbars = viewer.window._qt_window.findChildren(QToolBar, "openhcs_roi_selection_toolbar")
    assert len(toolbars) == 1
    assert len(controller._selection_observers) == 1
    original.manager.hide()
    original.manager.show()
    assert server.require_result_selection_surface() is original

    if destroy == "napari_close":
        viewer.window.remove_dock_widget(original.dock)
    elif destroy == "manager":
        original.manager.deleteLater()
    elif destroy == "immediate_manager":
        sip.delete(original.manager)
        QCoreApplication.processEvents()
    elif destroy == "manager_then_dock":
        sip.delete(original.manager)
        viewer.window.remove_dock_widget(original.dock)
    elif destroy == "manager_then_window":
        sip.delete(original.manager)
        sip.delete(viewer.window._qt_window)
    else:
        sip.delete(viewer.window._qt_window)
    QCoreApplication.sendPostedEvents(None, QEvent.Type.DeferredDelete)
    QCoreApplication.sendPostedEvents(None, QEvent.Type.DeferredDelete)
    assert server.result_selection_surface is None
    assert controller._selection_observers == []
    assert original.manager._layer_connections == []
    assert not original.manager._viewer_selection_connected
    assert sip.isdeleted(original.dock)
    assert sip.isdeleted(original.manager)
    assert sip.isdeleted(toolbars[0])

    if destroy in ("window", "manager_then_window"):
        return

    next_layer = viewer.add_shapes(
        [np.array([[8, 8], [8, 12], [12, 12]], dtype=float)],
        shape_type="polygon", features={"name": ["next"]}, name="Next streamed result",
    )
    server.layer_route_state.set_layer("next", next_layer)
    server.bind_result_selection_layer(next_layer)
    replacement = server.require_result_selection_surface()
    assert replacement is not original
    assert replacement.manager._layer is next_layer
    assert replacement.manager._roilist.rowCount() == 1
    assert len(controller._selection_observers) == 1
    assert len(viewer.window._qt_window.findChildren(QToolBar, "openhcs_roi_selection_toolbar")) == 1
    get_settings().appearance.highlight.highlight_thickness = 5
    controller._notify_selection_observers()
    viewer.close()


@pytest.mark.unit
def test_roi_manager_virtualizes_thousands_over_one_native_shapes_owner(
    qtbot,
) -> None:
    pytest.importorskip("napari")
    from napari.components import ViewerModel
    from qtpy import QtCore
    from qtpy.QtWidgets import QHeaderView, QTableView, QTableWidget

    from openhcs.napari_roi_manager.widgets._roi_manager import (
        QRoiManager,
        RoiTableColumn,
    )

    member_count = 4_097
    viewer = ViewerModel()
    layer = viewer.add_shapes(
        [
            np.asarray(
                ((index, 0.0), (index, 1.0), (index + 1.0, 0.0)),
                dtype=float,
            )
            for index in range(member_count)
        ],
        shape_type=["polygon"] * member_count,
        features={
            "name": [f"ROI-{index:04d}" for index in range(member_count)],
            "area": [0.5] * member_count,
        },
        name="Large native ROI set",
        visible=False,
    )
    manager = QRoiManager(viewer)
    qtbot.addWidget(manager)
    table = manager._roilist
    model = table._roi_model

    assert isinstance(table, QTableView)
    assert not isinstance(table, QTableWidget)
    assert manager.findChildren(QTableWidget) == []
    assert (
        table.horizontalHeader().sectionResizeMode(RoiTableColumn.SHAPE_TYPE)
        is QHeaderView.ResizeMode.Interactive
    )
    assert model.rowCount() == member_count
    last_name = model.index(member_count - 1, RoiTableColumn.NAME)
    assert model.data(last_name) == f"ROI-{member_count - 1:04d}"

    feature_events = []
    layer.events.features.connect(feature_events.append)
    assert model.setData(
        last_name,
        "renamed-last",
        QtCore.Qt.ItemDataRole.EditRole,
    )
    assert layer.features["name"].iat[-1] == "renamed-last"
    assert len(feature_events) == 1

    table.selectRow(member_count - 1)
    assert layer.selected_data == {member_count - 1}
    manager.close()
