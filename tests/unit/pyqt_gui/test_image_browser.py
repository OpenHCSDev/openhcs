"""The image browser renders what the axis family, file records and viewers declare."""

from __future__ import annotations

from collections.abc import Iterator
from pathlib import Path

import pytest
from objectstate import ObjectStateRegistry
from objectstate.global_config import set_global_config_for_editing
from PyQt6.QtCore import Qt
from pyqt_reactive.theming import ColorScheme
from pyqt_reactive.widgets.shared.record_table_browser import LabelledValue

from openhcs.core.axes import AxisFamily, GridAddressed
from openhcs.core.config import GlobalPipelineConfig, StreamingConfig
from openhcs.core.plate_image_inventory import PlateFileKind, PlateFileRecord
from openhcs.core.result_file_formats import RoiArchiveResultFile, TextResultFile
from openhcs.domains.microscopy.axes import Microscopy
from openhcs.pyqt_gui.config import ProgressUIConfig
from openhcs.pyqt_gui.widgets import image_browser
from openhcs.pyqt_gui.widgets.image_browser import (
    ImageBrowserWidget,
    NoDataset,
    viewer_actions,
)
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG
from tests.unit.remote_sensing_witness_domain import RemoteSensing


class _Files(NoDataset):
    """A dataset of in-memory records that labels every axis value."""

    def __init__(self, records: tuple[PlateFileRecord, ...]) -> None:
        self._records = records
        self.viewed: list[tuple[list[str], list[str], str]] = []

    def records(self) -> tuple[PlateFileRecord, ...]:
        return self._records

    def labelled(self, column_key: str, raw: str) -> LabelledValue:
        family = AxisFamily.active()
        if column_key not in family.names():
            return LabelledValue(column_key, raw)
        return LabelledValue(column_key, raw, label="label", source=family.named(column_key))

    def grid_positions(self, axis, values):
        return {axis.grid_index(value): value for value in values}

    def view(self, batch, config, status, failed) -> None:
        self.viewed.append((batch.image_paths, batch.roi_paths, config.viewer_family.display_name))
        status("sent")


def _image(key: str, **axis_values: str) -> PlateFileRecord:
    return PlateFileRecord(
        kind=PlateFileKind.IMAGE,
        key=key,
        metadata={"filename": key, "type": "Image", "extension": ".tif", **axis_values},
    )


def _result(key: str, file_format, **axis_values: str) -> PlateFileRecord:
    return PlateFileRecord(
        kind=PlateFileKind.RESULT,
        key=key,
        metadata={"filename": key, "type": file_format.name, **axis_values},
        relative_path=key,
        full_path=f"/plate/{key}",
        file_format=file_format,
    )


def _browser(qapp, dataset: NoDataset) -> ImageBrowserWidget:
    browser = ImageBrowserWidget(
        dataset,
        color_scheme=ColorScheme(),
        zmq_config=OPENHCS_ZMQ_CONFIG,
        progress_config=ProgressUIConfig(),
    )
    browser.load_files()
    qapp.processEvents()
    return browser


def _close(qapp, browser: ImageBrowserWidget) -> None:
    browser.cleanup()
    browser.cleanup()  # a second release is a no-op: the browser holds NoDataset
    browser.close()
    browser.deleteLater()
    qapp.processEvents()


def _column_keys(browser: ImageBrowserWidget) -> tuple[str, ...]:
    return tuple(column.key for column in browser.table.column_presentation.columns)


@pytest.fixture
def synchronous_threads(monkeypatch) -> None:
    monkeypatch.setattr(
        image_browser, "spawn_thread_with_context", lambda target, name: target()
    )


@pytest.fixture
def remote_sensing() -> Iterator[type[RemoteSensing]]:
    # Config defaults name the active family's axes, so the global config other
    # tests left behind is rebuilt under each family.
    RemoteSensing.activate()
    _reset_global_config()
    try:
        yield RemoteSensing
    finally:
        Microscopy.activate()
        ObjectStateRegistry.clear()


def _reset_global_config() -> None:
    ObjectStateRegistry.clear()
    set_global_config_for_editing(GlobalPipelineConfig, GlobalPipelineConfig())


def test_microscopy_files_show_axis_columns_filters_grid_and_folders(qapp) -> None:
    dataset = _Files(
        (
            _image("images/A01_s1_w1.tif", well="A01", site="1", channel="1"),
            _image("images/B03_s1_w2.tif", well="B03", site="1", channel="2"),
            _result("images_results/A01.roi.zip", RoiArchiveResultFile, well="A01"),
            _result("images_results/notes.txt", TextResultFile),
        )
    )
    browser = _browser(qapp, dataset)
    try:
        table = browser.table
        axis_keys = tuple(
            name for name in Microscopy.names() if name in {"well", "site", "channel"}
        )
        assert _column_keys(browser) == ("filename", *axis_keys, "extension", "type")
        headers = {column.key: column.name for column in table.column_presentation.columns}
        assert headers["well"] == Microscopy.Well.label
        assert tuple(table.column_filter_panel.column_filters) == (
            *axis_keys,
            "extension",
            "type",
        )
        assert table.column_filter_panel.column_filters["well"].unique_values == [
            "A01 | label",
            "B03 | label",
            "N/A",
        ]
        # A labelled cell keeps the axis that supplied its label.
        (shown,) = table.value_labels.shown("well", ["A01 | label"])
        assert (shown.raw, shown.source) == ("A01", Microscopy.Well)
        assert browser.info_label.text() == "4 files loaded (2 images, 2 results)"
        assert table.status_label.text() == "Showing 4/4 files"

        # The results folder has no tree item; its files show with their image folder.
        root = browser.folder_tree.topLevelItem(0)
        assert [root.child(i).text(0) for i in range(root.childCount())] == ["images"]
        assert table.column_filter_context_widget is browser.folder_tree
        root.child(0).setSelected(True)
        assert len(table.filtered_items) == 4

        # One grid per GridAddressed axis, joined to that axis's column filter.
        (grid,) = browser.grids
        assert grid.axis is Microscopy.Well
        assert grid.panel.toggle_button.text() == f"Show {Microscopy.Well.label} Grid"
        grid.panel.toggle_button.click()
        selector = grid.link.grid
        assert selector.model.available == {"A01", "B03"}
        selector.select_cells({"B03"})
        assert tuple(table.filtered_items) == ("images/B03_s1_w2.tif",)
        assert table.set_column_filter_selection("well", ("A01 | label",))
        assert selector.selected == {"A01"}
        assert set(table.filtered_items) == {
            "images/A01_s1_w1.tif",
            "images_results/A01.roi.zip",
        }

        selector.clear_selection()
        table.search_input.setText("roi")
        assert browser.focus_file_by_path("/elsewhere/notes.txt")
        assert table.get_selected_keys() == ["images_results/notes.txt"]
    finally:
        _close(qapp, browser)


def test_selection_goes_to_viewers_the_way_each_file_kind_declares(
    qapp, monkeypatch, synchronous_threads
) -> None:
    dataset = _Files(
        (
            _image("images/A01.tif", well="A01"),
            _result("images_results/A01.roi.zip", RoiArchiveResultFile, well="A01"),
            _result("images_results/notes.txt", TextResultFile),
        )
    )
    prompts: list[str] = []
    opened: list[list[str]] = []
    monkeypatch.setattr(
        image_browser.QMessageBox,
        "information",
        lambda _parent, _title, text: prompts.append(text),
    )
    monkeypatch.setattr(
        image_browser.subprocess, "run", lambda command, check: opened.append(command)
    )
    browser = _browser(qapp, dataset)
    try:
        table = browser.table
        actions = viewer_actions()
        assert [action.field_name for action in actions] == list(
            StreamingConfig.supported_config_keys()
        )
        assert tuple(browser.viewer_tabs.buttons) == actions
        first = actions[0]
        button = browser.viewer_tabs.buttons[first]
        assert button.text() == f"View in {first.title}"

        table.select_keys(list(table.all_items))
        image, roi, text = (table.all_items[key] for key in table.all_items)

        # No viewer is switched on: double-clicking asks for one.
        for action in actions:
            browser.state.update_parameter(action.enabled_path, False)
        assert not button.isEnabled()
        image.open(browser)
        roi.open(browser)
        assert prompts == [
            "Please enable at least one viewer streaming to view images.",
            "Please enable at least one viewer streaming to view ROIs.",
        ]
        assert dataset.viewed == []

        browser.state.update_parameter(first.enabled_path, True)
        browser.viewer_tabs.parameter_changed.emit(first.enabled_path, True)
        assert button.isEnabled()

        # The button sends the whole selection as one batch; the text file adds nothing.
        button.click()
        viewer_name = browser.state.get_resolved_value(first.field_name).viewer_family.display_name
        assert dataset.viewed == [
            (["images/A01.tif"], ["/plate/images_results/A01.roi.zip"], viewer_name)
        ]
        qapp.processEvents()
        assert browser.info_label.text() == "sent"

        # Double-click: an image sends the selection, a ROI archive sends itself,
        # a text file opens in the desktop's default application.
        dataset.viewed.clear()
        image.open(browser)
        roi.open(browser)
        text.open(browser)
        assert [(images, rois) for images, rois, _viewer in dataset.viewed] == [
            (["images/A01.tif"], ["/plate/images_results/A01.roi.zip"]),
            ([], ["/plate/images_results/A01.roi.zip"]),
        ]
        assert opened == [["xdg-open", str(Path("/plate/images_results/notes.txt"))]]
    finally:
        _close(qapp, browser)


def test_remote_sensing_family_needs_no_widget_edit(qapp, remote_sensing) -> None:
    """New case: another axis family gets its own columns and filters, and no grid."""

    dataset = _Files(
        (
            _image("scenes/s1_t1_b1.tif", scene="s1", tile="1", band="1", date="20260101"),
            _image("scenes/s2_t1_b2.tif", scene="s2", tile="1", band="2", date="20260102"),
        )
    )
    browser = _browser(qapp, dataset)
    try:
        table = browser.table
        assert remote_sensing.with_role(GridAddressed) == ()
        assert browser.grids == ()
        assert _column_keys(browser) == (
            "filename",
            *remote_sensing.names(),
            "extension",
            "type",
        )
        assert [
            column.name for column in table.column_presentation.columns[1:5]
        ] == [remote_sensing.named(name).label for name in remote_sensing.names()]
        assert tuple(table.column_filter_panel.column_filters) == (
            *remote_sensing.names(),
            "extension",
            "type",
        )
        (shown,) = table.value_labels.shown("band", ["2 | label"])
        assert shown.source is remote_sensing.Band
        assert table.set_column_filter_selection("scene", ("s2 | label",))
        assert tuple(table.filtered_items) == ("scenes/s2_t1_b2.tif",)
        assert table.table_widget.horizontalHeaderItem(0).text() == "Filename"
        assert table.table_widget.item(0, 0).data(Qt.ItemDataRole.UserRole) == (
            "scenes/s2_t1_b2.tif"
        )
    finally:
        _close(qapp, browser)
