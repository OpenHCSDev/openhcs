"""Browse a dataset's files and send selections to viewers.

pyqt-reactive does the browsing (record table, folder tree, grid selector,
detachable panel, config-action tabs). This module declares what OpenHCS puts
in them: the dataset being browsed, the kinds of file row, the columns the
active axis family and the file records give, and the registered viewers.
"""

from __future__ import annotations

import logging
import subprocess
from abc import ABC, abstractmethod
from collections import Counter
from collections.abc import Callable, Iterator, Mapping
from dataclasses import dataclass, field, make_dataclass
from functools import cached_property
from pathlib import Path
from typing import ClassVar

from objectstate import ScopeKey, spawn_thread_with_context
from objectstate.object_state import ObjectState, ObjectStateRegistry
from PyQt6.QtCore import Qt, QTimer, pyqtSignal
from PyQt6.QtWidgets import (
    QHBoxLayout,
    QLabel,
    QMessageBox,
    QPushButton,
    QSplitter,
    QVBoxLayout,
    QWidget,
)
from pyqt_reactive.theming import ColorScheme
from pyqt_reactive.widgets.grid_selector import GridAddressing, GridSelectorWidget
from pyqt_reactive.widgets.shared.abstract_table_browser import ColumnDef
from pyqt_reactive.widgets.shared.config_action_tabs import ConfigAction, ConfigActionTabs
from pyqt_reactive.widgets.shared.detachable_panel import DetachablePanel
from pyqt_reactive.widgets.shared.folder_tree import FolderRowFilter, FolderTreeWidget
from pyqt_reactive.widgets.shared.grid_column_filter import GridColumnFilterLink
from pyqt_reactive.widgets.shared.record_table_browser import (
    LabelledValue,
    RecordTableBrowser,
    RecordValue,
    ValueLabels,
    ValueLabelSource,
)

from openhcs.core.axes import Axis, AxisFamily, GridAddressed, OrdinalValued
from openhcs.core.config import StreamingConfig
from openhcs.core.pipeline.path_planner import ANALYSIS_RESULTS_DIR_SUFFIX
from openhcs.core.plate_image_inventory import (
    FILE_NAME_FIELD,
    PlateFileInventory,
    PlateFileRecord,
)
from openhcs.core.result_file_formats import ResultFileFormat, ResultFileOpener
from openhcs.pyqt_gui.config import ProgressUIConfig
from openhcs.pyqt_gui.services.ui_window_ids import OpenHCSUiWindowId
from openhcs.runtime.zmq_config import OpenHCSZMQConfig

logger = logging.getLogger(__name__)

ORDINAL_COLUMN_WIDTH = 70
NAME_COLUMN_WIDTH = 200


# --- Declarations derived from registries -----------------------------------

ImageBrowserConfig = make_dataclass(
    "ImageBrowserConfig",
    tuple(
        (
            config_key,
            StreamingConfig.config_type_for_key(config_key),
            field(default_factory=StreamingConfig.config_type_for_key(config_key)),
        )
        for config_key in StreamingConfig.supported_config_keys()
    ),
    frozen=False,
    slots=True,
)
"""One nested streaming config per registered viewer."""


def viewer_actions() -> tuple[ConfigAction, ...]:
    """One "view in" action per registered streaming config."""

    return tuple(
        ConfigAction(
            field_name=config_key,
            title=StreamingConfig.display_name_for_config_key(config_key),
            button_text=f"View in {StreamingConfig.display_name_for_config_key(config_key)}",
        )
        for config_key in StreamingConfig.supported_config_keys()
    )


def file_columns(record_fields: set[str]) -> tuple[ColumnDef, ...]:
    """Table columns: the file name, the active family's axes, then other record fields.

    An axis column is headed by the axis's label; the remaining fields are the
    file records' own and are headed by their title-cased key.
    """

    family = AxisFamily.active()
    axes = tuple(family.named(name) for name in family.names() if name in record_fields)
    other_fields = sorted(record_fields - set(family.names()) - {FILE_NAME_FIELD})
    return (
        ColumnDef(name="Filename", key=FILE_NAME_FIELD, width=NAME_COLUMN_WIDTH),
        *(
            ColumnDef(
                name=axis.label,
                key=axis.name,
                width=ORDINAL_COLUMN_WIDTH if issubclass(axis, OrdinalValued) else None,
                filterable=True,
            )
            for axis in axes
        ),
        *(
            ColumnDef(name=key.replace("_", " ").title(), key=key, filterable=True)
            for key in other_fields
        ),
    )


@dataclass(frozen=True, slots=True)
class GridAxisAddressing(GridAddressing):
    """Lays a GridAddressed axis's values out on the grid selector."""

    axis: type[Axis]

    @property
    def default_grid(self) -> tuple[int, int]:
        return self.axis.default_grid

    def grid_index(self, value: object) -> tuple[int, int] | None:
        return self.axis.grid_index(value)

    def row_label(self, row: int) -> str:
        return self.axis.row_label(row)


# --- File rows --------------------------------------------------------------


@dataclass(slots=True)
class ViewerBatch(ResultFileOpener):
    """What a selection of files sends to one viewer.

    A result file joins the batch the way its format opens: a format that
    streams ROIs adds its path, a format that opens in the desktop's default
    application adds nothing.
    """

    image_paths: list[str] = field(default_factory=list)
    roi_paths: list[str] = field(default_factory=list)

    def open_in_default_app(self, file_path: Path) -> None:
        """Nothing in such a file goes to a viewer."""

    def stream_rois(self, file_path: Path) -> None:
        self.roi_paths.append(str(file_path))


@dataclass(frozen=True)
class BrowsedFile(Mapping[str, RecordValue], ABC):
    """One table row: a file record. Each kind says how it opens and what it streams."""

    kind_noun: ClassVar[str]
    """Plural name of this kind in the summary line."""

    record: PlateFileRecord

    @classmethod
    def of(cls, record: PlateFileRecord) -> tuple[BrowsedFile, ...]:
        """The row a record gives; a record that is neither kind gives none."""

        image_path = record.streamable_image_path
        if image_path is not None:
            return (ImageFile(record, image_path),)
        if record.file_format is not None and record.full_path is not None:
            return (ResultFile(record, record.file_format, Path(record.full_path)),)
        return ()

    @property
    def key(self) -> str:
        return self.record.key

    @abstractmethod
    def open(self, browser: ImageBrowserWidget) -> None:
        """What double-clicking the row does."""

    @abstractmethod
    def add_to(self, batch: ViewerBatch) -> None:
        """Add what this file sends to a viewer."""

    def __getitem__(self, key: str) -> RecordValue:
        return self.record.metadata[key]

    def __iter__(self) -> Iterator[str]:
        return iter(self.record.metadata)

    def __len__(self) -> int:
        return len(self.record.metadata)


@dataclass(frozen=True)
class ImageFile(BrowsedFile):
    """A file a viewer can show as an image."""

    kind_noun: ClassVar[str] = "images"

    image_path: str

    def open(self, browser: ImageBrowserWidget) -> None:
        browser.view_in_enabled_viewers(browser.selected_files(), "images")

    def add_to(self, batch: ViewerBatch) -> None:
        batch.image_paths.append(self.image_path)


@dataclass(frozen=True)
class ResultFile(BrowsedFile):
    """A result file; its declared format decides how it opens."""

    kind_noun: ClassVar[str] = "results"

    file_format: type[ResultFileFormat]
    path: Path

    def open(self, browser: ImageBrowserWidget) -> None:
        self.file_format.open_with(ResultFileBrowserOpener(browser, self), self.path)

    def add_to(self, batch: ViewerBatch) -> None:
        self.file_format.open_with(batch, self.path)


@dataclass(frozen=True)
class ResultFileBrowserOpener(ResultFileOpener):
    """What the image browser does when a result file is opened."""

    browser: ImageBrowserWidget
    file: ResultFile

    def open_in_default_app(self, file_path: Path) -> None:
        subprocess.run(["xdg-open", str(file_path)], check=False)

    def stream_rois(self, file_path: Path) -> None:
        self.browser.view_in_enabled_viewers((self.file,), "ROIs")


# --- The dataset being browsed ----------------------------------------------


class BrowsedDataset(ValueLabelSource):
    """The dataset whose files the browser shows, or the lack of one."""

    @abstractmethod
    def config_state(self, config: object) -> ObjectState:
        """The viewer-config state for this dataset."""

    @abstractmethod
    def release_state(self, state: ObjectState) -> None:
        """Undo whatever ``config_state`` registered."""

    @abstractmethod
    def records(self) -> tuple[PlateFileRecord, ...]:
        """Every image and result file record."""

    @abstractmethod
    def viewer_ports(self, ports_per_type: int) -> list[int]:
        """Ports on which this dataset's viewers may listen."""

    @abstractmethod
    def grid_positions(
        self, axis: type[Axis], values: set[str]
    ) -> dict[tuple[int, int], str]:
        """Where each value of a grid-addressed axis sits."""

    @abstractmethod
    def reveal(self, table: RecordTableBrowser, file_path: str | Path) -> bool:
        """Select the table row a file path names."""

    @abstractmethod
    def view(
        self,
        batch: ViewerBatch,
        config: StreamingConfig,
        status: Callable[[str], None],
        failed: Callable[[str], None],
    ) -> None:
        """Send a batch to the viewer a streaming config names. Blocks until sent."""


class NoDataset(BrowsedDataset):
    """Nothing is loaded: no files, and a viewer config that belongs to no scope."""

    def labelled(self, column_key: str, raw: str) -> LabelledValue:
        return LabelledValue(column_key, raw)

    def config_state(self, config: object) -> ObjectState:
        return ObjectState(object_instance=config)

    def release_state(self, state: ObjectState) -> None:
        """An unscoped state was never registered."""

    def records(self) -> tuple[PlateFileRecord, ...]:
        return ()

    def viewer_ports(self, ports_per_type: int) -> list[int]:
        from openhcs.core.streaming_config_factory import get_all_streaming_ports

        return get_all_streaming_ports(num_ports_per_type=ports_per_type)

    def grid_positions(
        self, axis: type[Axis], values: set[str]
    ) -> dict[tuple[int, int], str]:
        return {}

    def reveal(self, table: RecordTableBrowser, file_path: str | Path) -> bool:
        return table.reveal_path(file_path)

    def view(self, batch, config, status, failed) -> None:
        raise RuntimeError("No dataset is loaded; there is nothing to view.")


class OrchestratorDataset(BrowsedDataset):
    """A dataset opened by an orchestrator.

    ``scope_parent`` is the ObjectState scope the browser's viewer config
    lives under (the dataset itself, or the window that embeds the browser).
    """

    def __init__(self, orchestrator, scope_parent: str) -> None:
        self.orchestrator = orchestrator
        self.scope_parent = scope_parent

    @classmethod
    def scoped_to_dataset(cls, orchestrator) -> OrchestratorDataset:
        return cls(orchestrator, str(orchestrator.dataset_root))

    @cached_property
    def streaming(self):
        from openhcs.core.viewer_streaming_service import StreamingService

        return StreamingService(
            filemanager=self.orchestrator.filemanager,
            microscope_handler=self.orchestrator.microscope_handler,
            plate_path=self.orchestrator.dataset_root,
            transport_config=self.orchestrator.transport_config,
        )

    def labelled(self, column_key: str, raw: str) -> LabelledValue:
        family = AxisFamily.active()
        if column_key not in family.names():
            return LabelledValue(column_key, raw)
        axis = family.named(column_key)
        try:
            label = self.orchestrator.metadata_cache.get_component_metadata(axis, raw)
        except Exception:
            logger.warning("Could not read the label of %s %s", column_key, raw, exc_info=True)
            return LabelledValue(column_key, raw)
        if not label or label == "None":
            return LabelledValue(column_key, raw)
        return LabelledValue(column_key, raw, label=label, source=axis)

    def config_state(self, config: object) -> ObjectState:
        state = ObjectState(
            object_instance=config,
            scope_id=ScopeKey(self.scope_parent).child(OpenHCSUiWindowId.image_browser),
            parent_state=ObjectStateRegistry.get_by_scope(str(self.orchestrator.dataset_root)),
        )
        ObjectStateRegistry.register(state, _skip_snapshot=True)
        return state

    def release_state(self, state: ObjectState) -> None:
        ObjectStateRegistry.unregister(state, _skip_snapshot=True)

    def records(self) -> tuple[PlateFileRecord, ...]:
        return PlateFileInventory.from_orchestrator(
            self.orchestrator, all_subdirs=True
        ).file_records()

    def viewer_ports(self, ports_per_type: int) -> list[int]:
        from openhcs.core.streaming_config_factory import get_all_streaming_ports

        return get_all_streaming_ports(
            config=self.orchestrator.pipeline_config,
            num_ports_per_type=ports_per_type,
        )

    def grid_positions(
        self, axis: type[Axis], values: set[str]
    ) -> dict[tuple[int, int], str]:
        # The dataset's filename parser spells each value's row and column; the
        # axis places those labels on the grid.
        parser = self.orchestrator.microscope_handler.parser
        return {
            axis.grid_position(*parser.extract_component_coordinates(value)): value
            for value in values
        }

    def reveal(self, table: RecordTableBrowser, file_path: str | Path) -> bool:
        return table.reveal_path(file_path, root=self.orchestrator.dataset_root)

    def view(self, batch, config, status, failed) -> None:
        from openhcs.core.viewer_streaming_service import (
            ImageStreamingRequest,
            RoiStreamingRequest,
        )

        viewer = self.orchestrator.get_or_create_visualizer(config)
        if batch.roi_paths:
            self.streaming.stream_rois(
                RoiStreamingRequest(
                    viewer=viewer,
                    config=config,
                    status_callback=status,
                    error_callback=failed,
                    roi_filenames=tuple(batch.roi_paths),
                )
            )
        if batch.image_paths:
            self.streaming.stream_images(
                ImageStreamingRequest(
                    viewer=viewer,
                    config=config,
                    status_callback=status,
                    error_callback=failed,
                    filenames=tuple(batch.image_paths),
                    read_backend=self.orchestrator.microscope_handler.get_primary_backend(
                        Path(self.orchestrator.dataset_root),
                        self.orchestrator.filemanager,
                    ),
                )
            )


# --- The widget -------------------------------------------------------------


@dataclass(frozen=True)
class AxisGrid:
    """A grid-addressed axis shown as a detachable grid joined to its table column."""

    axis: type[Axis]
    panel: DetachablePanel
    link: GridColumnFilterLink

    def offer_cells(self, dataset: BrowsedDataset) -> None:
        self.link.offer_cells(dataset.grid_positions(self.axis, self.link.column_values()))


class ImageBrowserWidget(QWidget):
    """Shows a dataset's image and result files and sends selections to viewers."""

    _stream_status = pyqtSignal(str)
    _stream_failed = pyqtSignal(str, str)

    def __init__(
        self,
        dataset: BrowsedDataset,
        *,
        color_scheme: ColorScheme,
        zmq_config: OpenHCSZMQConfig,
        progress_config: ProgressUIConfig,
        parent=None,
    ):
        super().__init__(parent)
        self.dataset = dataset
        self.color_scheme = color_scheme
        self._zmq_config = zmq_config
        self._progress_config = progress_config
        self.state = dataset.config_state(ImageBrowserConfig())

        self.table = RecordTableBrowser(
            color_scheme=color_scheme,
            value_labels=ValueLabels(dataset),
            item_noun="files",
            parent=self,
        )
        self.folder_tree = FolderTreeWidget(
            color_scheme, companion_suffixes=(ANALYSIS_RESULTS_DIR_SUFFIX,)
        )
        self.table.add_row_filter(FolderRowFilter(self.folder_tree))
        self.table.set_column_filter_context_widget(self.folder_tree)
        self.folder_tree.folder_changed.connect(lambda _folder: self.table.apply_row_filters())
        self.table.item_double_clicked.connect(lambda _key, file: file.open(self))
        self.table.items_selected.connect(
            lambda keys: self.viewer_tabs.set_target_available(bool(keys))
        )

        self.refresh_button = QPushButton("Refresh")
        self.refresh_button.setStyleSheet(color_scheme.styles.generate_button_style())
        self.refresh_button.clicked.connect(self.load_files)
        self.info_label = QLabel()
        self.info_label.setStyleSheet(
            f"color: {color_scheme.to_hex(color_scheme.text_disabled)};"
        )

        self.middle_splitter = QSplitter(Qt.Orientation.Vertical)
        self.middle_splitter.addWidget(self.table)
        self.grids = tuple(
            self._grid_for(axis, index)
            for index, axis in enumerate(AxisFamily.active().with_role(GridAddressed))
        )
        self.middle_splitter.setSizes([*(150 for _grid in self.grids), 350])

        self.main_splitter = QSplitter(Qt.Orientation.Horizontal)
        self.main_splitter.addWidget(self.middle_splitter)
        self.main_splitter.addWidget(self._build_viewer_panel())
        self.main_splitter.setSizes([2000, 400])

        header = QHBoxLayout()
        header.setSpacing(10)
        header.addWidget(self.table.search_input, 1)
        for grid in self.grids:
            header.addWidget(grid.panel.toggle_button)
        header.addWidget(self.refresh_button)
        header.addWidget(self.info_label)

        layout = QVBoxLayout(self)
        layout.setContentsMargins(5, 5, 5, 5)
        layout.setSpacing(5)
        layout.addLayout(header)
        layout.addWidget(self.main_splitter, 1)

        self._stream_status.connect(self.info_label.setText)
        self._stream_failed.connect(self._show_streaming_error)
        QTimer.singleShot(0, self.load_files)

    def _grid_for(self, axis: type[Axis], index: int) -> AxisGrid:
        selector = GridSelectorWidget(
            addressing=GridAxisAddressing(axis),
            title=f"{axis.label} Grid",
            cell_noun=f"{axis.label.lower()}s",
            color_scheme=self.color_scheme,
            parent=self,
        )
        panel = DetachablePanel(
            selector, self.middle_splitter, index, f"{axis.label} Grid", self.color_scheme
        )
        grid = AxisGrid(axis, panel, GridColumnFilterLink(selector, self.table, axis.name, self))
        selector.detach_requested.connect(panel.detach)
        panel.shown.connect(lambda: grid.offer_cells(self.dataset))
        return grid

    def _build_viewer_panel(self) -> QWidget:
        """Viewer config tabs with their "view in" buttons, above the viewer instances."""
        from openhcs.pyqt_gui.widgets.shared.zmq_server_manager import (
            ZMQServerManagerWidget,
        )

        self.viewer_tabs = ConfigActionTabs(self.state, viewer_actions(), self.color_scheme)
        self.viewer_tabs.action_requested.connect(
            lambda action: self.view_in(action, self.selected_files())
        )
        self.viewer_tabs.set_target_available(bool(self.table.get_selected_keys()))
        self.zmq_manager = ZMQServerManagerWidget(
            ports_to_scan=self.dataset.viewer_ports(self._zmq_config.ports_per_server_type),
            title="Viewer Instances",
            color_scheme=self.color_scheme,
            config=self._zmq_config,
            progress_config=self._progress_config,
            parent=self,
        )
        splitter = QSplitter(Qt.Orientation.Vertical)
        splitter.setChildrenCollapsible(True)
        splitter.addWidget(self.viewer_tabs)
        splitter.addWidget(self.zmq_manager)
        splitter.setSizes([350, 150])
        splitter.setMinimumWidth(360)
        return splitter

    # --- configuration pushed by the owning window ---

    def set_zmq_config(self, config: OpenHCSZMQConfig) -> None:
        """Use the resolved process transport config for viewer discovery."""
        self._zmq_config = config
        self.zmq_manager.set_zmq_config(
            config, self.dataset.viewer_ports(config.ports_per_server_type)
        )

    def set_progress_config(self, config: ProgressUIConfig) -> None:
        """Use the resolved progress refresh configuration."""
        self._progress_config = config
        self.zmq_manager.set_progress_config(config)

    def set_ui_config(
        self,
        *,
        zmq_config: OpenHCSZMQConfig,
        progress_config: ProgressUIConfig,
    ) -> None:
        """Apply the process-owned transport and progress configuration."""
        self.set_zmq_config(zmq_config)
        self.set_progress_config(progress_config)

    # --- the dataset ---

    def set_dataset(self, dataset: BrowsedDataset) -> None:
        """Browse another dataset: its own viewer config, viewer ports and files."""
        self.dataset.release_state(self.state)
        self.dataset = dataset
        self.state = dataset.config_state(ImageBrowserConfig())
        self.table.value_labels.source = dataset

        previous_panel = self.main_splitter.widget(1)
        previous_manager = self.zmq_manager
        self.main_splitter.replaceWidget(1, self._build_viewer_panel())
        previous_manager.cleanup()
        previous_panel.deleteLater()
        self.load_files()

    def load_files(self) -> None:
        """Read the dataset's file records into the table, tree and grids."""
        self.table.value_labels.clear()
        kinds = BrowsedFile.__subclasses__()
        try:
            rows = sorted(
                (row for record in self.dataset.records() for row in BrowsedFile.of(record)),
                key=lambda row: kinds.index(type(row)),
            )
        except Exception as error:
            logger.error("Failed to load files: %s", error, exc_info=True)
            QMessageBox.warning(self, "Error", f"Failed to load files: {error}")
            rows = []
        files = {row.key: row for row in rows}

        self.table.set_columns(file_columns({key for row in rows for key in row}))
        self.folder_tree.set_keys(files)
        self.table.set_items(files)
        for grid in self.grids:
            if grid.panel.is_shown:
                grid.offer_cells(self.dataset)

        counts = Counter(type(row) for row in rows)
        summary = ", ".join(f"{counts[kind]} {kind.kind_noun}" for kind in kinds)
        self.info_label.setText(f"{len(files)} files loaded ({summary})")

    def focus_file_by_path(self, file_path: str | Path) -> bool:
        """Select the row of a file, loading the files first when none are."""
        if not self.table.all_items:
            self.load_files()
        return self.dataset.reveal(self.table, file_path)

    def cleanup(self) -> None:
        """Release the viewer browser and the viewer-config state."""
        self.zmq_manager.cleanup()
        self.dataset.release_state(self.state)
        self.dataset = NoDataset()

    # --- sending files to viewers ---

    def selected_files(self) -> tuple[BrowsedFile, ...]:
        return tuple(self.table.all_items[key] for key in self.table.get_selected_keys())

    def view_in_enabled_viewers(self, files: tuple[BrowsedFile, ...], noun: str) -> None:
        """Send the files to every viewer whose config is switched on."""
        enabled = self.viewer_tabs.enabled_actions()
        if not enabled:
            QMessageBox.information(
                self,
                "No Viewer Enabled",
                f"Please enable at least one viewer streaming to view {noun}.",
            )
        for action in enabled:
            self.view_in(action, files)

    def view_in(self, action: ConfigAction, files: tuple[BrowsedFile, ...]) -> None:
        """Send the files to one viewer as a batch, off the UI thread."""
        batch = ViewerBatch()
        for file in files:
            file.add_to(batch)
        if not (batch.image_paths or batch.roi_paths):
            return
        # The resolved config carries inherited values; its viewer family names the viewer.
        config = self.state.get_resolved_value(action.field_name)
        viewer_name = config.viewer_family.display_name
        dataset = self.dataset

        def send() -> None:
            try:
                dataset.view(
                    batch,
                    config,
                    self._stream_status.emit,
                    lambda error: self._stream_failed.emit(viewer_name, str(error)),
                )
            except Exception as error:
                logger.error("Failed to stream to %s: %s", viewer_name, error, exc_info=True)
                self._stream_failed.emit(viewer_name, str(error))

        spawn_thread_with_context(send, name=f"view_{action.field_name}")

    def _show_streaming_error(self, viewer_name: str, message: str) -> None:
        QMessageBox.warning(
            self, "Streaming Error", f"Failed to stream to {viewer_name}: {message}"
        )
