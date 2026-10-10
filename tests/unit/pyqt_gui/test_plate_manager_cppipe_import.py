"""A folder of CellProfiler pipelines becomes one dataset row per pipeline."""

from __future__ import annotations

from pathlib import Path

from objectstate.object_state import ObjectStateRegistry
from PyQt6.QtCore import Qt

from openhcs.agent.dto.session import DatasetRootsRequest
from openhcs.authoring.session.datasets import dataset_scope_ids
from openhcs.authoring.session.operations.datasets import (
    AddDatasets,
    DeleteDatasets,
    EditDatasetConfig,
)
from openhcs.core.config import PipelineConfig
from openhcs.interop.cellprofiler.dataset_scope import CellProfilerPipelineScope
from tests.unit.pyqt_gui.session_harness import caller_session, session_gui


def _pipeline_folder(tmp_path: Path, name: str, *pipelines: str) -> tuple[Path, ...]:
    root = tmp_path / name
    root.mkdir()
    paths = []
    for pipeline in pipelines:
        path = root / pipeline
        path.write_text("Version:5", encoding="utf-8")
        paths.append(path)
    return (root, *paths)


def _scope(root: Path, pipeline: Path) -> str:
    return CellProfilerPipelineScope.scope_for(root, pipeline).scope_id


def test_multi_pipeline_folder_adds_one_logical_row_per_pipeline(tmp_path) -> None:
    root, first, second = _pipeline_folder(
        tmp_path, "plate", "first.cppipe", "second.cppipe"
    )
    with caller_session() as session:
        result = session.invoke(AddDatasets, DatasetRootsRequest(roots=(str(root),)))

        first_scope, second_scope = _scope(root, first), _scope(root, second)
        assert "::" not in first_scope and "::" not in second_scope
        assert result.target_scope_ids == (first_scope, second_scope)
        rows = {row.scope_id: row for row in session.dataset_rows()}
        assert sorted(rows) == sorted([first_scope, second_scope])
        assert rows[first_scope].name == "plate / first"
        assert rows[first_scope].pipeline_path == str(first)
        assert rows[second_scope].name == "plate / second"
        assert rows[second_scope].pipeline_path == str(second)
        for scope_id, pipeline in ((first_scope, first), (second_scope, second)):
            orchestrator = session.orchestrator(scope_id)
            assert orchestrator.plate_path == root
            assert orchestrator.selected_pipeline_path == pipeline
        assert session.current_scope_id == first_scope


def test_tutorial_final_pipeline_is_selected_and_shown_in_the_list(tmp_path) -> None:
    root, final, start = _pipeline_folder(
        tmp_path,
        "AdvancedSegmentation",
        "BBBC022_Analysis_Final.cppipe",
        "BBBC022_Analysis_Start.cppipe",
    )
    with session_gui() as gui:
        gui.session.invoke(AddDatasets, DatasetRootsRequest(roots=(str(root),)))
        gui.settle()

        final_scope = _scope(root, final)
        assert gui.session.dataset_scope_ids() == [_scope(root, start), final_scope]
        assert gui.session.current_scope_id == final_scope
        current_item = gui.plate_manager.item_list.currentItem()
        assert current_item is not None
        assert current_item.data(Qt.ItemDataRole.UserRole) == final_scope
        assert gui.pipeline_editor.current_plate == final_scope


def test_list_refresh_keeps_the_selection_without_reannouncing_it(tmp_path) -> None:
    root, _final = _pipeline_folder(
        tmp_path, "AdvancedSegmentation", "BBBC022_Analysis_Final.cppipe"
    )
    with session_gui() as gui:
        gui.session.invoke(AddDatasets, DatasetRootsRequest(roots=(str(root),)))
        gui.settle()
        emissions = []
        gui.plate_manager.plate_selected.connect(emissions.append)

        gui.plate_manager.update_item_list()
        gui.settle()

        assert emissions == []


def test_deleting_the_selected_pipeline_row_moves_both_widgets_to_the_rest(
    tmp_path,
) -> None:
    root, start, final = _pipeline_folder(
        tmp_path,
        "BeginnerSegmentation",
        "segmentation_start.cppipe",
        "segmentation_final.cppipe",
    )
    with session_gui() as gui:
        gui.session.invoke(AddDatasets, DatasetRootsRequest(roots=(str(root),)))
        gui.settle()
        start_scope, final_scope = _scope(root, start), _scope(root, final)
        assert gui.session.current_scope_id == final_scope
        assert gui.pipeline_editor.current_plate == final_scope
        emissions = []
        gui.plate_manager.plate_selected.connect(emissions.append)

        gui.plate_manager.handle_button_action(DeleteDatasets.operation_id)
        gui.settle()

        assert [row.scope_id for row in gui.plate_manager.plates] == [start_scope]
        assert gui.session.current_scope_id == start_scope
        assert gui.pipeline_editor.current_plate == start_scope
        assert emissions == [start_scope]
        assert ObjectStateRegistry.get_by_scope(final_scope) is None


def test_persisted_multi_pipeline_root_is_split_into_logical_rows(tmp_path) -> None:
    root, final, start = _pipeline_folder(
        tmp_path,
        "AdvancedSegmentation",
        "BBBC022_Analysis_Final.cppipe",
        "BBBC022_Analysis_Start.cppipe",
    )
    with caller_session(persisted_scope_ids=[str(root)]) as session:
        start_scope, final_scope = _scope(root, start), _scope(root, final)
        assert dataset_scope_ids() == [start_scope, final_scope]
        assert session.orchestrator(start_scope).selected_pipeline_path == start
        assert session.orchestrator(final_scope).selected_pipeline_path == final


def test_code_documents_naming_a_pipeline_scope_keep_its_import_request(
    tmp_path,
) -> None:
    root, pipeline = _pipeline_folder(
        tmp_path, "BeginnerSegmentation", "segmentation_final.cppipe"
    )
    scope_id = _scope(root, pipeline)
    with caller_session() as session:
        session.sync_datasets((scope_id,))

        orchestrator = session.orchestrator(scope_id)
        assert orchestrator.plate_path == root
        assert orchestrator.selected_pipeline_path == pipeline
        assert session.current_scope_id == scope_id


def test_config_window_edits_the_logical_pipeline_scope(tmp_path, monkeypatch) -> None:
    root, pipeline = _pipeline_folder(
        tmp_path, "AdvancedSegmentation", "BBBC022_Analysis_Final.cppipe"
    )
    scope_id = _scope(root, pipeline)
    captured = {}

    class FakeConfigWindow:
        def __init__(self, tabs, color_scheme=None, parent=None, scope_id=None):
            captured["tabs"] = tabs
            captured["scope_id"] = scope_id

        def show(self):
            captured["shown"] = True

        def raise_(self):
            pass

        def activateWindow(self):
            pass

    monkeypatch.setattr(
        "openhcs.pyqt_gui.widgets.plate_manager.ConfigWindow", FakeConfigWindow
    )
    with session_gui() as gui:
        gui.session.invoke(AddDatasets, DatasetRootsRequest(roots=(str(root),)))
        orchestrator = gui.session.orchestrator(scope_id)
        orchestrator._state = type(orchestrator.state).READY
        gui.session.refresh()
        gui.settle()
        emissions = []
        gui.plate_manager.orchestrator_config_changed.connect(
            lambda emitted_scope, config: emissions.append((emitted_scope, config))
        )

        gui.plate_manager.handle_button_action(EditDatasetConfig.operation_id)

        assert captured["shown"] is True
        assert captured["scope_id"] == scope_id
        assert captured["tabs"][0].state is ObjectStateRegistry.get_by_scope(scope_id)
        captured["tabs"][0].save_participant.apply(PipelineConfig(num_workers=5))
        gui.settle()

        assert (
            ObjectStateRegistry.get_by_scope(scope_id).get_saved_resolved_value(
                "num_workers"
            )
            == 5
        )
        assert ObjectStateRegistry.get_by_scope(str(root)) is None
        assert emissions[-1][0] == scope_id


def test_pipeline_row_preview_reads_the_logical_config_scope(tmp_path) -> None:
    root, pipeline = _pipeline_folder(
        tmp_path, "AdvancedSegmentation", "BBBC022_Analysis_Final.cppipe"
    )
    scope_id = _scope(root, pipeline)
    with session_gui() as gui:
        gui.session.invoke(AddDatasets, DatasetRootsRequest(roots=(str(root),)))
        gui.settle()
        (row,) = gui.plate_manager.plates

        rendered = gui.plate_manager._format_item_content(row, 0, None)

        preview_paths = {
            segment.field_path for segment in rendered.layout.preview_segments
        }
        assert "num_workers" in preview_paths
        assert "vfs_config.materialization_backend" in preview_paths
        assert rendered.layout.detail_line == scope_id
