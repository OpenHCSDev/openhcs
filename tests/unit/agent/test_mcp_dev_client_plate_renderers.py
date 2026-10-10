"""Plate renderer family over typed DTO fixtures."""

from __future__ import annotations
from openhcs.agent.dto.session import DatasetRowState

import sys
from dataclasses import replace

import pytest
from python_introspect import to_jsonable
from zmqruntime.config import TransportMode

from openhcs.agent.capabilities import agent_capabilities
from openhcs.agent.dto.common import SCHEMA_VERSION, AgentError, AgentWarning
from openhcs.agent.dto.execution_connection import ExecutionConnectionSpec
from openhcs.agent.dto.plate import (
    PlateFileQueryRecordSummary,
    PlateFileQueryResult,
    PlateFileStreamResult,
    PlateInspectionComponentSummary,
    PlateInspectionComponentValue,
    PlateInspectionHandlerCandidate,
    PlateInspectionImageFileSummary,
    PlateInspectionImageRecordSummary,
    PlateInspectionIssueCode,
    PlateInspectionResultFilePreview,
    PlateInspectionResultFileRecordSummary,
    PlateInspectionResultFileSummary,
    PlateInspectionStatus,
    PlateInspectionValueSource,
    PlatePathInspectionResult,
    SelectedPlateFileQueryResult,
    SelectedPlateFileQueryTarget,
    SelectedPlateFileStreamResult,
    SelectedPlateImageInspectionResult,
    SelectedPlateImageSampleResult,
    SyntheticPlateGenerationResult,
)
from openhcs.core.plate_file_inventory import PlateFileKind
from openhcs.core.streaming_config_declarations import ViewerType
from openhcs.core.synthetic_plate_generation import SyntheticPlateFormat
from openhcs.mcp.dev_client_core import (
    McpDevServerSpec,
    McpDevToolBatchResponse,
    McpDevToolResult,
)
from openhcs.mcp.dev_client_rendering import McpDevOutputRenderer
from openhcs.mcp.dev_client_renderers import plate as plate_renderers

CAPABILITY = {
    SyntheticPlateGenerationResult: agent_capabilities.generate_synthetic_plate,
    PlatePathInspectionResult: agent_capabilities.inspect_plate_path,
    PlateFileQueryResult: agent_capabilities.query_plate_files,
    PlateFileStreamResult: agent_capabilities.stream_plate_files_to_viewer,
    SelectedPlateImageInspectionResult: agent_capabilities.ui_inspect_selected_plate_images,
    SelectedPlateFileQueryResult: agent_capabilities.ui_query_selected_plate_files,
    SelectedPlateImageSampleResult: agent_capabilities.ui_sample_selected_plate_image,
    SelectedPlateFileStreamResult: agent_capabilities.ui_stream_selected_plate_files_to_viewer,
}


def render(value) -> str:
    response = McpDevToolBatchResponse.from_results(
        McpDevServerSpec(sys.executable),
        (McpDevToolResult(CAPABILITY[type(value)].name, False, (value,)),),
    )
    renderer = McpDevOutputRenderer.for_output_contract(type(value))
    return renderer.render(response)


def row(**changes) -> DatasetRowState:
    return replace(
        DatasetRowState(
            scope_id="/plates/a", name="plate-a", root="/plates/a",
            pipeline_path=None, selected=True, initialized=True, compiled=False,
            init_pending=False, compile_pending=False, execution_active=False,
            status_prefix="", orchestrator_state=None, execution_id=None,
            terminal_status=None, runtime_state=None, runtime_percent=None,
            queue_position=None,
        ),
        **changes,
    )


def inspection(**changes) -> PlatePathInspectionResult:
    return replace(
        PlatePathInspectionResult(
            schema_version=SCHEMA_VERSION,
            plate_path="/plates/a",
            requested_source_format="auto",
            status=PlateInspectionStatus.OK,
            detected_source_format="imagexpress",
            handler_class="ImageXpressHandler",
            grid_dimensions=(2, 3),
            image_files=PlateInspectionImageFileSummary(
                count=2,
                sampled_records=(
                    PlateInspectionImageRecordSummary(
                        "A01_w1.tif", "/plates/a/A01_w1.tif", "/src/A01_w1.tif",
                        {"modified": "2026-01-01", "size": "1 KB"},
                    ),
                    PlateInspectionImageRecordSummary(
                        "A01_w2.tif", "/plates/a/A01_w2.tif", "A01_w2.tif",
                        {"modified": "2026-01-02"},
                    ),
                ),
            ),
            result_files=PlateInspectionResultFileSummary(
                count=1,
                scanned_file_count=1,
                sampled_records=(
                    PlateInspectionResultFileRecordSummary(
                        "results/counts.csv", "/plates/a/results/counts.csv", "CSV",
                        preview=PlateInspectionResultFilePreview(
                            csv_columns=("well", "count"),
                            csv_rows=({"well": "A01", "count": "11"},),
                        ),
                    ),
                ),
            ),
            components=(
                PlateInspectionComponentSummary(
                    "well", PlateInspectionValueSource.METADATA, 1,
                    (PlateInspectionComponentValue("A01"),),
                ),
                PlateInspectionComponentSummary(
                    "channel", PlateInspectionValueSource.PARSED_FILENAMES, 2,
                    (PlateInspectionComponentValue("1", "DAPI"),
                     PlateInspectionComponentValue("2")),
                ),
            ),
            format_specific_handler_candidates=(
                PlateInspectionHandlerCandidate(
                    "opera_phenix", "OperaPhenixHandler", "OperaPhenixParser",
                    "Images", 3, 2, False, True, False,
                ),
            ),
            source_diagnostics=({"diagnostic_type": "scene", "message": "two scenes"},),
            warnings=(AgentWarning("plate_parse_failures", "some names unparsed"),),
        ),
        **changes,
    )


def query(**changes) -> PlateFileQueryResult:
    return replace(
        PlateFileQueryResult(
            schema_version=SCHEMA_VERSION,
            plate_path="/plates/a",
            requested_source_format="auto",
            detected_source_format="imagexpress",
            total_count=3, returned_count=2, offset=0, limit=2, truncated_count=1,
            records=(
                PlateFileQueryRecordSummary(
                    PlateFileKind.IMAGE, "A01_w1.tif", {"modified": "2026-02-01"},
                    source_path="/src/A01_w1.tif",
                ),
                PlateFileQueryRecordSummary(
                    PlateFileKind.RESULT, "results/summary.csv", {"modified": "2026-01-01"},
                    relative_path="results/summary.csv",
                    full_path="/plates/a_out/results/summary.csv",
                    file_format="CSV",
                    preview=PlateInspectionResultFilePreview(
                        csv_columns=("well", "notes"),
                        csv_rows=tuple(
                            {"well": f"A0{index}", "notes": "line\nbreak"}
                            for index in range(5)
                        ),
                    ),
                ),
            ),
        ),
        **changes,
    )


def stream(**changes) -> PlateFileStreamResult:
    return replace(
        PlateFileStreamResult(
            schema_version=SCHEMA_VERSION,
            plate_path="/plates/a_out",
            requested_source_format="auto",
            viewer_type=ViewerType.NAPARI,
            viewer_config_key="napari_streaming_config",
            connection=ExecutionConnectionSpec(port=5555, transport_mode=TransportMode.IPC),
            requested_paths=("a.tif", "a.roi.zip"),
            streamed_image_paths=tuple(f"/src/{index}.tif" for index in range(10)),
            streamed_roi_paths=("/plates/a_out/a.roi.zip",),
            skipped_records=(PlateFileQueryRecordSummary(PlateFileKind.IMAGE, "missing.tif"),),
            status_messages=("streamed 11 files",),
        ),
        **changes,
    )


def test_every_plate_renderer_presents_its_declared_dto_and_failure():
    """One family check: each renderer is registered for its DTO and none reads a dict."""
    fixtures = (
        SyntheticPlateGenerationResult(
            schema_version=SCHEMA_VERSION, output_dir="/plates/synthetic",
            requested_format=SyntheticPlateFormat.IMAGE_XPRESS,
            grid_size=(2, 2), wells=("A01", "B02"), sampled_image_files=("a.tif",),
        ),
        inspection(),
        query(),
        stream(),
        SelectedPlateImageInspectionResult(
            schema_version=SCHEMA_VERSION, selected_plate=to_jsonable(row()),
            inspection=inspection(),
        ),
        SelectedPlateFileQueryResult(
            schema_version=SCHEMA_VERSION, selected_plate=to_jsonable(row()), query=query(),
        ),
        SelectedPlateImageSampleResult(
            schema_version=SCHEMA_VERSION, selected_plate=to_jsonable(row()),
        ),
        SelectedPlateFileStreamResult(
            schema_version=SCHEMA_VERSION, selected_plate=to_jsonable(row()), stream=stream(),
        ),
    )
    for value in fixtures:
        renderer = McpDevOutputRenderer.for_output_contract(type(value))
        assert renderer.__module__ == plate_renderers.__name__
        assert "<none>" not in render(value).splitlines()[0]
        failed = replace(value, errors=(AgentError("plate_failure", "cause"),))
        failed_text = render(failed)
        assert failed_text.count("plate_failure") == 1
        assert "failed" in failed_text.splitlines()[0]
        tool_failure = McpDevToolBatchResponse.from_results(
            McpDevServerSpec(sys.executable),
            (McpDevToolResult(CAPABILITY[type(value)].name, True, ()),),
        )
        assert renderer.render(tool_failure).splitlines()[0] == renderer.unavailable_summary


def test_inspection_presents_axes_records_previews_and_next_sample():
    text = render(inspection())
    assert "Status: ok confidence=none microscope=imagexpress" in text
    assert "Geometry: grid=2x3 pixel_size=<none>" in text
    assert "Axis sizes: well=1 site=<unknown> channel=2" in text
    assert "profile=unknown-site,multi-channel,unknown-z_index,unknown-timepoint" in text
    assert "Metadata sources: well=metadata, channel=parsed_filenames" in text
    assert "- channel: count=2 source=parsed_filenames values=1 (DAPI), 2 truncated=0" in text
    assert "  - opera_phenix parser=OperaPhenixParser recognized=2/3 root=Images" in text
    assert "- scene: two scenes" in text
    assert "Sampled artifacts modified: mixed latest=2026-01-02 earliest=2026-01-01" in text
    assert "- A01_w1.tif -> /src/A01_w1.tif modified=2026-01-01 size=1 KB" in text
    assert "- A01_w2.tif modified=2026-01-02" in text
    # The most recently modified record is the one suggested for sampling.
    assert (
        "Next: sample-plate-image /plates/a A01_w2.tif "
        "--height 8 --width 8 --no-array-values"
    ) in text
    assert "- results/counts.csv type=CSV\n  csv columns: well, count\n  csv row: well=A01, count=11" in text
    assert text.count("plate_parse_failures") == 1
    assert text.index("Warnings:") > text.index("Result records:")


def test_query_presents_previews_pages_staleness_roots_and_result_hint():
    text = render(query())
    assert "Result: returned=2 total=3 offset=0 limit=2 truncated=1" in text
    assert "- image A01_w1.tif -> /src/A01_w1.tif modified=2026-02-01" in text
    assert "- result results/summary.csv type=CSV -> /plates/a_out/results/summary.csv" in text
    assert "  csv row: well=A00; omitted wide cells: notes" in text
    assert "  csv preview: showing 3/5 rows; 2 more in payload" in text
    assert "Next page: rerun with --offset 2 --limit 2" in text
    assert "Potential stale results: 1 result artifact(s) are older" in text
    assert "Record file roots: /plates/a_out (differs from query root" in text
    assert "--kind result --include-previews" not in text
    hinted = render(
        query(
            records=(),
            truncated_count=0,
            warnings=(
                AgentWarning(PlateInspectionIssueCode.RESULT_FILES_AVAILABLE.value, "results"),
            ),
        )
    )
    assert "Records: <none>" in hinted
    assert "Next page" not in hinted
    assert (
        "Next: query-plate-files /plates/a --source-format imagexpress "
        "--kind result --include-previews"
    ) in hinted


def test_stream_bounds_paths_and_suggests_viewer_commands():
    text = render(stream())
    assert "Viewer: napari config=napari_streaming_config host=localhost port=5555 transport=ipc persistent=True" in text
    assert "Files: requested=2 resolved=0 images=10 rois=1 skipped=1" in text
    assert "- ... 2 more" in text
    assert "Skipped:\n- image missing.tif" in text
    assert "Status:\n- streamed 11 files" in text
    assert (
        "Next:\n- validate-viewer --port 5555 --transport-mode ipc --require-nonzero-payloads\n"
        "- viewer-state --port 5555 --transport-mode ipc\n"
        "- viewer-rois --port 5555 --transport-mode ipc --limit 5"
    ) in text
    assert "Next:" not in render(stream(connection=ExecutionConnectionSpec()))


@pytest.mark.parametrize(
    "target,command",
    [
        (SelectedPlateFileQueryTarget.SELECTED, "Next: selected-plate-sample A01_w2.tif"),
        (SelectedPlateFileQueryTarget.OUTPUT, "Next: selected-plate-sample --target output A01_w2.tif"),
    ],
)
def test_selected_plate_images_render_the_nested_inspection(target, command):
    text = render(
        SelectedPlateImageInspectionResult(
            schema_version=SCHEMA_VERSION, selected_plate=to_jsonable(row()),
            target=target, inspection=inspection(),
        )
    )
    assert text.startswith(f"Selected plate: plate-a root=/plates/a target={target.value}\nPlate: /plates/a")
    assert command in text
    assert "sample-plate-image" not in text
    assert text.count("plate_parse_failures") == 1


def test_selected_plate_files_hint_related_output_only_for_an_empty_selected_query():
    selected_row = to_jsonable(row(output_root="/plates/a_out"))
    empty = query(total_count=0, returned_count=0, truncated_count=0, records=())
    text = render(
        SelectedPlateFileQueryResult(
            schema_version=SCHEMA_VERSION, selected_plate=selected_row, query=empty,
        )
    )
    assert "Plate file query: /plates/a" in text
    assert "Related output: /plates/a_out\nNext: selected-plate-files --target output --kind result" in text
    assert "Related output" not in render(
        SelectedPlateFileQueryResult(
            schema_version=SCHEMA_VERSION, selected_plate=selected_row, query=query(),
        )
    )
    assert "Query: <none>" in render(
        SelectedPlateFileQueryResult(schema_version=SCHEMA_VERSION, selected_plate=selected_row)
    )


def test_selected_plate_sample_and_stream_keep_target_context_on_failure():
    error = AgentError("ui_selected_plate_count_not_one", "two plates selected")
    sample_text = render(
        SelectedPlateImageSampleResult(
            schema_version=SCHEMA_VERSION, selected_plate=to_jsonable(row()),
            target=SelectedPlateFileQueryTarget.OUTPUT, image_path="a.tif", errors=(error,),
        )
    )
    assert sample_text.startswith(
        "Selected plate sample: failed\n"
        "Selected plate: plate-a root=/plates/a target=output\n"
        "Selected image: a.tif auto=False"
    )
    stream_text = render(
        SelectedPlateFileStreamResult(schema_version=SCHEMA_VERSION, errors=(error,))
    )
    assert stream_text.startswith(
        "Selected plate stream: failed\nSelected plate: <none> root=<none> target=selected"
    )
    assert stream_text.count("two plates selected") == 1
    nested = render(
        SelectedPlateFileStreamResult(
            schema_version=SCHEMA_VERSION, selected_plate=to_jsonable(row()),
            target=SelectedPlateFileQueryTarget.OUTPUT,
            stream=stream(warnings=(AgentWarning("viewer_slow", "slow start"),)),
        )
    )
    assert "Plate file stream: /plates/a_out" in nested
    assert nested.count("viewer_slow") == 1


def test_synthetic_generation_suggests_inspection_and_query():
    text = render(
        SyntheticPlateGenerationResult(
            schema_version=SCHEMA_VERSION, output_dir="/plates/synthetic",
            requested_format=SyntheticPlateFormat.IMAGE_XPRESS,
            grid_size=(2, 2), tile_size=(64, 64), overlap_percent=10, wells=("A01", "B02"),
            wavelengths=2, image_count=8, sampled_image_files=tuple(f"{i}.tif" for i in range(14)),
            truncated_image_count=0,
        )
    )
    assert "Geometry: grid=2x2 tile=64x64 overlap=10% stage_error_px=0" in text
    assert "Content: wells=A01,B02 channels=2" in text
    assert "Files: images=8 sampled=14 truncated=0" in text
    assert "- 11.tif" in text and "- 12.tif" not in text
    assert text.endswith(
        "Next: inspect-plate /plates/synthetic\nNext: query-plate-files /plates/synthetic --limit 10"
    )
