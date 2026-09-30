from __future__ import annotations

import json
import pytest
from dataclasses import dataclass
from pathlib import Path
from types import SimpleNamespace

from polystore.virtual_workspace import SourcePixelRef

from openhcs.constants.constants import AllComponents
from openhcs.core.virtual_workspace_metadata import FIELDS
from openhcs.core.source_metadata import SourceVoxelSpacing, SourceVoxelSpacingUnit
from openhcs.core.viewer_streaming_service import ViewerStreamingSource
from openhcs.microscopes.opera_phenix import OperaPhenixHandler
from openhcs.core.source_workspace_projection import (
    VirtualWorkspaceSourceProjection,
)


def test_virtual_workspace_metadata_records_parser_owned_axis_values(
    tmp_path: Path,
    monkeypatch,
) -> None:
    handler = OperaPhenixHandler(SimpleNamespace())
    monkeypatch.setattr(
        handler.metadata_handler,
        "get_grid_dimensions",
        lambda plate_path: (3, 3),
    )
    monkeypatch.setattr(
        handler.metadata_handler,
        "get_pixel_size",
        lambda plate_path: 1.0,
    )
    virtual_a = "Images/r01c01f001p001-ch1sk1fk1fl1.tiff"
    virtual_b = "Images/r02c03f001p001-ch1sk1fk1fl1.tiff"

    handler.save_virtual_workspace_metadata(
        tmp_path,
        {
            virtual_a: SourcePixelRef("disk", "Images/source-a.tiff"),
            virtual_b: SourcePixelRef("disk", "Images/source-b.tiff"),
        },
    )

    metadata = json.loads(
        (tmp_path / "openhcs_metadata.json").read_text(encoding="utf-8")
    )
    source_metadata = metadata[FIELDS.SUBDIRECTORIES]["Images"][FIELDS.SOURCE_METADATA]
    assert source_metadata[virtual_a][AllComponents.WELL.value] == "R01C01"
    assert source_metadata[virtual_b][AllComponents.WELL.value] == "R02C03"

    projection = VirtualWorkspaceSourceProjection.from_openhcs_metadata(
        tmp_path,
        metadata,
    )
    assert projection.pipeline_start_files(axis_id="R01C01") == (
        str(tmp_path / virtual_a),
    )
    assert projection.pipeline_start_files(axis_id="R02C03") == (
        str(tmp_path / virtual_b),
    )


@pytest.mark.parametrize(
    "spacing",
    [
        SourceVoxelSpacing((0.65, 0.65)),
        SourceVoxelSpacing((0.65, 0.8)),
        SourceVoxelSpacing((1.0, 2.0), SourceVoxelSpacingUnit.RELATIVE),
    ],
)
def test_acquisition_spacing_declaration_serves_publication_and_manual_viewer(
    spacing,
    tmp_path,
    monkeypatch,
):
    handler = OperaPhenixHandler(SimpleNamespace())
    monkeypatch.setattr(
        handler.metadata_handler, "get_grid_dimensions", lambda _path: (1, 1)
    )
    monkeypatch.setattr(handler.metadata_handler, "get_pixel_size", lambda _path: 1.0)
    monkeypatch.setattr(
        handler.metadata_handler, "source_voxel_spacing", lambda _path: spacing
    )
    virtual_path = "Images/r01c01f001p001-ch1sk1fk1fl1.tiff"
    handler.save_virtual_workspace_metadata(
        tmp_path,
        {virtual_path: SourcePixelRef("disk", "Images/source.tiff")},
    )
    document = json.loads((tmp_path / "openhcs_metadata.json").read_text())
    values = document[FIELDS.SUBDIRECTORIES]["Images"][FIELDS.SOURCE_METADATA][
        virtual_path
    ]
    assert SourceVoxelSpacing.from_source_metadata(values) == spacing
    source = ViewerStreamingSource(
        microscope_handler=handler,
        plate_path=tmp_path,
        filemanager=SimpleNamespace(),
    )
    assert source.plate_image_metadata().source_voxel_spacing == spacing


def _ingest_records(records: list[dict]) -> None:
    import typing

    import openhcs.core.source_projection as projection_module
    from openhcs.core.virtual_workspace_metadata import (
        VirtualWorkspaceSourceProjectionEntries,
    )

    calls = {"count": 0}
    original_get_type_hints = typing.get_type_hints

    def counting_get_type_hints(*args, **kwargs):
        calls["count"] += 1
        return original_get_type_hints(*args, **kwargs)

    original = projection_module.get_type_hints
    projection_module.get_type_hints = counting_get_type_hints
    try:
        VirtualWorkspaceSourceProjectionEntries.from_subdirectory(
            {"source_projection": records}
        )
    finally:
        projection_module.get_type_hints = original
    return calls["count"]


def test_projection_ingest_resolves_wire_field_once_for_many_records():
    """Wire-field derivation is a class-level fact, not per-record introspection."""

    records = [
        {
            "virtual_path": f"images/A0{index % 10}_s1_w1_z1_t1_{index}.tif",
            "address": {
                "well": "A01",
                "site": "1",
                "channel": "1",
                "z_index": "1",
                "timepoint": "1",
            },
            "ref": {
                "backend": "disk",
                "backend_address": f"images/{index}.tif",
                "source_axis_indices": [],
            },
            "projection_role": "primary_plane",
            "image_metadata": None,
        }
        for index in range(50)
    ]

    resolution_calls = _ingest_records(records)

    assert resolution_calls <= 1, (
        "Wire-field derivation must not run per record: "
        f"{resolution_calls} typing resolutions for {len(records)} records."
    )


class _MarkerA:
    pass


class _MarkerB:
    pass


@dataclass(frozen=True, slots=True)
class _TwoPayloadProjection:
    first: _MarkerA | None = None
    second: _MarkerB | None = None


def test_declared_optional_payload_field_is_type_parametric():
    from openhcs.core.source_projection import declared_optional_payload_field

    assert declared_optional_payload_field(_TwoPayloadProjection, _MarkerA) == "first"
    assert declared_optional_payload_field(_TwoPayloadProjection, _MarkerB) == "second"
    assert declared_optional_payload_field(_TwoPayloadProjection, _MarkerA) == "first"
