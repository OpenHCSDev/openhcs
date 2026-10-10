from __future__ import annotations

import json
import pytest
from dataclasses import dataclass, replace
from pathlib import Path
from types import SimpleNamespace

from polystore.virtual_workspace import SourcePixelRef

from openhcs.core.virtual_workspace_metadata import FIELDS
from openhcs.core.source_metadata import SourceVoxelSpacing, SourceVoxelSpacingUnit
from openhcs.core.viewer_streaming_service import ViewerStreamingSource
from openhcs.microscopes.opera_phenix import OperaPhenixHandler
from openhcs.core.source_workspace_projection import (
    VirtualWorkspaceSourceProjection,
)
from openhcs.domains.microscopy.axes import Microscopy


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
    assert source_metadata[virtual_a][Microscopy.Well.name] == "R01C01"
    assert source_metadata[virtual_b][Microscopy.Well.name] == "R02C03"

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


def test_compiler_source_queries_borrow_config_while_public_queries_stay_live(
    tmp_path, monkeypatch
):
    from unittest.mock import Mock
    from objectstate.lazy_factory import ensure_global_config_context
    from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
    from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
    from openhcs.core.source_bindings import (
        SourceBindingsConfig,
        LazySourceBindingsConfig,
        SourceFilterClause,
        SourceFilterMatchType,
        SourceFilterSubject,
    )

    source_handler = OperaPhenixHandler(SimpleNamespace())
    (tmp_path / "Images").mkdir()
    monkeypatch.setattr(
        source_handler.metadata_handler, "get_grid_dimensions", lambda _: (3, 3)
    )
    monkeypatch.setattr(source_handler.metadata_handler, "get_pixel_size", lambda _: 1.0)
    source_handler.save_virtual_workspace_metadata(
        tmp_path,
        {
            "Images/r01c01f001p001-ch1sk1fk1fl1.tiff": SourcePixelRef(
                "disk", "/source/source-a.tiff"
            ),
            "Images/r02c03f001p001-ch1sk1fk1fl1.tiff": SourcePixelRef(
                "disk", "/source/source-b.tiff"
            ),
        },
    )
    metadata_path = tmp_path / "openhcs_metadata.json"
    metadata_document = json.loads(metadata_path.read_text())
    subdirectory = metadata_document[FIELDS.SUBDIRECTORIES]["Images"]
    subdirectory[FIELDS.IMAGE_FILES] = list(subdirectory[FIELDS.WORKSPACE_MAPPING])
    metadata_path.write_text(json.dumps(metadata_document))
    source_a = SourceBindingsConfig(source_filters=(
        SourceFilterClause(
            SourceFilterSubject.FILE, SourceFilterMatchType.CONTAINS, "source-a"
        ),
    ))
    source_b = SourceBindingsConfig(source_filters=(
        SourceFilterClause(
            SourceFilterSubject.FILE, SourceFilterMatchType.CONTAINS, "source-b"
        ),
    ))
    held_config = GlobalPipelineConfig(source_bindings_config=source_a)
    ensure_global_config_context(GlobalPipelineConfig, held_config)
    owner = PipelineOrchestrator(
        tmp_path,
        pipeline_config=PipelineConfig(
            source_bindings_config=LazySourceBindingsConfig(
                source_filters=source_a.source_filters
            )
        ),
        resolved_config=held_config,
    )
    owner.initialize(resolved_config=held_config)
    live_config = Mock(wraps=owner.get_effective_config)
    monkeypatch.setattr(owner, "get_effective_config", live_config)

    assert owner.get_component_keys(
        Microscopy.Well, resolved_config=held_config
    ) == ["R01C01"]
    live_config.assert_not_called()
    owner.pipeline_config = replace(
        owner.pipeline_config,
        source_bindings_config=LazySourceBindingsConfig(
            source_filters=source_b.source_filters
        ),
    )
    owner.initialize()
    live_config.reset_mock()
    assert owner.get_component_keys(Microscopy.Well) == ["R02C03"]
    assert live_config.call_count == 1
    assert owner.get_component_keys(
        Microscopy.Well, resolved_config=held_config
    ) == ["R01C01"]
    assert live_config.call_count == 1


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


def test_workspace_registration_reuses_owner_and_refreshes_changed_mapping(tmp_path):
    import os
    from polystore.filemanager import FileManager
    from openhcs.constants import Backend
    from openhcs.core.virtual_workspace_metadata import METADATA_CONFIG
    from openhcs.core.dataset_sources.source import DatasetSource

    metadata_path = METADATA_CONFIG.metadata_path(tmp_path)
    document = {FIELDS.SUBDIRECTORIES: {".": {FIELDS.WORKSPACE_MAPPING: {
        "image.tif": SourcePixelRef("disk", "first.tif").to_workspace_mapping(),
    }}}}
    metadata_path.write_text(json.dumps(document))
    manager = FileManager({})
    DatasetSource._register_virtual_workspace_backend(tmp_path, manager)
    owner = manager.registry[Backend.VIRTUAL_WORKSPACE.value]
    alias = tmp_path / "plate-alias"
    alias.symlink_to(tmp_path, target_is_directory=True)
    DatasetSource._register_virtual_workspace_backend(alias, manager)
    assert manager.registry[Backend.VIRTUAL_WORKSPACE.value] is owner
    assert owner._resolve_ref("image.tif").backend_address == "first.tif"

    document[FIELDS.SUBDIRECTORIES]["."][FIELDS.WORKSPACE_MAPPING]["image.tif"] = (
        SourcePixelRef("disk", "second.tif").to_workspace_mapping()
    )
    prior_mtime = metadata_path.stat().st_mtime
    metadata_path.write_text(json.dumps(document))
    os.utime(metadata_path, (prior_mtime + 1, prior_mtime + 1))
    DatasetSource._register_virtual_workspace_backend(tmp_path, manager)
    assert manager.registry[Backend.VIRTUAL_WORKSPACE.value] is owner
    assert owner._resolve_ref("image.tif").backend_address == "second.tif"

    document[FIELDS.SUBDIRECTORIES]["."][FIELDS.WORKSPACE_MAPPING]["image.tif"] = {}
    metadata_path.write_text(json.dumps(document))
    os.utime(metadata_path, (prior_mtime + 2, prior_mtime + 2))
    with pytest.raises(ValueError, match="workspace mapping fields are invalid"):
        owner._resolve_ref("image.tif")


def test_workspace_registration_replaces_different_plate_or_metadata_contract(tmp_path):
    from dataclasses import replace
    from polystore.filemanager import FileManager
    from polystore.virtual_workspace import VirtualWorkspaceBackend
    from openhcs.constants import Backend
    from openhcs.core.virtual_workspace_metadata import METADATA_CONFIG
    from openhcs.core.dataset_sources.source import DatasetSource

    manager = FileManager({})
    owners = []
    for name in ("first", "second"):
        plate = tmp_path / name
        plate.mkdir()
        document = {FIELDS.SUBDIRECTORIES: {".": {FIELDS.WORKSPACE_MAPPING: {
            "image.tif": SourcePixelRef("disk", f"{name}.tif").to_workspace_mapping(),
        }}}}
        METADATA_CONFIG.metadata_path(plate).write_text(json.dumps(document))
        DatasetSource._register_virtual_workspace_backend(plate, manager)
        owner = manager.registry[Backend.VIRTUAL_WORKSPACE.value]
        assert owner._resolve_ref("image.tif").backend_address == f"{name}.tif"
        owners.append(owner)
    assert owners[0] is not owners[1]
    alternative = replace(METADATA_CONFIG, METADATA_FILENAME="alternative_metadata.json")
    alternative.metadata_path(plate).write_text(json.dumps(document))
    foreign_owner = VirtualWorkspaceBackend(plate, metadata_config=alternative)
    manager.register_backend(Backend.VIRTUAL_WORKSPACE.value, foreign_owner)
    DatasetSource._register_virtual_workspace_backend(plate, manager)
    assert manager.registry[Backend.VIRTUAL_WORKSPACE.value] is not foreign_owner
    assert manager.registry[Backend.VIRTUAL_WORKSPACE.value].metadata_config == METADATA_CONFIG
