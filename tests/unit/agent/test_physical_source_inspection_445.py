"""Real inspection/inventory/source-ref boundary; no Java or scientific input."""

import json
from dataclasses import replace
from pathlib import Path

import numpy as np
import pytest
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager

from openhcs.agent.dto.plate import (
    PlateFileQueryRequest,
    PlateImageSampleRequest,
    PlatePathInspectionRequest,
)
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.plate_inspection_service import (
    PlateInspectionFileManagerFactory,
    PlateInspectionService,
)
from openhcs.constants.constants import Backend
from openhcs.core.plate_image_inventory import PlateFileKind, PlateImageInventory
from openhcs.core.source_bindings import (
    MetadataSelector,
    NamedSourceBinding,
    SourceBindingsConfig,
    SourceSelector,
)
from openhcs.microscopes.bioformats import BioFormatsHandler
from openhcs.core.source_workspace_projection import VirtualWorkspaceSourceProjectionAuthority
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.microscopes.bioformats import BioFormatsMetadataHandler
from tests.unit.bioformats_fixture import write_bioformats_manifest_fixture


class DiskOnlyInspectionFileManagerFactory(PlateInspectionFileManagerFactory):
    """Declare only the real storage capability used by the engineering fixture."""

    def create(self) -> FileManager:
        return FileManager({Backend.DISK.value: DiskStorageBackend()})


class DeclaredInspectionMetadata(BioFormatsMetadataHandler):
    """Independent acquisition metadata hook; no generic consumer edit."""

    def source_dataset(self, plate_path):
        dataset = super().source_dataset(plate_path)
        return replace(
            dataset,
            candidates=tuple(
                replace(candidate, metadata={**candidate.metadata, "inspection_witness": "declared"})
                for candidate in dataset.candidates
            ),
        )


def _fixture(root: Path, channels: int):
    write_bioformats_manifest_fixture(root)
    stack = np.arange(channels * 8 * 8, dtype=np.uint16).reshape(1, 1, channels, 8, 8)
    np.save(root / "stack.npy", stack)
    manifest_path = root / "bioformats_spw.json"
    manifest = json.loads(manifest_path.read_text())
    image = manifest["images"][0]
    image["channel_names"] = [f"engineering-{channel}" for channel in range(1, channels + 1)]
    image["pixels"]["size_c"] = channels
    image["pixels"]["planes"] = [
        {"c": channel, "z": 1, "t": 1, "index": channel - 1}
        for channel in range(1, channels + 1)
    ]
    manifest_path.write_text(json.dumps(manifest))
    factory = DiskOnlyInspectionFileManagerFactory()
    service = PlateInspectionService(
        AgentPathPolicy.with_roots(readable_roots=(root,), writable_roots=(root,)),
        filemanager_factory=factory,
    )
    return stack, service, factory


def _query(service, root, *, microscope_type="bioformats"):
    result = service.query_files(
        PlateFileQueryRequest.from_fields(
            plate_path=str(root), microscope_type=microscope_type, limit=10
        )
    )
    assert result.errors == ()
    return result


def _sample(service, root, image_path, *, microscope_type="bioformats"):
    result = service.sample_image(
        PlateImageSampleRequest.from_fields(
            plate_path=str(root),
            image_path=image_path,
            microscope_type=microscope_type,
            resolution_index=0,
            y=2,
            x=3,
            height=2,
            width=2,
            max_array_elements=4,
        )
    )
    assert result.errors == ()
    return result


@pytest.mark.parametrize("channels", (3, 4))
def test_original_physical_candidates_are_sampleable_before_projection(tmp_path, channels):
    stack, service, _ = _fixture(tmp_path, channels)
    query = _query(service, tmp_path)
    assert query.total_count == channels
    record = next(record for record in query.records if int(record.metadata["channel"]) == 3)
    sample = _sample(service, tmp_path, record.virtual_path)
    assert int(sample.source_metadata["channel"]) == 3
    assert sample.sample_values == stack[0, 0, 2, 2:4, 3:5].tolist()
    assert not (tmp_path / "openhcs_metadata.json").exists()


@pytest.mark.parametrize("channels", (3, 4))
def test_physical_c3_remains_available_after_c1_only_preparation(tmp_path, channels):
    stack, service, factory = _fixture(tmp_path, channels)
    bindings = SourceBindingsConfig(
        bindings=(
            NamedSourceBinding(
                alias="engineering_selected",
                selector=SourceSelector(metadata=(MetadataSelector("channel", "1"),)),
            ),
        )
    )
    filemanager = factory.create()
    BioFormatsHandler(filemanager, source_bindings_config=bindings).initialize_workspace(
        tmp_path, filemanager
    )
    metadata_path = tmp_path / "openhcs_metadata.json"
    before = metadata_path.read_bytes()
    persisted = json.loads(before)["subdirectories"]["."]
    assert len(persisted["image_files"]) == 1
    assert {int(value["channel"]) for value in persisted["source_metadata"].values()} == {1}
    try:
        # Ordinary auto/workspace routing must keep the persisted C1 selection.
        selected = _query(service, tmp_path, microscope_type="auto")
        assert selected.total_count == 1
        assert {int(record.metadata["channel"]) for record in selected.records} == {1}
        sample = _sample(
            service, tmp_path, str(tmp_path / "stack.npy"), microscope_type="auto"
        )
        assert int(sample.source_metadata["channel"]) == 1
        assert sample.sample_values == stack[0, 0, 0, 2:4, 3:5].tolist()

        query = _query(service, tmp_path)
        observed_channels = {int(record.metadata["channel"]) for record in query.records}
        # No invented C3 path, receipt, source-ref override, or projection mutation.
        assert 3 in observed_channels, (
            "Explicit physical-source inspection hides C3 after C1 preparation: "
            f"observed_channels={sorted(observed_channels)}, total_count={query.total_count}"
        )
        assert observed_channels == set(range(1, channels + 1))
        record = next(record for record in query.records if int(record.metadata["channel"]) == 3)
        physical = _sample(service, tmp_path, record.virtual_path)
        assert int(physical.source_metadata["channel"]) == 3
        assert physical.sample_values == stack[0, 0, 2, 2:4, 3:5].tolist()
        assert physical.source_path == str(tmp_path / "stack.npy")

        # The original generic (pipeline/Image Browser) constructor still gives
        # the selected projection precedence even over an exact acquisition owner.
        physical_handler = BioFormatsHandler(filemanager)
        projection = VirtualWorkspaceSourceProjectionAuthority.from_plate_metadata(
            plate_path=tmp_path,
            metadata_handler=physical_handler.metadata_handler,
            filemanager=filemanager,
        ).projection_if_available()
        assert projection is not None
        selected_inventory = PlateImageInventory.from_handler(
            plate_path=tmp_path,
            handler=physical_handler,
            filemanager=filemanager,
            backend=Backend.DISK.value,
            source_projection=projection,
        )
        assert len(selected_inventory.records) == 1
        assert int(selected_inventory.records[0].metadata["channel"]) == 1

        # Exercise the existing stream's source preparation, not a viewer/mock
        # or a new decoder. The actual native launch remains parent-owned.
        from openhcs.agent.services.plate_streaming_service import PlateStreamingService
        from openhcs.core.viewer_streaming_service import ViewerStreamingSource

        context, errors, _ = service.open_context(
            PlatePathInspectionRequest(plate_path=str(tmp_path), microscope_type="bioformats")
        )
        assert errors == ()
        inventory, warnings = service.file_inventory(context, kind=PlateFileKind.IMAGE)
        assert warnings == ()
        stream_record = inventory.require_stream_record(record.virtual_path)
        stream_projection = PlateStreamingService._inventory_source_projection(
            (stream_record,), context
        )
        assert stream_projection is not None
        stream_source = ViewerStreamingSource(
            filemanager=context.filemanager,
            microscope_handler=context.handler,
            plate_path=str(tmp_path),
        )
        image = stream_source.load_image(
            stream_record.streamable_image_path,
            stream_record.source_ref.backend,
            source_projection=stream_projection,
            component_metadata=stream_record.metadata,
        )
        np.testing.assert_array_equal(image.data, stack[0, 0, 2])
        metadata = image.metadata
        assert metadata.source_voxel_spacing == SourceVoxelSpacing((0.5, 0.5))

        ambiguous = service.sample_image(
            PlateImageSampleRequest.from_fields(
                plate_path=str(tmp_path),
                image_path=str(tmp_path / "stack.npy"),
                microscope_type="bioformats",
                resolution_index=0,
                height=2,
                width=2,
                max_array_elements=4,
            )
        )
        assert ambiguous.errors
        assert ambiguous.errors[0].code == "plate_image_sample_failed"
        assert "matched multiple records" in ambiguous.errors[0].message
        assert ambiguous.sample_included is False
        assert ambiguous.sample_values == ()
    finally:
        assert metadata_path.read_bytes() == before


def test_independent_metadata_hook_flows_through_unchanged_inventory_consumer(tmp_path):
    _, service, factory = _fixture(tmp_path, 4)
    filemanager = factory.create()
    handler = BioFormatsHandler(filemanager)
    handler.metadata_handler = DeclaredInspectionMetadata(filemanager)
    warnings = []
    inventory = service._image_inventory(handler, tmp_path, filemanager, warnings)
    assert warnings == []
    assert len(inventory.records) == 4
    assert {record.metadata["inspection_witness"] for record in inventory.records} == {"declared"}
    assert {int(record.metadata["channel"]) for record in inventory.records} == {1, 2, 3, 4}
    assert all(record.source_ref is not None for record in inventory.records)
    assert not (tmp_path / "openhcs_metadata.json").exists()
