"""Real inspection/inventory/source-ref boundary; no Java or scientific input."""

import json
from pathlib import Path

import numpy as np
import pytest
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager

from openhcs.agent.dto.plate import PlateFileQueryRequest, PlateImageSampleRequest
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.plate_inspection_service import (
    PlateInspectionFileManagerFactory,
    PlateInspectionService,
)
from openhcs.constants.constants import Backend
from openhcs.core.source_bindings import (
    MetadataSelector,
    NamedSourceBinding,
    SourceBindingsConfig,
    SourceSelector,
)
from openhcs.microscopes.bioformats import BioFormatsHandler
from tests.unit.bioformats_fixture import write_bioformats_manifest_fixture


class DiskOnlyInspectionFileManagerFactory(PlateInspectionFileManagerFactory):
    """Declare only the real storage capability used by the engineering fixture."""

    def create(self) -> FileManager:
        return FileManager({Backend.DISK.value: DiskStorageBackend()})


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


def _query(service, root):
    result = service.query_files(
        PlateFileQueryRequest.from_fields(
            plate_path=str(root), microscope_type="bioformats", limit=10
        )
    )
    assert result.errors == ()
    return result


def _sample(service, root, image_path):
    result = service.sample_image(
        PlateImageSampleRequest.from_fields(
            plate_path=str(root),
            image_path=image_path,
            microscope_type="bioformats",
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


def test_physical_c3_remains_available_after_c1_only_preparation(tmp_path):
    stack, service, factory = _fixture(tmp_path, 3)
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
        # The exact retained live behavior: a physical container resolves to C1.
        sample = _sample(service, tmp_path, str(tmp_path / "stack.npy"))
        assert int(sample.source_metadata["channel"]) == 1
        assert sample.sample_values == stack[0, 0, 0, 2:4, 3:5].tolist()

        query = _query(service, tmp_path)
        observed_channels = {int(record.metadata["channel"]) for record in query.records}
        # Receiving requirement, deliberately RED on the original public contract.
        # No invented C3 path, receipt, source-ref override, or projection mutation.
        assert 3 in observed_channels, (
            "Explicit physical-source inspection hides C3 after C1 preparation: "
            f"observed_channels={sorted(observed_channels)}, total_count={query.total_count}"
        )
    finally:
        assert metadata_path.read_bytes() == before
