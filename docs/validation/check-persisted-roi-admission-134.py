"""Read-only admission witness and provider-free producer regression for #134.

No image loader, ROI decoder, sampler, viewer or transport is invoked. Synthetic
archive sentinels intentionally test inventory admission, not archive validity.
"""

from pathlib import Path
from types import SimpleNamespace

import pytest
from polystore.filemanager import FileManager
from polystore.disk import DiskStorageBackend
from polystore.virtual_workspace import SourcePixelRef

from openhcs.agent.dto.plate import PlateFileQueryRequest
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.plate_inspection_service import PlateInspectionService
from openhcs.constants.constants import Backend, FileFormat
from openhcs.core.artifacts import ObjectLabelsArtifactType
from openhcs.core.compiled_step_plan import (
    CompiledStepPlan,
    RuntimeArtifactMaterializationPlan,
)
from openhcs.core.plate_file_inventory import PlateFileKind
from openhcs.core.plate_image_inventory import PlateResultFileInventory
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.source_projection import (
    OpenHCSPlaneAddress,
    SourceArtifactProjection,
    SourceProjectionMetadataSerializer,
)
from openhcs.core.steps.function_outputs import RuntimeArtifactMetadataTarget
from openhcs.core.virtual_workspace_metadata import AtomicMetadataWriter, METADATA_CONFIG
from openhcs.microscopes.openhcs import OpenHCSMetadataHandler
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser


RETAINED_PLATE = Path(
    "/home/ts/wt/openhcs-issue-batch-20260929/"
    "neurite-development-skill383-20261001/output/"
    "assisted-2-candidate-2-sensitivity-diagnostic/input_openhcs"
)
RETAINED_ROI = (
    RETAINED_PLATE / "results/A01_s001_w2_z001_t001_neurons_step0_rois.roi.zip"
)


def test_retained_explicit_directory_admits_exact_roi_without_content_read():
    service = PlateInspectionService(
        AgentPathPolicy.with_roots(readable_roots=(RETAINED_PLATE,), writable_roots=())
    )
    result = service.query_files(
        PlateFileQueryRequest.from_fields(
            plate_path=str(RETAINED_PLATE),
            result_directory=str(RETAINED_ROI.parent),
            kind="result",
            include_previews=False,
        )
    )
    assert result.errors == ()
    matching = [record for record in result.records if record.full_path == str(RETAINED_ROI)]
    assert len(matching) == 1
    assert matching[0].file_format == "ROI"
    assert matching[0].preview is None
    record = service.result_directory_inventory(RETAINED_ROI.parent).require_file_record(
        str(RETAINED_ROI)
    )
    assert record.kind is PlateFileKind.RESULT
    assert record.file_format is FileFormat.ROI
    assert record.streamable_roi_path == str(RETAINED_ROI)
    filemanager = FileManager({Backend.DISK.value: DiskStorageBackend()})
    ordinary = PlateResultFileInventory.from_handler(
        plate_path=RETAINED_PLATE,
        metadata_handler=OpenHCSMetadataHandler(filemanager),
        parser=None,
    )
    assert ordinary.records == ()
    print(f"Explicit typed inventory admits {result.total_count} files and exact ROI; no content read")


@pytest.mark.parametrize("destination", ("declared_outputs", "nested/independent_outputs"))
def test_runtime_result_publication_reaches_original_inventory(tmp_path, destination):
    plate = tmp_path / "output_plate"
    directory = plate / destination
    directory.mkdir(parents=True)
    roi = directory / "unrelated-name.roi.zip"
    roi.write_bytes(b"inventory sentinel; not a scientific ROI")
    # Mixed persisted results, like the retained run. This image is never loaded;
    # original typed projection publication supplies its synthetic address.
    image = directory / "unrelated-labels.tif"
    image.write_bytes(b"inventory sentinel; not a scientific image")
    virtual_path = str(image.relative_to(plate))
    components = {
        "well": "A01", "site": "1", "channel": "2",
        "z_index": "1", "timepoint": "1", "pixel_size": 1.25,
    }
    projection = SourceArtifactProjection(
        address=OpenHCSPlaneAddress.from_values("A01", "1", "2", "1", "1"),
        ref=SourcePixelRef(Backend.DISK.value, virtual_path),
        source_alias="synthetic labels",
        artifact_kind=ObjectLabelsArtifactType,
        source_metadata=components,
        image_metadata=ImagePayloadMetadata(source_component_metadata=components),
    )
    AtomicMetadataWriter().merge_source_projection_metadata(
        METADATA_CONFIG.metadata_path(plate),
        destination,
        SourceProjectionMetadataSerializer(SourceSchemaFilenameParser()).projection_fields(
            ((projection, virtual_path),)
        ),
    )
    filemanager = FileManager({Backend.DISK.value: DiskStorageBackend()})
    plan = CompiledStepPlan(
        step_index=0,
        step_name="independent persistent result",
        step_type="FunctionStep",
        axis_id="A01",
        output_plate_root=str(plate),
        analysis_results_dir=str(directory),
        runtime_artifact_materialization=RuntimeArtifactMaterializationPlan(
            persistent_enabled=True, persistent_backend=Backend.DISK.value
        ),
    )
    target = RuntimeArtifactMetadataTarget.from_plan(plan)
    assert target is not None
    context = SimpleNamespace(
        filemanager=filemanager,
        metadata_cache={},
        microscope_handler=SimpleNamespace(
            parser=SourceSchemaFilenameParser(), microscope_type="openhcsdata"
        ),
    )
    # Exercise the original target's shared writer and original metadata reader,
    # without rendering, reading the sentinel, or fabricating a source receipt.
    target.write(context)
    inventory = PlateResultFileInventory.from_handler(
        plate_path=plate,
        metadata_handler=OpenHCSMetadataHandler(filemanager),
        parser=None,
    )
    assert str(roi) in tuple(record.full_path for record in inventory.records)
