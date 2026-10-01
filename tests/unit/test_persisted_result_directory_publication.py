"""Original metadata writer/reader contracts, with no pixel or ROI content reads."""

from pathlib import Path
from types import SimpleNamespace

import pytest
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
from polystore.virtual_workspace import SourcePixelRef

from openhcs.agent.dto.plate import PlateFileQueryRequest
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.plate_inspection_service import PlateInspectionService
from openhcs.constants.constants import Backend
from openhcs.core.artifacts import ObjectLabelsArtifactType
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.source_projection import (
    OpenHCSPlaneAddress,
    SourceArtifactProjection,
    SourceProjectionMetadataSerializer,
)
from openhcs.core.steps.function_outputs import (
    OpenHCSMetadataWriter,
    ProducedImageMetadataCapability,
)
from openhcs.core.virtual_workspace_metadata import AtomicMetadataWriter, METADATA_CONFIG
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser


@pytest.fixture
def publication_context(tmp_path):
    filemanager = FileManager({Backend.DISK.value: DiskStorageBackend()})
    context = ProcessingContext(filemanager=filemanager)
    context.metadata_cache = {}
    context.microscope_handler = SimpleNamespace(
        parser=SourceSchemaFilenameParser(), microscope_type="openhcsdata"
    )
    context.publication_audit = []
    return context


def seed_synthetic_projection(plate, directory):
    directory.mkdir(parents=True)
    roi = directory / "independent-outline.roi.zip"
    roi.write_bytes(b"path-admission sentinel, never decoded")
    image = directory / "independent-labels.tif"
    image.write_bytes(b"path-admission sentinel, never loaded")
    path = str(image.relative_to(plate))
    components = {
        "well": "A01", "site": "1", "channel": "2",
        "z_index": "1", "timepoint": "1", "pixel_size": 1.25,
    }
    projection = SourceArtifactProjection(
        address=OpenHCSPlaneAddress.from_values("A01", "1", "2", "1", "1"),
        ref=SourcePixelRef(Backend.DISK.value, path),
        source_alias="independent labels",
        artifact_kind=ObjectLabelsArtifactType,
        source_metadata=components,
        image_metadata=ImagePayloadMetadata(source_component_metadata=components),
    )
    AtomicMetadataWriter().merge_source_projection_metadata(
        METADATA_CONFIG.metadata_path(plate),
        str(directory.relative_to(plate)),
        SourceProjectionMetadataSerializer(SourceSchemaFilenameParser()).projection_fields(
            ((projection, path),)
        ),
    )
    return roi


class PublicationAuditCapability:
    """Independent audit capability extends, rather than replaces, publication."""

    def write(self, context, *, produced_plan=None):
        context.publication_audit.append(("before", self.sub_dir))
        super().write(context, produced_plan=produced_plan)
        context.publication_audit.append(("after", self.sub_dir))


@pytest.mark.parametrize("destination", ("supplemental", "nested/supplemental"))
def test_new_declared_target_composes_original_capability_and_writer(
    tmp_path, publication_context, destination
):
    plate = tmp_path / "plate"
    directory = plate / destination
    roi = seed_synthetic_projection(plate, directory)
    registry = OpenHCSMetadataWriter.OutputTarget.__registry__
    original_keys = set(registry)
    try:
        class SupplementalResultMetadataTarget(
            PublicationAuditCapability,
            ProducedImageMetadataCapability,
            OpenHCSMetadataWriter.OutputTarget,
        ):
            @classmethod
            def from_plan(cls, plan):
                return cls(
                    output_dir=directory,
                    backend=Backend.DISK.value,
                    plate_root=str(plate),
                    sub_dir=destination,
                    results_dir=str(directory),
                )

        plan = CompiledStepPlan(
            step_index=0, step_name="independent declaration", step_type="FunctionStep",
            axis_id="A01", write_backend=Backend.MEMORY.value,
        )
        # Discovery stays the original family algorithm. No roster or consumer
        # edit: the new declaration supplies only its destination hook.
        (target,) = OpenHCSMetadataWriter.OutputTarget.for_execution(publication_context, plan)
        target.write(publication_context, produced_plan=plan)
        assert publication_context.publication_audit == [
            ("before", destination), ("after", destination)
        ]
        service = PlateInspectionService(
            AgentPathPolicy.with_roots(readable_roots=(plate,), writable_roots=())
        )
        result = service.query_files(
            PlateFileQueryRequest.from_fields(
                plate_path=str(plate), kind="result", include_previews=False
            )
        )
        assert result.errors == ()
        assert str(roi) in tuple(record.full_path for record in result.records)
        assert all(record.preview is None for record in result.records)
    finally:
        for key in set(registry) - original_keys:
            del registry[key]
