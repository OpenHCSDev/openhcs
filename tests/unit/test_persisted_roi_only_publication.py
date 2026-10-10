"""Saved-output publication only: synthetic bytes, no ROI or pixel decoding."""

from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.dataset_sources.source_schema import SourceSchemaFilenameParser
import json

import pytest

from openhcs.agent.dto.plate import PlateFileQueryRequest
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.plate_inspection_service import (
    PlateInspectionFileManagerFactory,
    PlateInspectionService,
)
from openhcs.constants.constants import Backend
from openhcs.core.artifacts import ArtifactOutputPlan, MetadataArtifactType
from openhcs.core.compiled_step_plan import (
    CompiledStepPlan,
    RuntimeArtifactMaterializationPlan,
)
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.runtime_artifact_values import RuntimeValue
from openhcs.core.runtime_stores import RuntimeArtifactLocation, StoredRuntimeValue
from openhcs.core.steps.function_artifact_materialization import (
    MaterializedRuntimeArtifact,
    RuntimeArtifactMaterialization,
)
from openhcs.core.steps.function_outputs import (
    OpenHCSMetadataTarget,
    ProducedImageMetadataCapability,
    RuntimeArtifactMetadataTarget,
)
from openhcs.core.virtual_workspace_metadata import AtomicMetadataWriter, METADATA_CONFIG, MetadataWriteError
from openhcs.processing.materialization.core import (
    MaterializationSpec,
    _WRITERS_BY_OPTIONS,
    prepare_materialization,
)
from openhcs.processing.materialization.options import FileBundleOptions
from openhcs.domains.microscopy.axes import Microscopy


def _publish_saved_step(context, plan, *, artifact_materializations=()):
    """Exercise the receiving transaction with this step's actual saved facts."""
    facts = OpenHCSMetadataTarget.observe_for_step(
        context, plan, artifact_materializations=artifact_materializations
    )
    for metadata_path in dict.fromkeys(
        METADATA_CONFIG.metadata_path(target.plate_root) for target in facts
    ):
        entries = {
            target: value for target, value in facts.items()
            if METADATA_CONFIG.metadata_path(target.plate_root) == metadata_path
        }
        AtomicMetadataWriter().reconcile_completed_plate(
            metadata_path,
            {target: context for target in entries if target.create_openhcs_metadata},
            produced_entries_by_target=entries,
        )


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


class PublicationAuditCapability:
    """Independent audit capability extends, rather than replaces, publication."""

    def write(self, context, *, produced_plan=None):
        context.publication_audit.append(("before", self.sub_dir))
        super().write(context, produced_plan=produced_plan)
        context.publication_audit.append(("after", self.sub_dir))


def plan_for(plate):
    return CompiledStepPlan(
        step_index=0,
        step_name="synthetic saved result",
        axis_id="A01",
        write_backend=Backend.MEMORY.value,
        create_openhcs_metadata=True,
        output_plate_root=str(plate),
        analysis_results_dir=str(plate / "compiled_default"),
        runtime_artifact_materialization=RuntimeArtifactMaterializationPlan(
            persistent_enabled=True,
            persistent_backend=Backend.DISK.value,
        ),
    )


def save_archive_outcome(
    context, plate, destination, monkeypatch,
    *, filename="independent-outline.roi.zip", content=b"synthetic admission only",
):
    """Use the original declared bundle writer, batch and disk save boundary."""
    spec = MaterializationSpec(FileBundleOptions())
    payload = {f"{destination}/{filename}": content}
    base_path = plate / "bundle"
    batch = prepare_materialization(
        spec,
        payload,
        str(base_path),
        context.filemanager,
        (Backend.DISK.value,),
    )
    saved = batch.save()
    (output,) = saved.outputs_for_backend(Backend.DISK.value)
    assert output is batch.outputs[0]
    # Source qualification must consume the original successful save, not render
    # a mutable logical payload again or use planned names as proof of a save.
    payload.clear()

    def forbidden_render(*args, **kwargs):
        pytest.fail("Publication rendered the already-saved batch again")

    writer = _WRITERS_BY_OPTIONS[FileBundleOptions]
    monkeypatch.setitem(
        _WRITERS_BY_OPTIONS, FileBundleOptions, replace(writer, write=forbidden_render)
    )
    artifact_plan = ArtifactOutputPlan(
        name="synthetic archive bundle",
        path="/memory/bundle.pkl",
        artifact_type=MetadataArtifactType,
        materialization=spec,
    )
    value = RuntimeValue.from_output_plan(
        artifact_plan,
        {},
        execution_scope=RuntimeExecutionAxisScope(axis_id="A01"),
    )
    record = StoredRuntimeValue(
        key=value.key,
        data=value.data,
        materialization_source_metadata=value.materialization_source_metadata,
        location=RuntimeArtifactLocation(
            path=artifact_plan.path, backend=Backend.MEMORY.value
        ),
    )
    materialization = RuntimeArtifactMaterialization(
        output_plan=artifact_plan,
        spec=spec,
        record=record,
        data=payload,
        base_path=base_path,
        source_identity=None,
        filename_source_identity=None,
    )
    return (
        MaterializedRuntimeArtifact(
            outputs_by_backend=saved.outputs_by_backend,
            materialization=materialization,
        ),
        output,
    )


class ExistingDiskInspectionFactory(PlateInspectionFileManagerFactory):
    """Original public service receives the same real disk manager as saving."""

    def __init__(self, manager):
        self.manager = manager

    def create(self):
        return self.manager


@pytest.fixture(autouse=True)
def forbid_optional_backend_bootstrap(monkeypatch):
    import polystore.base

    def forbidden_bootstrap(*args, **kwargs):
        pytest.fail("Source-only qualification must not bootstrap optional backends")

    monkeypatch.setattr(polystore.base, "ensure_storage_registry", forbidden_bootstrap)


def result_paths(plate, context):
    service = PlateInspectionService(
        AgentPathPolicy.with_roots(readable_roots=(plate,), writable_roots=()),
        filemanager_factory=ExistingDiskInspectionFactory(context.filemanager),
    )
    result = service.query_files(
        PlateFileQueryRequest.from_fields(
            plate_path=str(plate),
            microscope_type="openhcsdata",
            kind="result",
            include_previews=False,
        )
    )
    assert result.errors == ()
    assert all(record.preview is None for record in result.records)
    return tuple(record.full_path for record in result.records)


@pytest.mark.parametrize("destination", ("roi_only", "independent/nested/roi_only"))
def test_saved_roi_only_batch_publishes_and_reconciles_without_rendering(
    tmp_path,
    publication_context,
    monkeypatch,
    destination,
):
    plate = tmp_path / "plate"
    outcome, output = save_archive_outcome(
        publication_context, plate, destination, monkeypatch
    )
    plan = plan_for(plate)
    targets = OpenHCSMetadataTarget.for_execution(
        publication_context,
        plan,
        artifact_materializations=(outcome,),
    )
    assert tuple(target.output_dir for target in targets) == (plate / destination,)
    _publish_saved_step(
        publication_context, plan, artifact_materializations=(outcome,)
    )
    assert result_paths(plate, publication_context) == (output.path,)
    published = json.loads(METADATA_CONFIG.metadata_path(plate).read_text())
    assert published["subdirectories"][destination]["image_files"] == []
    assert published["subdirectories"][destination]["source_projection"] == []
    # Final reconciliation has no runtime outcome/value to reconstruct. Its
    # destination comes from the same durable declaration the reader admitted.
    publication_context.step_plans = {0: plan}
    owner = RuntimeArtifactMetadataTarget.from_plan(plan)
    reconciled = tuple(
        target.output_dir
        for target in owner.reconciliation_targets(publication_context)
    )
    assert plate / destination in reconciled
    OpenHCSMetadataTarget.finalize_completed_plate({"A01": publication_context})
    assert result_paths(plate, publication_context) == (output.path,)


def test_shared_writer_accepts_result_only_but_not_unaddressed_images(
    tmp_path,
    publication_context,
):
    plate = tmp_path / "plate"
    directory = plate / "standalone_result"
    directory.mkdir(parents=True)
    roi = directory / "independent-outline.roi.zip"
    roi.write_bytes(b"synthetic admission only")
    target = RuntimeArtifactMetadataTarget.from_plan(plan_for(plate)).for_directory(
        directory
    )
    target.write(publication_context)
    assert result_paths(plate, publication_context) == (str(roi),)
    metadata_path = METADATA_CONFIG.metadata_path(plate)
    before = metadata_path.read_bytes()
    (directory / "unaddressed-image.tif").write_bytes(b"never decoded")
    with pytest.raises(
        MetadataWriteError, match="Saved images lack typed produced addresses"
    ):
        target.write(publication_context)
    assert metadata_path.read_bytes() == before


def test_measurement_only_step_does_not_reconcile_pending_image_producer(
    tmp_path, publication_context, monkeypatch,
):
    from polystore.virtual_workspace import SourcePixelRef

    from openhcs.core.artifacts import ImageArtifactType
    from openhcs.core.source_projection import OpenHCSPlaneAddress, SourceArtifactProjection
    from openhcs.core.virtual_workspace_metadata import (
        AtomicMetadataWriter, FIELDS, VirtualWorkspaceSourceProjectionEntries,
    )

    plate = tmp_path / "plate"
    destination = "shared_results"
    outcome, table_output = save_archive_outcome(
        publication_context, plate, destination, monkeypatch,
        filename="measurements.csv", content=b"ObjectNumber,Area\n1,6\n",
    )
    pending = plate / destination / "independent-image.tif"
    # This lifecycle fixture never reads or derives addresses from the bytes.
    pending.write_bytes(b"producer pixel save precedes its typed publication")
    plan = plan_for(plate)
    (target,) = OpenHCSMetadataTarget.for_execution(
        publication_context, plan, artifact_materializations=(outcome,),
    )
    assert target.produced_projection_entries(publication_context, plan).entries == {}
    staged = OpenHCSMetadataTarget.observe_for_step(
        publication_context, plan, artifact_materializations=(outcome,),
    )
    metadata_path = METADATA_CONFIG.metadata_path(plate)
    assert not metadata_path.exists()
    assert table_output.path == str(plate / destination / "measurements.csv")
    assert (plate / destination / "measurements.csv").read_bytes() == b"ObjectNumber,Area\n1,6\n"
    with pytest.raises(MetadataWriteError, match="lack typed produced addresses"):
        AtomicMetadataWriter().reconcile_completed_plate(
            metadata_path, {target: publication_context},
            produced_entries_by_target=staged,
        )
    assert not metadata_path.exists()

    virtual_path = str(pending.relative_to(plate))
    projection = SourceArtifactProjection(
        address=OpenHCSPlaneAddress(((Microscopy.Well, "A04"), (Microscopy.Site, 1), (Microscopy.Channel, 2), (Microscopy.ZIndex, 1), (Microscopy.Timepoint, 1))),
        ref=SourcePixelRef(Backend.DISK.value, virtual_path),
        source_alias="declared_image", artifact_kind=ImageArtifactType,
    )
    from openhcs.core.source_projection import SourceProjectionMetadataSerializer
    AtomicMetadataWriter().replace_subdirectory_metadata(
        metadata_path, destination,
        SourceProjectionMetadataSerializer.projection_fields(((projection, virtual_path),)),
    )
    publication_context.step_plans = {0: plan}
    OpenHCSMetadataTarget.finalize_completed_plate({"A01": publication_context})
    reconciled = json.loads(metadata_path.read_text())[FIELDS.SUBDIRECTORIES][destination]
    assert reconciled[FIELDS.IMAGE_FILES] == [virtual_path]
    assert len(reconciled[FIELDS.SOURCE_PROJECTION]) == 1
    restored = VirtualWorkspaceSourceProjectionEntries.from_subdirectory(reconciled)
    assert restored.entries[virtual_path].address == projection.address
    assert pending.read_bytes() == b"producer pixel save precedes its typed publication"


def test_reconciliation_keeps_artifact_destination_without_results_field(
    tmp_path, publication_context
):
    from polystore.virtual_workspace import SourcePixelRef

    from openhcs.core.source_projection import (
        OpenHCSPlaneAddress,
        SourceArtifactProjection,
        SourceProjectionMetadataSerializer,
    )
    from openhcs.core.dataset_sources.openhcs_format import OpenHCSMetadataHandler

    plate = tmp_path / "plate"
    plate.mkdir()
    projection = SourceArtifactProjection(
        address=OpenHCSPlaneAddress(((Microscopy.Well, "A01"), (Microscopy.Site, "1"), (Microscopy.Channel, "2"), (Microscopy.ZIndex, "1"), (Microscopy.Timepoint, "1"))),
        ref=SourcePixelRef(Backend.DISK.value, "physical/acquisition-source.tif"),
        source_alias="Declared",
        artifact_kind=MetadataArtifactType,
    )
    fields = SourceProjectionMetadataSerializer(
        SourceSchemaFilenameParser()
    ).projection_fields(((projection, "nested/declared-result.tif"),))
    metadata_path = METADATA_CONFIG.metadata_path(plate)
    metadata_path.write_text(json.dumps({"subdirectories": {"nested": fields}}))
    before = metadata_path.read_bytes()
    handler = OpenHCSMetadataHandler(publication_context.filemanager)
    assert handler.analysis_result_directories(plate) == ()
    owner = RuntimeArtifactMetadataTarget.from_plan(plan_for(plate))
    assert plate / "nested" in tuple(
        target.output_dir for target in owner.reconciliation_targets(publication_context)
    )
    assert metadata_path.read_bytes() == before


@pytest.mark.parametrize("later_subdirectory", [False, True])
def test_reconciliation_admits_all_projection_rows_before_workspace_fields(
    tmp_path, publication_context, later_subdirectory
):
    plate = tmp_path / "plate"
    plate.mkdir()
    invalid_row = {
        "virtual_path": "images/unregistered.tif",
        "projection_role": "unknown",
    }
    subdirectories = {"images": {"workspace_mapping": "invalid"}}
    destination = "later" if later_subdirectory else "images"
    subdirectories.setdefault(destination, {})["source_projection"] = [invalid_row]
    metadata_path = METADATA_CONFIG.metadata_path(plate)
    metadata_path.write_text(json.dumps({"subdirectories": subdirectories}))
    before = metadata_path.read_bytes()
    owner = RuntimeArtifactMetadataTarget.from_plan(plan_for(plate))
    with pytest.raises(RuntimeError, match="unknown projection_role"):
        owner.reconciliation_targets(publication_context)
    assert metadata_path.read_bytes() == before


def test_reconciliation_preserves_raw_json_error_and_missing_document_error(
    tmp_path, publication_context
):
    from polystore.exceptions import MetadataNotFoundError

    plate = tmp_path / "plate"
    plate.mkdir()
    metadata_path = METADATA_CONFIG.metadata_path(plate)
    owner = RuntimeArtifactMetadataTarget.from_plan(plan_for(plate))
    with pytest.raises(MetadataNotFoundError):
        owner.reconciliation_targets(publication_context)
    metadata_path.write_text("{")
    with pytest.raises(json.JSONDecodeError):
        owner.reconciliation_targets(publication_context)
    assert metadata_path.read_text() == "{"


def test_new_result_declaration_composes_cooperative_hooks_without_consumer_edits(
    tmp_path,
    publication_context,
    monkeypatch,
):
    plate = tmp_path / "plate"
    destination = "new/declaration_only"
    outcome, output = save_archive_outcome(
        publication_context, plate, destination, monkeypatch
    )
    registry = OpenHCSMetadataTarget.__registry__
    original_declarations = dict(registry)
    try:

        class IndependentSavedResultMetadataTarget(
            PublicationAuditCapability,
            ProducedImageMetadataCapability,
            RuntimeArtifactMetadataTarget,
        ):
            declaration_key = None

            @classmethod
            def from_plan(cls, plan):
                return cls(
                    output_dir=plate / destination,
                    backend=Backend.DISK.value,
                    plate_root=str(plate),
                    sub_dir=destination,
                    results_dir=str(plate / destination),
                )

        plan = replace(
            plan_for(plate),
            runtime_artifact_materialization=RuntimeArtifactMaterializationPlan(),
        )
        (target,) = OpenHCSMetadataTarget.for_execution(
            publication_context,
            plan,
            artifact_materializations=(outcome,),
        )
        target.write(publication_context, produced_plan=plan)
        assert publication_context.publication_audit == [
            ("before", destination),
            ("after", destination),
        ]
        assert result_paths(plate, publication_context) == (output.path,)
        pending = plate / destination / "pending-image.tif"
        pending.write_bytes(b"never decoded")
        target.write(publication_context, produced_plan=plan)
        assert publication_context.publication_audit == [
            ("before", destination), ("after", destination),
            ("before", destination), ("after", destination),
        ]
        # Independent MI hooks reach the inherited empty-step behavior even
        # while another image producer has not published its typed address.
        assert target.produced_projection_entries(publication_context, plan).entries == {}
        before = METADATA_CONFIG.metadata_path(plate).read_bytes()
        with pytest.raises(MetadataWriteError, match="lack typed produced addresses"):
            target.write(publication_context)
        assert METADATA_CONFIG.metadata_path(plate).read_bytes() == before
        assert Path(output.path).read_bytes() == b"synthetic admission only"
    finally:
        registry.clear()
        registry.update(original_declarations)


def test_files_without_successful_batch_outcomes_do_not_create_step_targets(
    tmp_path,
    publication_context,
):
    plate = tmp_path / "plate"
    directory = plate / "unclaimed"
    directory.mkdir(parents=True)
    (directory / "not_a_saved_outcome.roi.zip").write_bytes(b"synthetic admission only")
    assert (
        OpenHCSMetadataTarget.for_execution(
            publication_context,
            plan_for(plate),
            artifact_materializations=(),
        )
        == ()
    )
