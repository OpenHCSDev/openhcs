"""Saved-output publication only: synthetic bytes, no ROI or pixel decoding."""

from dataclasses import replace
import json

import pytest

from openhcs.agent.dto.plate import PlateFileQueryRequest
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.plate_inspection_service import (
    PlateInspectionFileManagerFactory, PlateInspectionService,
)
from openhcs.constants.constants import Backend
from openhcs.core.artifacts import ArtifactOutputPlan, MetadataArtifactType
from openhcs.core.compiled_step_plan import CompiledStepPlan, RuntimeArtifactMaterializationPlan
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.runtime_artifact_values import RuntimeValue
from openhcs.core.runtime_stores import RuntimeArtifactLocation, StoredRuntimeValue
from openhcs.core.steps.function_artifact_materialization import (
    MaterializedRuntimeArtifact, RuntimeArtifactMaterialization,
)
from openhcs.core.steps.function_outputs import (
    OpenHCSMetadataWriter, ProducedImageMetadataCapability, RuntimeArtifactMetadataTarget,
)
from openhcs.core.virtual_workspace_metadata import METADATA_CONFIG, MetadataWriteError
from openhcs.processing.materialization.core import (
    MaterializationSpec, _WRITERS_BY_OPTIONS, prepare_materialization,
)
from openhcs.processing.materialization.options import FileBundleOptions

from test_persisted_result_directory_publication import (
    PublicationAuditCapability, publication_context,
)


def plan_for(plate):
    return CompiledStepPlan(
        step_index=0, step_name="synthetic saved result", step_type="FunctionStep",
        axis_id="A01", write_backend=Backend.MEMORY.value, create_openhcs_metadata=True,
        output_plate_root=str(plate), analysis_results_dir=str(plate / "compiled_default"),
        runtime_artifact_materialization=RuntimeArtifactMaterializationPlan(
            persistent_enabled=True, persistent_backend=Backend.DISK.value,
        ),
    )


def save_archive_outcome(context, plate, destination, monkeypatch):
    """Use the original declared bundle writer, batch and disk save boundary."""
    spec = MaterializationSpec(FileBundleOptions())
    payload = {f"{destination}/independent-outline.roi.zip": b"synthetic admission only"}
    base_path = plate / "bundle"
    batch = prepare_materialization(
        spec, payload, str(base_path), context.filemanager, (Backend.DISK.value,),
    )
    saved = batch.save()
    output, = saved.outputs_for_backend(Backend.DISK.value)
    assert output is batch.outputs[0]
    # Source qualification must consume the original successful save, not render
    # a mutable logical payload again or use planned names as proof of a save.
    payload.clear()

    def forbidden_render(*args, **kwargs):
        pytest.fail("Publication rendered the already-saved batch again")

    writer = _WRITERS_BY_OPTIONS[FileBundleOptions]
    monkeypatch.setitem(_WRITERS_BY_OPTIONS, FileBundleOptions, replace(writer, write=forbidden_render))
    artifact_plan = ArtifactOutputPlan(
        name="synthetic archive bundle", path="/memory/bundle.pkl",
        artifact_type=MetadataArtifactType, materialization=spec,
    )
    record = StoredRuntimeValue(
        value=RuntimeValue.from_output_plan(
            artifact_plan, {}, execution_scope=RuntimeExecutionAxisScope(axis_id="A01"),
        ),
        location=RuntimeArtifactLocation(path=artifact_plan.path, backend=Backend.MEMORY.value),
    )
    materialization = RuntimeArtifactMaterialization(
        output_plan=artifact_plan, spec=spec, record=record, data=payload,
        base_path=base_path, source_identity=None, filename_source_identity=None,
    )
    return MaterializedRuntimeArtifact(
        outputs_by_backend=saved.outputs_by_backend, materialization=materialization,
    ), output


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
    result = service.query_files(PlateFileQueryRequest.from_fields(
        plate_path=str(plate), microscope_type="openhcsdata",
        kind="result", include_previews=False,
    ))
    assert result.errors == ()
    assert all(record.preview is None for record in result.records)
    return tuple(record.full_path for record in result.records)


@pytest.mark.parametrize("destination", ("roi_only", "independent/nested/roi_only"))
def test_saved_roi_only_batch_publishes_and_reconciles_without_rendering(
    tmp_path, publication_context, monkeypatch, destination,
):
    plate = tmp_path / "plate"
    outcome, output = save_archive_outcome(publication_context, plate, destination, monkeypatch)
    plan = plan_for(plate)
    targets = OpenHCSMetadataWriter.OutputTarget.for_execution(
        publication_context, plan, artifact_materializations=(outcome,),
    )
    assert tuple(target.output_dir for target in targets) == (plate / destination,)
    OpenHCSMetadataWriter.write(publication_context, plan, artifact_materializations=(outcome,))
    assert result_paths(plate, publication_context) == (output.path,)
    published = json.loads(METADATA_CONFIG.metadata_path(plate).read_text())
    assert published["subdirectories"][destination]["image_files"] == []
    assert published["subdirectories"][destination]["source_projection"] == []
    # Final reconciliation has no runtime outcome/value to reconstruct. Its
    # destination comes from the same durable declaration the reader admitted.
    publication_context.step_plans = {0: plan}
    owner = RuntimeArtifactMetadataTarget.from_plan(plan)
    reconciled = tuple(target.output_dir for target in owner.reconciliation_targets(publication_context))
    assert plate / destination in reconciled
    OpenHCSMetadataWriter.finalize_completed_plate({"A01": publication_context})
    assert result_paths(plate, publication_context) == (output.path,)


def test_shared_writer_accepts_result_only_but_not_unaddressed_images(
    tmp_path, publication_context,
):
    plate = tmp_path / "plate"
    directory = plate / "standalone_result"
    directory.mkdir(parents=True)
    roi = directory / "independent-outline.roi.zip"
    roi.write_bytes(b"synthetic admission only")
    target = RuntimeArtifactMetadataTarget.from_plan(plan_for(plate)).for_directory(directory)
    target.write(publication_context)
    assert result_paths(plate, publication_context) == (str(roi),)
    metadata_path = METADATA_CONFIG.metadata_path(plate)
    before = metadata_path.read_bytes()
    (directory / "unaddressed-image.tif").write_bytes(b"never decoded")
    with pytest.raises(MetadataWriteError, match="Saved images lack typed produced addresses"):
        target.write(publication_context)
    assert metadata_path.read_bytes() == before


def test_new_result_declaration_composes_cooperative_hooks_without_consumer_edits(
    tmp_path, publication_context, monkeypatch,
):
    plate = tmp_path / "plate"
    destination = "new/declaration_only"
    outcome, output = save_archive_outcome(publication_context, plate, destination, monkeypatch)
    registry = OpenHCSMetadataWriter.OutputTarget.__registry__
    original_keys = set(registry)
    try:
        class IndependentSavedResultMetadataTarget(
            PublicationAuditCapability, ProducedImageMetadataCapability,
            RuntimeArtifactMetadataTarget,
        ):
            @classmethod
            def from_plan(cls, plan):
                return cls(
                    output_dir=plate / destination, backend=Backend.DISK.value,
                    plate_root=str(plate), sub_dir=destination,
                    results_dir=str(plate / destination),
                )

        plan = replace(plan_for(plate), runtime_artifact_materialization=RuntimeArtifactMaterializationPlan())
        target, = OpenHCSMetadataWriter.OutputTarget.for_execution(
            publication_context, plan, artifact_materializations=(outcome,),
        )
        target.write(publication_context, produced_plan=plan)
        assert publication_context.publication_audit == [("before", destination), ("after", destination)]
        assert result_paths(plate, publication_context) == (output.path,)
    finally:
        for key in set(registry) - original_keys:
            del registry[key]


def test_files_without_successful_batch_outcomes_do_not_create_step_targets(
    tmp_path, publication_context,
):
    plate = tmp_path / "plate"
    directory = plate / "unclaimed"
    directory.mkdir(parents=True)
    (directory / "not_a_saved_outcome.roi.zip").write_bytes(b"synthetic admission only")
    assert OpenHCSMetadataWriter.OutputTarget.for_execution(
        publication_context, plan_for(plate), artifact_materializations=(),
    ) == ()
