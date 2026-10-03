"""Issue435: real saved image occurrences projected through two existing owners."""

from dataclasses import asdict, replace
import json

import pytest
import numpy as np
import tifffile
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
from polystore.memory import MemoryStorageBackend

from test_function_outputs import (
    context_stub, function_step_plan, record_output_path,
)
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser
from openhcs.constants.constants import Backend, Microscope
from openhcs.core.aligned_image_payload import AlignedImageSliceContext
from openhcs.core.artifacts import ArtifactOutputPlan, ImageArtifactType, ObjectLabelsArtifactType
from openhcs.core.compiled_step_plan import RuntimeArtifactMaterializationPlan
from openhcs.core.runtime_artifact_values import RuntimeValue
from openhcs.core.runtime_image_values import ImageMetadataPayload, ImagePayloadMetadata
from openhcs.core.runtime_stores import RuntimeValueStore
from openhcs.core.runtime_object_label_building import SourceImageObjectLabelBuildRequest
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_projection import SourceProjectionMetadataSerializer
from openhcs.core.source_workspace_projection import VirtualWorkspaceSourceProjection
from openhcs.core.steps.function_outputs import (
    PrimaryImageMetadataTarget, RuntimeArtifactMaterializationAuthority,
)
from openhcs.processing.materialization import (
    ImageFileOptions, MaterializationSpec, MaterializedFilenameIdentity,
)


@pytest.mark.parametrize("scenario", ("same_occurrence", "different_path", "stale_scope", "conflicting_metadata", "different_kind"))
def test_saved_roles_publish_once_per_persisted_occurrence(tmp_path, scenario):
    same_persisted_path = scenario != "different_path"
    filemanager = FileManager({
        Backend.DISK.value: DiskStorageBackend(),
        Backend.MEMORY.value: MemoryStorageBackend(),
    })
    context = context_stub(filemanager, parser=SourceSchemaFilenameParser())
    context.microscope_handler.microscope_type = Microscope.OPENHCS.value
    context.runtime_value_store = RuntimeValueStore()
    context.metadata_cache = {}
    context.tiff_config = None
    plan = function_step_plan("Derived role images")
    plan.streaming_configs = {}
    plan.write_backend = Backend.DISK.value
    plan.output_plate_root = str(tmp_path)
    plan.output_dir = tmp_path / "images"
    plan.sub_dir = "images"
    plan.analysis_results_dir = str(plan.output_dir)
    plan.runtime_artifact_materialization = RuntimeArtifactMaterializationPlan(
        persistent_enabled=True, persistent_backend=Backend.DISK.value,
    )
    context.step_plans = {plan.step_index: plan}
    filemanager.ensure_directory(plan.output_dir, Backend.MEMORY.value)
    components = {
        "well": "A01", "site": "1", "channel": "2",
        "z_index": "1", "timepoint": "1", "extension": ".tif",
    }
    for role, scale in (("RawRole", 1.0), ("CappedRole", 0.5)):
        filename = f"A01_s001_w2_z001_t001_{role}.tif"
        output_plan = ArtifactOutputPlan(
            name=role, path=f"/memory/A01_s001_w2_z001_t001_{role}.pkl",
            artifact_type=(ObjectLabelsArtifactType if scenario == "different_kind" and role == "CappedRole" else ImageArtifactType),
            producer_step_index=plan.step_index,
            producer_step_scope_id=("different-step-scope" if scenario == "stale_scope" and role == "CappedRole" else plan.step_scope_id),
            producer_step_name=plan.step_name,
            materialization=MaterializationSpec(ImageFileOptions(
                filename_suffix=".tif",
                filename_identity=MaterializedFilenameIdentity.SOURCE_IDENTITY,
                relative_path_template=(filename if same_persisted_path else filename.replace(".tif", "_independent.tif")),
            )),
        )
        plan.artifact_outputs[output_plan.ref()] = output_plan
        payload = ImageMetadataPayload(
            np.ones((4, 5), dtype=np.float32) * scale,
            ImagePayloadMetadata(
                source_component_metadata=components,
                source_image_names=(role,),
                source_voxel_spacing=SourceVoxelSpacing((0.65, 0.65)),
            ),
        )
        artifact_payload = payload
        if role == "CappedRole" and scenario == "conflicting_metadata":
            artifact_payload = payload.metadata.replace_fields(source_image_names=("IndependentRole",)).payload_with(payload.data)
        if role == "CappedRole" and scenario == "different_kind":
            artifact_payload = SourceImageObjectLabelBuildRequest(
                image=payload, labels=np.ones(payload.data.shape, dtype=np.int32),
                declared_object_count=1, declared_object_ids=(1,),
            ).payload()
        context.runtime_value_store.record(
            RuntimeValue.normalize(output_plan, artifact_payload, axis_id="A01"),
            path=output_plan.path, backend=Backend.MEMORY.value,
        )
        destination = plan.output_dir / filename
        filemanager.save(payload, str(destination), Backend.MEMORY.value)
        filemanager.ensure_directory(plan.output_dir, Backend.DISK.value)
        filemanager.save(payload.data, str(destination), Backend.DISK.value)
        record_output_path(
            context, plan, str(destination), image_metadata=payload.metadata,
            output_context=AlignedImageSliceContext.main_flow(
                output_key=role, artifact_kind=ImageArtifactType.value,
            ),
        )
    saved = RuntimeArtifactMaterializationAuthority.materialize(context, plan)
    assert len(saved) == 2
    target = replace(PrimaryImageMetadataTarget.from_plan(plan), artifact_materializations=saved)
    records = target.produced_records(context, plan)
    artifacts = target.runtime_artifact_projection_paths(context, plan)
    receipt = {
        "source_scope": plan.step_scope_id,
        "produced": [{"path": str(record.path_under(plan.output_dir)),
                      "identity": asdict(record.producer_identity),
                      "address": record.filename_address.as_component_metadata()} for record in records],
        "materialized": [{"path": output.path,
                          "role": item.materialization.output_plan.name,
                          "producer_scope": item.materialization.output_plan.producer_step_scope_id,
                          "stored_key": repr(item.materialization.record.key)}
                         for item in saved for output in item.outputs_for_backend(Backend.DISK.value)],
        "artifact_projections": [{"path": path,
                                 "role": projection.projection_role.value,
                                 "address": projection.address.as_component_metadata(),
                                 "alias": projection.source_alias,
                                 "kind": projection.artifact_kind.value}
                                 for projection, path in artifacts],
    }
    (tmp_path / "persisted-occurrence-witness.json").write_text(json.dumps(receipt, indent=2))
    produced_paths = {item["path"] for item in receipt["produced"]}
    materialized_paths = {item["path"] for item in receipt["materialized"]}
    if same_persisted_path:
        assert produced_paths == materialized_paths
    else:
        assert produced_paths.isdisjoint(materialized_paths)
    expected_sums = {20.0} if scenario == "different_kind" else {20.0, 10.0}
    assert {float(tifffile.imread(item["path"]).sum()) for item in receipt["materialized"]} == expected_sums
    if scenario != "same_occurrence":
        message = "Conflicting metadata for persisted image" if scenario == "conflicting_metadata" else "Duplicate source projection address"
        with pytest.raises(ValueError, match=message) as rejection:
            target.produced_projection_entries(context, plan)
        receipt["rejection"] = str(rejection.value)
        (tmp_path / "persisted-occurrence-witness.json").write_text(json.dumps(receipt, indent=2))
        return
    structured = target.produced_projection_entries(context, plan)
    structured = SourceProjectionMetadataSerializer.projection_fields(
        structured.projection_paths
    )
    assert len(structured["source_projection"]) == 2
    assert {item["source_alias"] for item in structured["source_projection"]} == {"RawRole", "CappedRole"}
    target.write(context, produced_plan=plan)
    document = json.loads((tmp_path / "openhcs_metadata.json").read_text())
    reopened = VirtualWorkspaceSourceProjection.from_openhcs_metadata(tmp_path, document)
    projections = reopened.source_projections_by_virtual_path
    relative_paths = {item["path"].removeprefix(str(tmp_path) + "/") for item in receipt["produced"]}
    assert set(projections) == relative_paths | produced_paths
    assert {projection.source_alias for projection in projections.values()} == {"RawRole", "CappedRole"}
    for relative_path in relative_paths:
        projection = projections[relative_path]
        assert projection.address.as_component_metadata() == {key: components[key] for key in ("well", "site", "channel", "z_index", "timepoint")}
        expected_scale = 1.0 if projection.source_alias == "RawRole" else 0.5
        np.testing.assert_array_equal(tifffile.imread(tmp_path / relative_path), np.ones((4, 5), dtype=np.float32) * expected_scale)
