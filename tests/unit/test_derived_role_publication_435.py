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
from openhcs.constants.constants import (
    AllComponents, Backend, GroupBy, Microscope, VariableComponents,
)
from openhcs.core.aligned_image_payload import AlignedImageSliceContext, stack_image_payloads
from openhcs.core.artifacts import ArtifactOutputPlan, ImageArtifactType, ObjectLabelsArtifactType
from openhcs.core.component_group_scope import ComponentGroupScope, RuntimeExecutionAxisScope
from openhcs.core.compiled_step_plan import RuntimeArtifactMaterializationPlan
from openhcs.core.runtime_artifact_values import RuntimeValue
from openhcs.core.runtime_image_values import (
    ImageMetadataPayload, ImagePayloadMetadata, ImagePayloadMetadataCompositionMode,
)
from openhcs.core.runtime_stores import RuntimeValueStore
from openhcs.core.runtime_object_label_building import SourceImageObjectLabelBuildRequest
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_projection import SourceProjectionMetadataSerializer
from openhcs.core.source_workspace_projection import VirtualWorkspaceSourceProjection
from openhcs.core.steps.function_outputs import (
    PrimaryImageMetadataTarget, RuntimeArtifactMaterializationAuthority,
)
from openhcs.core.steps.function_output_identity import FunctionOutputIdentity
from openhcs.core.steps.function_runtime import ImageFunctionOutputContextStrategy
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis, RuntimePlaneAxisValueProjection
from openhcs.serialization.json import to_jsonable
from openhcs.processing.materialization import (
    ImageFileOptions, MaterializationSpec, MaterializedFilenameIdentity,
)


@pytest.mark.parametrize("scenario,aggregate", (
    *((scenario, False) for scenario in (
        "same_occurrence", "different_path", "stale_scope", "conflicting_metadata", "different_kind",
    )),
    *((scenario, True) for scenario in (
        "same_occurrence", "different_path", "stale_scope", "conflicting_metadata", "different_kind",
    )),
    ("conflicting_scope", True),
))
def test_saved_roles_publish_once_per_persisted_occurrence(tmp_path, scenario, aggregate):
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
    roles = (("RawRole", 1.0), ("CappedRole", 0.5))
    if aggregate:
        components.update(channel="1", z_index="0")
        plan.variable_components = (VariableComponents.Z_INDEX,)
        plan.group_by = GroupBy.CHANNEL
        plan.execution_group_scope = ComponentGroupScope.from_raw(
            ("1",), component=AllComponents.CHANNEL,
        )
        source_planes = []
        source_dir = tmp_path / "physical_source"
        filemanager.ensure_directory(source_dir, Backend.DISK.value)
        pixels = np.arange(140, dtype=np.uint16).reshape((4, 5, 7))
        for z_index, plane in enumerate(pixels):
            path = source_dir / f"A01_s001_w1_z{z_index:03d}_t001.tif"
            filemanager.save(plane, str(path), Backend.DISK.value)
            source_planes.append(ImagePayloadMetadata(
                source_path=str(path),
                source_component_metadata={**components, "z_index": str(z_index)},
                source_voxel_spacing=SourceVoxelSpacing((2.0, 0.65, 0.65)),
            ).payload_with(filemanager.load(str(path), Backend.DISK.value)))
        source_stack = stack_image_payloads(
            source_planes, metadata_mode=ImagePayloadMetadataCompositionMode.STACK,
        )
        roles = (("fixture_image_494", 1.0),)
    for role, scale in roles:
        tested_role = aggregate or role == "CappedRole"
        filename = (
            f"A01_s001_w{components['channel']}"
            f"_z{int(components['z_index']):03d}_t001_{role}.tif"
        )
        output_plan = ArtifactOutputPlan(
            name=role, path=f"/memory/{filename.removesuffix('.tif')}.pkl",
            artifact_type=(
                ObjectLabelsArtifactType
                if scenario == "different_kind" and tested_role else ImageArtifactType
            ),
            producer_step_index=plan.step_index,
            producer_step_scope_id=(
                "different-step-scope"
                if scenario == "stale_scope" and tested_role else plan.step_scope_id
            ),
            producer_step_name=plan.step_name,
            materialization=MaterializationSpec(ImageFileOptions(
                filename_suffix=".tif",
                filename_identity=(
                    MaterializedFilenameIdentity.ARTIFACT_NAME if aggregate
                    else MaterializedFilenameIdentity.SOURCE_IDENTITY
                ),
                relative_path_template=(filename if same_persisted_path else filename.replace(".tif", "_independent.tif")),
            )),
        )
        if aggregate:
            output_plan = replace(
                output_plan, group_keys=("1",), group_component=AllComponents.CHANNEL,
                variable_components=(AllComponents.Z_INDEX,),
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
        if aggregate:
            payload = ImageFunctionOutputContextStrategy().contextualize(
                source_stack, pixels.copy(), output_plan,
                RuntimePlaneAxisValueProjection(RuntimePlaneAxis.RUNTIME_SLICE, (), None, 4),
            )
        if aggregate:
            execution_scope = RuntimeExecutionAxisScope.from_raw(
                "A01", component=AllComponents.CHANNEL, value="1",
                fixed_component_values=(
                    (AllComponents.SITE, "1"), (AllComponents.TIMEPOINT, "1"),
                ),
            )
            payload = RuntimeValue.normalize_for_execution_scope(
                replace(output_plan, artifact_type=ImageArtifactType), payload,
                execution_scope=execution_scope,
            ).data
        artifact_payload = payload
        if tested_role and scenario == "conflicting_metadata":
            conflicting_fields = (
                {"source_voxel_spacing": SourceVoxelSpacing((3.0, 0.65, 0.65))}
                if aggregate else {"source_image_names": ("IndependentRole",)}
            )
            artifact_payload = payload.metadata.replace_fields(
                **conflicting_fields
            ).payload_with(payload.data)
        if tested_role and scenario == "different_kind":
            artifact_payload = SourceImageObjectLabelBuildRequest(
                image=payload, labels=np.ones(payload.data.shape, dtype=np.int32),
                declared_object_count=1, declared_object_ids=(1,),
            ).payload()
        output_identity = (
            FunctionOutputIdentity.from_metadata(
                context.microscope_handler.parser, payload.metadata,
                variable_components=plan.variable_components,
            ) if aggregate else None
        )
        value = (
            RuntimeValue.normalize_for_execution_scope(
                output_plan, artifact_payload,
                execution_scope=(
                    RuntimeExecutionAxisScope.from_raw(
                        "A01", component=AllComponents.CHANNEL, value="1",
                        fixed_component_values=(
                            (AllComponents.SITE, "2"), (AllComponents.TIMEPOINT, "1"),
                        ),
                    ) if scenario == "conflicting_scope" else execution_scope
                ),
            ) if aggregate else RuntimeValue.normalize(output_plan, artifact_payload, axis_id="A01")
        )
        context.runtime_value_store.record(
            value,
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
            identity=output_identity,
        )
    saved = RuntimeArtifactMaterializationAuthority.materialize(context, plan)
    assert len(saved) == len(roles)
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
                                 "address": None if projection.address is None else projection.address.as_component_metadata(),
                                 "alias": projection.source_alias,
                                 "kind": projection.artifact_kind.value}
                                 for projection, path in artifacts],
        "pre_join_main_flow": SourceProjectionMetadataSerializer.projection_records(
            replace(target, artifact_materializations=()).produced_projection_entries(context, plan).projection_paths,
        ),
        "pre_join_artifacts": SourceProjectionMetadataSerializer.projection_records(artifacts),
        "produced_records": [to_jsonable(record) for record in records],
    }
    (tmp_path / "persisted-occurrence-witness.json").write_text(json.dumps(receipt, indent=2))
    produced_paths = {item["path"] for item in receipt["produced"]}
    materialized_paths = {item["path"] for item in receipt["materialized"]}
    if same_persisted_path:
        assert produced_paths == materialized_paths
    else:
        assert produced_paths.isdisjoint(materialized_paths)
    if aggregate:
        expected_sums = {140.0} if scenario == "different_kind" else {float(pixels.sum())}
    else:
        expected_sums = {20.0} if scenario == "different_kind" else {20.0, 10.0}
    assert {float(tifffile.imread(item["path"]).sum()) for item in receipt["materialized"]} == expected_sums
    if scenario != "same_occurrence" and not (aggregate and scenario == "different_path"):
        message = (
            "Conflicting metadata for persisted image"
            if scenario in ("conflicting_metadata", "conflicting_scope")
            else "Duplicate source projection address"
        )
        with pytest.raises(ValueError, match=message) as rejection:
            target.produced_projection_entries(context, plan)
        receipt["rejection"] = str(rejection.value)
        (tmp_path / "persisted-occurrence-witness.json").write_text(json.dumps(receipt, indent=2))
        return
    if aggregate:
        (main_flow,) = receipt["pre_join_main_flow"]
        (artifact,) = receipt["pre_join_artifacts"]
        assert main_flow["address"] is artifact["address"] is None
        assert main_flow["execution_scope"] == artifact["execution_scope"] == {
            "axis_id": "A01", "component": "channel", "value": "1",
            "fixed_component_values": [["site", "1"], ["timepoint", "1"]],
        }
        assert main_flow["image_metadata"] == artifact["image_metadata"]
        assert main_flow["source_metadata"] == artifact["source_metadata"]
        assert receipt["produced"][0]["address"]["z_index"] == "0"
        assert "z_index" not in receipt["produced_records"][0]["component_values"]
        metadata = main_flow["image_metadata"]
        assert metadata["source_dtype"] == "uint16"
        assert metadata["source_voxel_spacing"] == {
            "values_zyx": [2.0, 0.65, 0.65], "unit": "micrometers",
        }
        provenance = metadata["source_provenance"]
        assert "z_index" not in provenance["source_component_metadata"]
        assert [plane["component_metadata"]["z_index"] for plane in
                provenance["source_image_provenance_planes"]] == ["0", "1", "2", "3"]
        assert [plane["path"] for plane in provenance["source_image_provenance_planes"]] == [
            str(source_dir / f"A01_s001_w1_z{z_index:03d}_t001.tif") for z_index in range(4)
        ]
        assert metadata["source_spatial_domain"]["spatial_dimensions"] == 2
        for path in produced_paths | materialized_paths:
            image = tifffile.imread(path)
            assert image.dtype == np.uint16
            np.testing.assert_array_equal(image, pixels)
    structured = target.produced_projection_entries(context, plan)
    structured = SourceProjectionMetadataSerializer.projection_fields(
        structured.projection_paths
    )
    occurrence_count = 2 if aggregate and scenario == "different_path" else 1
    assert len(structured["source_projection"]) == len(roles) * occurrence_count
    assert {item["source_alias"] for item in structured["source_projection"]} == {role for role, _ in roles}
    target.write(context, produced_plan=plan)
    document = json.loads((tmp_path / "openhcs_metadata.json").read_text())
    reopened = VirtualWorkspaceSourceProjection.from_openhcs_metadata(tmp_path, document)
    projections = reopened.source_projections_by_virtual_path
    relative_paths = {path.removeprefix(str(tmp_path) + "/") for path in produced_paths | materialized_paths}
    assert set(projections) == relative_paths | produced_paths | materialized_paths
    assert {projection.source_alias for projection in projections.values()} == {role for role, _ in roles}
    for relative_path in relative_paths:
        projection = projections[relative_path]
        if aggregate:
            assert projection.address is None
            np.testing.assert_array_equal(tifffile.imread(tmp_path / relative_path), pixels)
            continue
        assert projection.address.as_component_metadata() == {key: components[key] for key in ("well", "site", "channel", "z_index", "timepoint")}
        expected_scale = 1.0 if projection.source_alias == "RawRole" else 0.5
        np.testing.assert_array_equal(tifffile.imread(tmp_path / relative_path), np.ones((4, 5), dtype=np.float32) * expected_scale)
