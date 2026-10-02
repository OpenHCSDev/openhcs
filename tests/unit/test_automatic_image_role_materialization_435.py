"""Default retained image artifacts keep their declared output role identity."""

from dataclasses import replace
from pathlib import Path
import json

import pytest
import numpy as np
import tifffile
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
from polystore.memory import MemoryStorageBackend

from test_function_outputs import context_stub, function_step_plan, record_output_path
from openhcs.constants.constants import Backend, Microscope, VariableComponents
from openhcs.core.aligned_image_payload import AlignedImageSliceContext, ImagePayloadBundleContext
from openhcs.core.artifacts import ArtifactOutputPlan, ArtifactSpec, ImageArtifactType
from openhcs.core.compiled_step_plan import RuntimeArtifactMaterializationPlan
from openhcs.core.pipeline.artifact_planning import ArtifactOutputMaterializationPlanner
from openhcs.core.runtime_artifact_values import RuntimeValue
from openhcs.core.runtime_image_values import ImageMetadataPayload, ImagePayloadMetadata, ImagePayloadMetadataCompositionMode
from openhcs.core.runtime_stores import RuntimeValueStore
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_workspace_projection import VirtualWorkspaceSourceProjection
from openhcs.core.steps.function_output_identity import (
    FunctionOutputIdentityAuthority, FunctionOutputPathAuthority,
)
from openhcs.core.steps.function_outputs import (
    PrimaryImageMetadataTarget, RuntimeArtifactMaterializationAuthority,
)
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser


@pytest.mark.parametrize("plane_count", (1, 2))
def test_automatic_two_role_images_publish_their_actual_saved_occurrences(tmp_path, plane_count):
    filemanager = FileManager({
        Backend.DISK.value: DiskStorageBackend(),
        Backend.MEMORY.value: MemoryStorageBackend(),
    })
    context = context_stub(filemanager, parser=SourceSchemaFilenameParser())
    context.microscope_handler.microscope_type = Microscope.OPENHCS.value
    context.runtime_value_store = RuntimeValueStore()
    context.metadata_cache = {}
    context.tiff_config = None
    plan = function_step_plan(
        "Declared raw and capped roles",
        variable_components=((VariableComponents.Z_INDEX,) if plane_count > 1 else ()),
    )
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
    plans = tuple(
        ArtifactOutputPlan(
            name=name, path=f"/memory/{name}.pkl", artifact_type=ImageArtifactType,
            producer_step_index=plan.step_index,
            producer_step_scope_id=plan.step_scope_id,
            producer_step_name=plan.step_name,
            materialization=ArtifactOutputMaterializationPlanner.materialization_for(
                ArtifactSpec(name=name, artifact_type=ImageArtifactType, plan_type=ArtifactOutputPlan), (),
            ),
        )
        for name in ("raw_body_processing_role", "capped_outgrowth_processing_role")
    )
    plan.artifact_outputs = {output.ref(): output for output in plans}
    contexts = AlignedImageSliceContext.main_flow_for_output_plans(plans)
    expected = {}
    for output, output_context, factor in zip(plans, contexts, (1.0, 0.5), strict=True):
        payloads = tuple(
            ImageMetadataPayload(
                (np.arange(20, dtype=np.float32).reshape(4, 5) + index) * factor,
                ImagePayloadMetadata(
                    source_component_metadata={
                        "well": "A01", "site": "1", "channel": "2", "z_index": str(index),
                        "timepoint": "1", "extension": ".tif",
                    },
                    source_image_names=(output.name,),
                    source_voxel_spacing=SourceVoxelSpacing((1.3556, 1.3556)),
                ),
            )
            for index in range(1, plane_count + 1)
        )
        value = (
            payloads[0] if plane_count == 1 else ImagePayloadBundleContext.from_payloads(
                payloads, metadata_mode=ImagePayloadMetadataCompositionMode.STACK,
            ).compose()
        )
        context.runtime_value_store.record(
            RuntimeValue.normalize(output, value, axis_id="A01"),
            path=output.path, backend=Backend.MEMORY.value,
        )
        expected[output.name] = []
        for payload in payloads:
            identity = FunctionOutputIdentityAuthority.filename_identity_from_metadata(
                context.microscope_handler.parser, payload.metadata,
            ).with_filename_qualifier(output_context.output_key)
            destination = plan.output_dir / FunctionOutputPathAuthority.filename_for_identity(
                context.microscope_handler.parser, identity,
            )
            filemanager.ensure_directory(plan.output_dir, Backend.MEMORY.value)
            filemanager.ensure_directory(plan.output_dir, Backend.DISK.value)
            filemanager.save(payload, str(destination), Backend.MEMORY.value)
            filemanager.save(payload.data, str(destination), Backend.DISK.value)
            record_output_path(
                context, plan, str(destination), output_context=output_context,
                image_metadata=payload.metadata, identity=identity,
            )
            expected[output.name].append((destination, payload.data))
    saved = RuntimeArtifactMaterializationAuthority.materialize(context, plan)
    target = replace(PrimaryImageMetadataTarget.from_plan(plan), artifact_materializations=saved)
    # The original implementation raises its real duplicate projection guard
    # here: both automatic materializations used the same unqualified path.
    structured = target.produced_projection_metadata(context, plan)
    assert {item["source_alias"] for item in structured["source_projection"]} == set(expected)
    assert len(structured["source_projection"]) == 2 * plane_count
    for materialized in saved:
        outputs = materialized.outputs_for_backend(Backend.DISK.value)
        assert len(outputs) == plane_count
        for actual, (path, pixels) in zip(outputs, expected[materialized.materialization.output_plan.name], strict=True):
            assert actual.path == str(path)
            np.testing.assert_array_equal(tifffile.imread(path), pixels)
    target.write(context, produced_plan=plan)
    document = json.loads((tmp_path / "openhcs_metadata.json").read_text())
    reopened = VirtualWorkspaceSourceProjection.from_openhcs_metadata(tmp_path, document)
    for name, expected_planes in expected.items():
        for path, pixels in expected_planes:
            projection = reopened.source_projections_by_virtual_path[str(path.relative_to(tmp_path))]
            assert projection.source_alias == name
            assert projection.address.as_component_metadata()["channel"] == "2"
            assert projection.image_metadata.source_voxel_spacing == SourceVoxelSpacing((1.3556, 1.3556))
            np.testing.assert_array_equal(tifffile.imread(tmp_path / projection.ref.backend_address), pixels)


@pytest.mark.parametrize("purpose", (
    "explicit_source", "explicit_template", "terminal_template",
    "explicit_artifact", "terminal_artifact", "unnamed_terminal",
))
def test_retained_role_policy_preserves_authored_and_unnamed_image_paths(tmp_path, purpose):
    from openhcs.processing.materialization import (
        ImageFileOptions, MaterializationSpec, MaterializedFilenameIdentity,
        TerminalMaterializationSpec, materialization_outputs,
    )

    options = ImageFileOptions(
        filename_suffix=".tif",
        relative_path_template=("authored/plane_{index}.tif" if purpose.endswith("template") else None),
        filename_identity=(
            MaterializedFilenameIdentity.ARTIFACT_NAME if purpose.endswith("artifact")
            else MaterializedFilenameIdentity.SOURCE_IDENTITY
        ),
    )
    spec = (
        TerminalMaterializationSpec(options) if purpose.startswith("terminal") or purpose == "unnamed_terminal"
        else MaterializationSpec(options)
    )
    output_plan = None if purpose == "unnamed_terminal" else ArtifactOutputPlan(
        name="DeclaredRole", path="/memory/DeclaredRole.pkl",
        artifact_type=ImageArtifactType, materialization=spec,
    )
    payloads = tuple(
        ImageMetadataPayload(np.ones((4, 5), dtype=np.float32) * index, ImagePayloadMetadata(
            source_component_metadata={
                "well": "A01", "site": "1", "channel": "2", "z_index": str(index),
                "timepoint": "1", "extension": ".tif",
            },
        ))
        for index in (1, 2)
    )
    value = ImagePayloadBundleContext.from_payloads(
        payloads, metadata_mode=ImagePayloadMetadataCompositionMode.STACK,
    ).compose()
    filemanager = FileManager({Backend.MEMORY.value: MemoryStorageBackend()})
    context = context_stub(filemanager, parser=SourceSchemaFilenameParser())
    outputs = materialization_outputs(
        spec, value, str(tmp_path / "AuthoredBase"), filemanager,
        context=context, output_plan=output_plan,
        variable_components=(VariableComponents.Z_INDEX,),
    )
    expected_paths = (
        ("authored/plane_1.tif", "authored/plane_2.tif") if purpose.endswith("template")
        else ("AuthoredBase.tif",) if purpose.endswith("artifact")
        else ("A01_s001_w2_z001_t001.tif", "A01_s001_w2_z002_t001.tif")
    )
    assert tuple(Path(output.path).relative_to(tmp_path).as_posix() for output in outputs) == expected_paths
    if len(outputs) == 2:
        for actual, expected in zip(outputs, payloads, strict=True):
            np.testing.assert_array_equal(actual.content, expected.data)
    else:
        np.testing.assert_array_equal(outputs[0].content, value.data)


def test_authored_duplicate_template_still_fails_before_any_save(tmp_path):
    from openhcs.processing.materialization import ImageFileOptions, TerminalMaterializationSpec, materialization_outputs

    spec = TerminalMaterializationSpec(ImageFileOptions(
        filename_suffix=".tif", relative_path_template="same.tif",
    ))
    output_plan = ArtifactOutputPlan(name="NamedRole", path="/memory/role.pkl", artifact_type=ImageArtifactType, materialization=spec)
    payloads = tuple(
        ImageMetadataPayload(np.ones((4, 5), dtype=np.float32), ImagePayloadMetadata(
            source_component_metadata={"well": "A01", "site": "1", "channel": "2", "z_index": str(index), "timepoint": "1", "extension": ".tif"},
        )) for index in (1, 2)
    )
    value = ImagePayloadBundleContext.from_payloads(payloads, metadata_mode=ImagePayloadMetadataCompositionMode.STACK).compose()
    manager = FileManager({Backend.MEMORY.value: MemoryStorageBackend()})
    with pytest.raises(ValueError, match="produced duplicate paths"):
        materialization_outputs(spec, value, str(tmp_path / "role"), manager,
                                context=context_stub(manager, parser=SourceSchemaFilenameParser()),
                                output_plan=output_plan)
    assert not (tmp_path / "same.tif").exists()
