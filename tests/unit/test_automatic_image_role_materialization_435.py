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
from openhcs.core.source_projection import SourceProjectionMetadataSerializer
from openhcs.core.source_workspace_projection import VirtualWorkspaceSourceProjection
from openhcs.core.steps.function_output_identity import (
    FunctionOutputIdentity,
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
            identity = FunctionOutputIdentity.from_filename_metadata(
                context.microscope_handler.parser, payload.metadata,
            ).with_filename_qualifier(output_context.output_key)
            destination = plan.output_dir / identity.filename(context.microscope_handler.parser)
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
    structured = target.produced_projection_entries(context, plan)
    structured = SourceProjectionMetadataSerializer.projection_fields(
        structured.projection_paths
    )
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
    "explicit_artifact", "terminal_artifact", "unnamed_terminal", "unnamed_explicit",
    "explicit_source_declared_terminal", "terminal_source_declared_explicit",
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
    declared_spec = (
        TerminalMaterializationSpec(options) if purpose == "explicit_source_declared_terminal"
        else MaterializationSpec(options) if purpose == "terminal_source_declared_explicit"
        else spec
    )
    output_plan = None if purpose in ("unnamed_terminal", "unnamed_explicit") else ArtifactOutputPlan(
        name="DeclaredRole", path="/memory/DeclaredRole.pkl",
        artifact_type=ImageArtifactType, materialization=declared_spec,
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
        else ("A01_s001_w2_z001_t001_DeclaredRole.tif", "A01_s001_w2_z002_t001_DeclaredRole.tif") if purpose == "terminal_source_declared_explicit"
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


@pytest.mark.parametrize("suffix", (".tif", ".png", ".ome.tif", ".labels.tif"))
@pytest.mark.parametrize("plane_count", (1, 2))
def test_retained_image_qualifier_respects_complete_writer_suffix(tmp_path, suffix, plane_count):
    from openhcs.core.steps.function_artifact_materialization import RuntimeArtifactMaterialization
    from openhcs.processing.materialization import ImageFileOptions, TerminalMaterializationSpec

    manager = FileManager({Backend.MEMORY.value: MemoryStorageBackend()})
    context = context_stub(manager, parser=SourceSchemaFilenameParser())
    plan = function_step_plan("Retained format role", variable_components=(VariableComponents.Z_INDEX,) if plane_count > 1 else ())
    plan.output_dir = tmp_path / "images"
    plan.analysis_results_dir = str(plan.output_dir)
    output_plan = ArtifactOutputPlan(
        name="Role Name", path="/memory/role.pkl", artifact_type=ImageArtifactType,
        materialization=TerminalMaterializationSpec(ImageFileOptions(filename_suffix=suffix)),
    )
    payloads = tuple(
        ImageMetadataPayload(np.ones((4, 5), dtype=np.uint8) * index, ImagePayloadMetadata(
            source_component_metadata={"well": "A01", "site": "1", "channel": "2", "z_index": str(index), "timepoint": "1", "extension": ".tif"},
        )) for index in range(1, plane_count + 1)
    )
    value = payloads[0] if plane_count == 1 else ImagePayloadBundleContext.from_payloads(
        payloads, metadata_mode=ImagePayloadMetadataCompositionMode.STACK,
    ).compose()
    store = RuntimeValueStore()
    record = store.record(RuntimeValue.normalize(output_plan, value, axis_id="A01"), path=output_plan.path, backend=Backend.MEMORY.value)
    outputs = RuntimeArtifactMaterialization.from_record(
        output_plan=output_plan, record=record, plan=plan, context=context,
    ).outputs(plan, context)
    assert len(outputs) == plane_count
    for index, (output, payload) in enumerate(zip(outputs, payloads, strict=True), 1):
        identity = FunctionOutputIdentity.from_filename_metadata(
            context.microscope_handler.parser, payload.metadata,
        ).with_filename_qualifier(output_plan.name)
        expected = replace(identity, extension=suffix).filename(context.microscope_handler.parser)
        assert Path(output.path).name == expected
        assert Path(output.path).name.endswith("_Role_Name" + suffix)
        assert output.metadata.source_component_metadata["channel"] == "2"
        assert output.metadata.source_component_metadata["z_index"] == str(index)
        np.testing.assert_array_equal(output.content, payload.data)


def test_distinct_aliases_that_normalize_to_one_filename_still_conflict(tmp_path):
    from openhcs.core.steps.function_artifact_materialization import RuntimeArtifactMaterialization
    from openhcs.processing.materialization import ImageFileOptions, TerminalMaterializationSpec

    manager = FileManager({Backend.MEMORY.value: MemoryStorageBackend()})
    context = context_stub(manager, parser=SourceSchemaFilenameParser())
    plan = function_step_plan("Ambiguous role spelling")
    plan.output_dir = tmp_path / "images"
    plan.analysis_results_dir = str(plan.output_dir)
    value = ImageMetadataPayload(np.ones((4, 5), dtype=np.float32), ImagePayloadMetadata(
        source_component_metadata={"well": "A01", "site": "1", "channel": "2", "z_index": "1", "timepoint": "1", "extension": ".tif"},
    ))
    paths = []
    store = RuntimeValueStore()
    for name in ("a/b", "a b"):
        output_plan = ArtifactOutputPlan(name=name, path=f"/memory/{name}.pkl", artifact_type=ImageArtifactType,
                                        materialization=TerminalMaterializationSpec(ImageFileOptions(filename_suffix=".tif")))
        record = store.record(RuntimeValue.normalize(output_plan, value, axis_id="A01"), path=output_plan.path, backend=Backend.MEMORY.value)
        outputs = RuntimeArtifactMaterialization.from_record(output_plan=output_plan, record=record, plan=plan, context=context).outputs(plan, context)
        paths.append(outputs[0].path)
    assert paths[0] == paths[1]
    # Existing main-flow destination authority rejects this declared naming
    # collision instead of choosing a new suffix or inventing a channel.
    from openhcs.core.steps.function_output_identity import FunctionOutputIdentity
    with pytest.raises(ValueError, match="duplicate"):
        FunctionOutputIdentity.validate_output_paths(paths, input_paths=[], step_name=plan.step_name, pattern_repr="declared roles")


def test_batch_binds_actual_purpose_once_without_rewriting_plan_or_source(monkeypatch, tmp_path):
    from openhcs.processing.materialization import ImageFileOptions, MaterializationSpec, TerminalMaterializationSpec
    from openhcs.processing.materialization.constants import MaterializationFormat
    from openhcs.processing.materialization.core import MaterializationBatch, MaterializationContext, Output, WriterSpec, _WRITERS_BY_OPTIONS

    options = ImageFileOptions(filename_suffix=".tif")
    declared = TerminalMaterializationSpec(options)
    explicit = MaterializationSpec(options)
    plan = ArtifactOutputPlan(name="Role", path="/memory/role", artifact_type=ImageArtifactType, materialization=declared)
    manager = FileManager({Backend.MEMORY.value: MemoryStorageBackend()})
    source = {"physical_source": "original"}
    context = MaterializationContext(
        base_path=str(tmp_path / "role"), backends=[], backend_kwargs={},
        filemanager=manager, extra_inputs=source, output_plan=plan,
        materialization_spec=declared,
    )
    seen = []
    def custom_writer(data, actual_options, actual_context):
        assert actual_options is options
        assert actual_context.output_plan is plan
        assert actual_context.extra_inputs is source
        seen.append(actual_context)
        return [Output(path=str(tmp_path / "custom.tif"), content=data)]
    monkeypatch.setitem(_WRITERS_BY_OPTIONS, ImageFileOptions, WriterSpec(
        format=MaterializationFormat.IMAGE_FILE, options_type=ImageFileOptions,
        write=custom_writer, primary_path=lambda outputs: outputs[0].path,
        candidate_paths=lambda _options, base: (base,),
    ))
    pixels = np.ones((4, 5), dtype=np.float32)
    first = MaterializationBatch.render(explicit, pixels, context)
    second = MaterializationBatch.render(declared, pixels, first.context)
    assert seen == [first.context, second.context]
    assert seen[0] is first.context and seen[1] is second.context
    assert first.context.materialization_spec is explicit
    assert second.context.materialization_spec is declared
    assert context.materialization_spec is declared
    assert plan.materialization is declared
    assert source == {"physical_source": "original"}


def test_direct_image_writer_without_purpose_binding_retains_legacy_source_path(tmp_path):
    from openhcs.processing.materialization import ImageFileOptions, TerminalMaterializationSpec
    from openhcs.processing.materialization.core import MaterializationContext, write_image_file

    options = ImageFileOptions(filename_suffix=".tif")
    plan = ArtifactOutputPlan(name="Role", path="/memory/role", artifact_type=ImageArtifactType,
                              materialization=TerminalMaterializationSpec(options))
    manager = FileManager({Backend.MEMORY.value: MemoryStorageBackend()})
    value = ImageMetadataPayload(np.ones((4, 5), dtype=np.float32), ImagePayloadMetadata(
        source_component_metadata={"well": "A01", "site": "1", "channel": "2", "z_index": "1", "timepoint": "1", "extension": ".tif"},
    ))
    context = MaterializationContext(base_path=str(tmp_path / "role"), backends=[], backend_kwargs={},
                                     filemanager=manager, extra_inputs={}, output_plan=plan,
                                     context=context_stub(manager, parser=SourceSchemaFilenameParser()))
    outputs = write_image_file(value, options, context)
    assert Path(outputs[0].path).name == "A01_s001_w2_z001_t001.tif"
    assert context.materialization_spec is None
    assert context.output_plan is plan
    np.testing.assert_array_equal(outputs[0].content, value.data)


@pytest.mark.parametrize("purpose", ("named_terminal", "explicit", "unnamed_terminal"))
def test_parser_free_render_requires_parser_only_for_automatic_named_role(tmp_path, purpose):
    from openhcs.processing.materialization import ImageFileOptions, MaterializationSpec, TerminalMaterializationSpec, materialization_outputs

    options = ImageFileOptions(filename_suffix=".tif")
    spec = MaterializationSpec(options) if purpose == "explicit" else TerminalMaterializationSpec(options)
    plan = None if purpose == "unnamed_terminal" else ArtifactOutputPlan(
        name="Role", path="/memory/role", artifact_type=ImageArtifactType, materialization=spec,
    )
    manager = FileManager({Backend.MEMORY.value: MemoryStorageBackend()})
    value = ImageMetadataPayload(np.ones((4, 5), dtype=np.float32), ImagePayloadMetadata(
        source_path="/physical/OriginalSource.tif",
    ))
    if purpose == "named_terminal":
        with pytest.raises(ValueError, match="Parser-backed source-stem authority requires a parser"):
            materialization_outputs(spec, value, str(tmp_path / "Role"), manager, output_plan=plan)
    else:
        outputs = materialization_outputs(spec, value, str(tmp_path / "Role"), manager, output_plan=plan)
        assert Path(outputs[0].path).name == "OriginalSource.tif"
        np.testing.assert_array_equal(outputs[0].content, value.data)
    assert value.metadata.source_path == "/physical/OriginalSource.tif"
