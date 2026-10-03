"""Public same-path image publication controls; the original #494 pair is unknown."""

from dataclasses import fields, replace
from pathlib import Path
import json

import numpy as np
import pytest
import tifffile

from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
from polystore.memory import MemoryStorageBackend

from openhcs.constants.constants import Backend, Microscope
from openhcs.core.aligned_image_payload import AlignedImageSliceContext
from openhcs.core.artifacts import (
    ArtifactOutputPlan,
    ImageArtifactType,
    ObjectLabelsArtifactType,
)
from openhcs.core.compiled_step_plan import RuntimeArtifactMaterializationPlan
from openhcs.core.runtime_artifact_values import RuntimeValue
from openhcs.core.runtime_image_values import ImageMetadataPayload, ImagePayloadMetadata
from openhcs.core.runtime_stores import RuntimeValueStore
from openhcs.core.source_image_provenance import (
    SourceImageProvenance,
    SourceImageProvenancePlanes,
)
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_projection import (
    OpenHCSPlaneAddress,
    SourcePixelRef,
    SourcePlaneProjection,
    SourceProjectionSet,
    SourceProjectionMetadataSerializer,
)
from openhcs.core.source_workspace_projection import VirtualWorkspaceSourceProjection
from openhcs.core.steps.function_output_identity import FunctionOutputIdentity
from openhcs.core.steps.function_outputs import (
    PrimaryImageMetadataTarget,
    RuntimeArtifactMaterializationAuthority,
)
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser
from openhcs.processing.materialization import (
    ImageFileOptions,
    MaterializationSpec,
    MaterializedFilenameIdentity,
)

from tests.unit.test_function_outputs import (
    context_stub,
    function_step_plan,
    record_output_path,
)


def _actual_saved_occurrence(tmp_path, scenario):
    filemanager = FileManager(
        {
            Backend.DISK.value: DiskStorageBackend(),
            Backend.MEMORY.value: MemoryStorageBackend(),
        }
    )
    context = context_stub(filemanager, parser=SourceSchemaFilenameParser())
    context.microscope_handler.microscope_type = Microscope.OPENHCS.value
    context.runtime_value_store = RuntimeValueStore()
    context.metadata_cache = {}
    context.tiff_config = None
    plan = function_step_plan("Collapsed public mosaic")
    plan.streaming_configs = {}
    plan.write_backend = Backend.DISK.value
    plan.output_plate_root = str(tmp_path)
    plan.output_dir = tmp_path / "images"
    plan.sub_dir = "images"
    plan.analysis_results_dir = str(plan.output_dir)
    plan.runtime_artifact_materialization = RuntimeArtifactMaterializationPlan(
        persistent_enabled=True,
        persistent_backend=Backend.DISK.value,
    )
    context.step_plans = {plan.step_index: plan}
    filename = "A01_s001_w1_z001_t001_Mosaic.tif"
    output_plan = ArtifactOutputPlan(
        name="Mosaic",
        path="/memory/Mosaic.pkl",
        artifact_type=ImageArtifactType,
        producer_step_index=plan.step_index,
        producer_step_scope_id=plan.step_scope_id,
        producer_step_name=plan.step_name,
        materialization=MaterializationSpec(
            ImageFileOptions(
                filename_suffix=".tif",
                filename_identity=MaterializedFilenameIdentity.ARTIFACT_NAME,
                relative_path_template=filename,
            )
        ),
    )
    plan.artifact_outputs[output_plan.ref()] = output_plan
    semantic_components = {
        "well": "A01",
        "channel": "1",
        "z_index": "1",
        "timepoint": "1",
    }
    if scenario != "collapsed_site":
        semantic_components["site"] = "1"
    provenance = SourceImageProvenance(
        source_component_metadata=semantic_components,
        source_image_provenance_planes=(
            SourceImageProvenancePlanes.from_contributor_components(
                paths=("/source/site-1.tif", "/source/site-2.tif"),
                component_metadata=({"site": "1"}, {"site": "2"}),
            )
            if scenario == "collapsed_site"
            else SourceImageProvenancePlanes()
        ),
        source_image_names=("Mosaic",),
    )
    metadata = ImagePayloadMetadata(
        source_provenance=provenance,
        source_voxel_spacing=SourceVoxelSpacing((0.5, 0.5)),
    )
    pixels = np.arange(
        40 if scenario == "collapsed_site" else 20, dtype=np.uint16
    ).reshape((2, 4, 5) if scenario == "collapsed_site" else (4, 5))
    payload = ImageMetadataPayload(pixels, metadata)
    artifact_payload = payload
    if scenario == "metadata_conflict":
        artifact_payload = metadata.replace_fields(
            source_image_names=("IndependentRole",),
        ).payload_with(pixels)
    elif scenario == "scalar_address_conflict":
        artifact_payload = metadata.with_source_component_metadata(
            {**semantic_components, "site": "2"},
        ).payload_with(pixels)
    context.runtime_value_store.record(
        RuntimeValue.normalize(output_plan, artifact_payload, axis_id="A01"),
        path=output_plan.path,
        backend=Backend.MEMORY.value,
    )
    destination = plan.output_dir / filename
    filemanager.ensure_directory(plan.output_dir, Backend.MEMORY.value)
    filemanager.ensure_directory(plan.output_dir, Backend.DISK.value)
    filemanager.save(payload, str(destination), Backend.MEMORY.value)
    filemanager.save(pixels, str(destination), Backend.DISK.value)
    record_output_path(
        context,
        plan,
        destination,
        image_metadata=metadata,
        output_context=AlignedImageSliceContext.main_flow(
            output_key="Mosaic",
            artifact_kind=ImageArtifactType.value,
        ),
        identity=FunctionOutputIdentity(
            component_values=semantic_components,
            filename_component_values={**semantic_components, "site": "1"},
            extension=".tif",
            source="original collapsed-mosaic declaration",
        ),
    )
    target = PrimaryImageMetadataTarget.from_plan(plan)
    # This is the existing accepted main-flow publication, before a mirror is added.
    original = target.produced_projection_metadata(context, plan)
    assert len(original["source_projection"]) == 1
    if scenario == "collapsed_site":
        row = original["source_projection"][0]
        assert row["address"]["site"] == "1"
        assert "site" not in row["source_metadata"]
    saved = RuntimeArtifactMaterializationAuthority.materialize(context, plan)
    assert len(saved) == 1
    (output,) = saved[0].outputs_for_backend(Backend.DISK.value)
    assert output.path == str(destination)
    persisted = tifffile.imread(destination)
    np.testing.assert_array_equal(persisted, pixels)
    assert persisted.dtype == pixels.dtype
    return (
        context,
        plan,
        replace(target, artifact_materializations=saved),
        output_plan,
        pixels,
    )


def _rejected_original_pair(error):
    """Read actual operands from the raising frame; do not copy the join algorithm."""
    frames = []
    traceback = error.__traceback__
    while traceback is not None:
        frame = traceback.tb_frame
        if (
            frame.f_code.co_name == "project_runtime_artifacts"
            and frame.f_code.co_filename.endswith(
                "/openhcs/core/steps/function_outputs.py"
            )
        ):
            frames.append(frame.f_locals.copy())
        traceback = traceback.tb_next
    assert len(frames) == 1
    return frames[0]


@pytest.mark.parametrize(
    "scenario",
    (
        "scalar_address_conflict",
        "metadata_conflict",
    ),
)
def test_real_same_path_join_observes_original_rejected_pair(tmp_path, scenario):
    context, plan, target, _output_plan, pixels = _actual_saved_occurrence(
        tmp_path, scenario
    )
    with pytest.raises(
        ValueError, match="Conflicting metadata for persisted image occurrence"
    ) as failure:
        target.produced_projection_metadata(context, plan)
    pair = _rejected_original_pair(failure.value)
    projection = pair["projection"]
    metadata = pair["metadata"]
    assert pair["record"].owns_persisted_artifact(
        pair["materialization"].output_plan,
        pair["destination"],
        target.output_dir,
    )
    # Comparisons below are post-exception observations, not admission replacements.
    address_equal = projection.address == pair["address"]
    metadata_equal = projection.image_metadata == metadata
    differing_fields = [
        member.name
        for member in fields(projection.image_metadata)
        if getattr(projection.image_metadata, member.name)
        != getattr(metadata, member.name)
    ]
    witness = {
        "scenario": scenario,
        "exception": str(failure.value),
        "manifest_address": projection.address.as_component_metadata(),
        "artifact_address": (
            None if pair["address"] is None else pair["address"].as_component_metadata()
        ),
        "address_equal": address_equal,
        "metadata_equal": metadata_equal,
        "differing_fields": differing_fields,
    }
    (tmp_path / "actual-rejected-pair.json").write_text(json.dumps(witness, indent=2))
    if scenario == "metadata_conflict":
        assert address_equal
        assert not metadata_equal
        assert differing_fields == ["source_provenance"]
    else:
        assert not address_equal
        assert not metadata_equal
        assert differing_fields == ["source_provenance"]
        assert pair["address"].as_component_metadata()["site"] == "2"
    np.testing.assert_array_equal(pair["output"].content, pixels)


def test_real_scalar_same_path_mirror_remains_admissible(tmp_path):
    context, plan, target, _output_plan, _pixels = _actual_saved_occurrence(
        tmp_path, "scalar"
    )
    structured = target.produced_projection_metadata(context, plan)
    assert len(structured["source_projection"]) == 1
    assert structured["source_projection"][0]["source_alias"] == "Mosaic"


@pytest.mark.parametrize("mismatch", ("alias", "kind", "scope", "path"))
def test_actual_producer_occurrence_never_matches_foreign_declaration(
    tmp_path, mismatch
):
    context, plan, target, output_plan, _pixels = _actual_saved_occurrence(
        tmp_path, "scalar"
    )
    (record,) = target.produced_records(context, plan)
    destination = record.path_under(target.output_dir)
    assert record.owns_persisted_artifact(output_plan, destination, target.output_dir)
    if mismatch == "path":
        destination = str(target.output_dir / "independent.tif")
    else:
        change = {
            "alias": {"name": "IndependentRole"},
            "kind": {"artifact_type": ObjectLabelsArtifactType},
            "scope": {"producer_step_scope_id": "independent-step-scope"},
        }[mismatch]
        output_plan = replace(output_plan, **change)
    assert not record.owns_persisted_artifact(
        output_plan, destination, target.output_dir
    )


def test_collapsed_same_path_mirror_retains_filename_and_semantic_views(tmp_path):
    context, plan, target, _output_plan, pixels = _actual_saved_occurrence(
        tmp_path, "collapsed_site"
    )
    structured = target.produced_projection_metadata(context, plan)
    (row,) = structured["source_projection"]
    assert row["address"]["site"] == "1"
    assert row["source_alias"] == "Mosaic"
    assert "site" not in row["source_metadata"]
    metadata = ImagePayloadMetadata.from_mapping(
        row[SourceProjectionMetadataSerializer.IMAGE_METADATA_FIELD]
    )
    assert "site" not in metadata.source_component_metadata
    assert len(metadata.source_provenance.represented_source_identities) == 2
    assert metadata.source_voxel_spacing == SourceVoxelSpacing((0.5, 0.5))
    assert metadata.plane_axis is None
    target.write(context, produced_plan=plan)
    document = json.loads((tmp_path / "openhcs_metadata.json").read_text())
    reopened = VirtualWorkspaceSourceProjection.from_openhcs_metadata(
        tmp_path, document
    )
    projection = reopened.source_projections_by_virtual_path[row["virtual_path"]]
    assert projection.address.as_component_metadata()["site"] == "1"
    assert "site" not in projection.image_metadata.source_component_metadata
    assert (
        len(projection.image_metadata.source_provenance.represented_source_identities)
        == 2
    )
    np.testing.assert_array_equal(
        tifffile.imread(tmp_path / row["virtual_path"]), pixels
    )


def test_standalone_collapsed_artifact_keeps_semantic_optional_address(tmp_path):
    context, plan, target, _output_plan, _pixels = _actual_saved_occurrence(
        tmp_path, "collapsed_site"
    )
    ((projection, _path),) = target.project_runtime_artifacts(context, plan)
    assert projection.address is None
    assert projection.execution_scope is not None
    assert "site" not in projection.image_metadata.source_component_metadata
    assert (
        len(projection.image_metadata.source_provenance.represented_source_identities)
        == 2
    )
    assert SourceProjectionSet((projection,)).artifact_projections == (projection,)


@pytest.mark.parametrize("valid_address", (True, False))
def test_supplied_projection_map_must_retain_the_manifest_filename_address(
    tmp_path, valid_address
):
    context, plan, target, output_plan, _pixels = _actual_saved_occurrence(
        tmp_path, "scalar"
    )
    (record,) = target.produced_records(context, plan)
    destination = record.path_under(target.output_dir)
    (payload,) = context.filemanager.load_batch((destination,), Backend.MEMORY.value)
    metadata = target.persisted_image_metadata(
        context, destination=destination, payload=payload
    )
    address = record.filename_address
    if not valid_address:
        address = OpenHCSPlaneAddress.from_complete_source_metadata(
            {**address.as_component_metadata(), "site": "2"},
        )
    projection = SourcePlaneProjection(
        address=address,
        ref=SourcePixelRef(
            Backend.DISK.value, str(Path(destination).relative_to(tmp_path))
        ),
        source_alias=record.output_context.persisted_source_alias,
        source_metadata=metadata.source_component_metadata,
        image_metadata=metadata,
    )
    assert record.owns_persisted_artifact(output_plan, destination, target.output_dir)
    supplied = {Path(destination): (record, projection)}
    if valid_address:
        assert (
            target.project_runtime_artifacts(
                context, plan, produced_projections=supplied
            )
            == ()
        )
    else:
        with pytest.raises(
            ValueError, match="Conflicting metadata for persisted image occurrence"
        ):
            target.project_runtime_artifacts(
                context, plan, produced_projections=supplied
            )
