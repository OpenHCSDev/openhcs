"""Lightweight ownership/payload checks; these do not execute segmentation."""

import ast
from pathlib import Path
import subprocess
from typing import NamedTuple, get_args

import numpy as np
import pytest

from openhcs.core.artifacts import (
    ArtifactSidecarRole,
    ArtifactSidecarSourceRelation,
    ArtifactSpec,
    ArtifactViewerStreaming,
    ImageArtifactType,
    ObjectLabelsArtifactType,
)
from openhcs.core.runtime_image_values import ImagePayloadMetadata, MaskedImagePayload
from openhcs.core.runtime_object_label_building import SourceImageObjectLabelBuildRequest
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.processing.backends.cellprofiler.primary_object_diagnostics import (
    ExecutedDeclumpingEvidence,
    PrimaryObjectDiagnosticPlanes,
    PrimaryObjectsRuntimeTuple,
    SelectedDiagnosticPlaneImageOutput,
    UnexecutedDeclumpingEvidence,
)
from openhcs.processing.materialization import (
    ImageFileOptions,
    MaterializedFilenameIdentity,
)


def _source():
    image = np.arange(30, dtype=np.float32).reshape(5, 6)
    mask = np.ones_like(image, dtype=bool)
    mask[0] = False
    return MaskedImagePayload(
        image,
        mask,
        ImagePayloadMetadata(
            source_path="/synthetic/A01_s001_DNA.tif",
            source_image_names=("DNA",),
            source_spatial_domain=SourceSpatialDomain(
                origin_yx=(40, 80), source_shape_yx=(100, 120)
            ),
            intensity_scale=65535,
        ),
    )


def _objects(source):
    labels = np.zeros(source.data.shape, dtype=np.int32)
    labels[2, 3] = 1
    unedited = labels.copy()
    unedited[1, 1] = 2
    small_removed = unedited.copy()
    small_removed[1, 1] = 0
    return SourceImageObjectLabelBuildRequest(
        image=source,
        labels=labels,
        unedited_labels=unedited,
        small_removed_labels=small_removed,
        declared_object_count=1,
    ).payload()


def test_selected_response_keeps_source_frame_without_acquisition_intensity_scale():
    from openhcs.core.runtime_plane_projection import (
        RuntimePlaneAxis, RuntimePlaneAxisValueProjection,
    )
    from openhcs.core.runtime_image_values import normalize_image_payload_intensity

    source = _source()
    stack = source.metadata.replace_fields(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_dtype="uint16",
    ).payload_with(source.data[None])
    pixels = np.linspace(0, 3, 30, dtype=np.float32).reshape(1, 5, 6)
    projection = RuntimePlaneAxisValueProjection.preserve(
        axis=RuntimePlaneAxis.RUNTIME_SLICE, axis_size=1
    )
    output = SelectedDiagnosticPlaneImageOutput(pixels, (0,))
    resolved = output.resolve_source_context(stack, projection)
    np.testing.assert_array_equal(resolved.data, pixels[0])
    np.testing.assert_array_equal(normalize_image_payload_intensity(resolved), pixels[0])
    assert resolved.metadata.source_path == source.metadata.source_path
    assert resolved.metadata.source_spatial_domain == source.metadata.source_spatial_domain
    assert resolved.metadata.source_dtype == "float32"
    assert resolved.metadata.intensity_scale is None
    with pytest.raises(ValueError, match="preserve the source spatial shape"):
        SelectedDiagnosticPlaneImageOutput(pixels[:, :4], (0,)).resolve_source_context(
            stack, projection
        )


@pytest.mark.parametrize("executed", [False, True])
def test_planes_preserve_exact_source_coordinates_and_owned_variants(executed):
    source = _source()
    objects = _objects(source)
    response = source.data.copy()
    maxima = response > 20
    markers = maxima.astype(np.int32)
    evidence = (
        ExecutedDeclumpingEvidence(response, maxima, markers)
        if executed else UnexecutedDeclumpingEvidence()
    )
    threshold_support = source.data > 15
    initial_components = objects.labels.copy()
    diagnostics = PrimaryObjectDiagnosticPlanes.from_execution(
        image=source,
        threshold_support=threshold_support,
        initial_components=initial_components,
        declumping=evidence,
        objects=objects,
    )
    assert len(diagnostics) == 7
    for plane in diagnostics:
        assert plane.data.shape == source.data.shape
        assert plane.metadata.source_provenance == source.metadata.source_provenance
        assert plane.metadata.source_path == source.metadata.source_path
        assert plane.metadata.spatial_origin_yx == (40, 80)
        assert plane.metadata.intensity_scale is None
        assert plane.metadata.source_dtype == str(plane.data.dtype)
    assert source.metadata.intensity_scale == 65535
    assert diagnostics.threshold_support.data is threshold_support
    assert diagnostics.initial_components.data is initial_components
    assert diagnostics.unedited_objects.data is objects.unedited_labels
    assert diagnostics.small_removed_objects.data is objects.small_removed_labels
    assert objects.domain.declared_object_count == 1
    assert diagnostics.threshold_support.mask is diagnostics.initial_components.mask
    assert diagnostics.unedited_objects.mask is diagnostics.small_removed_objects.mask
    if executed:
        assert diagnostics.declump_response.data is response
        assert diagnostics.seed_maxima.data is maxima
        assert diagnostics.seed_markers.data is markers
        assert diagnostics.declump_response.mask is source.mask
    else:
        assert diagnostics.declump_response.data.dtype == np.float32
        assert np.isnan(diagnostics.declump_response.data).all()
        assert not diagnostics.seed_markers.data.any()
        assert not diagnostics.seed_maxima.data.any()
        assert not diagnostics.declump_response.mask.any()
        assert not diagnostics.seed_maxima.mask.any()
        assert not diagnostics.seed_markers.mask.any()
        assert diagnostics.declump_response.mask is diagnostics.seed_maxima.mask
        assert diagnostics.seed_maxima.mask is diagnostics.seed_markers.mask


def test_diagnostic_contract_has_source_producer_stage_identity_not_new_objects():
    source = ArtifactSpec.input("DNA", ImageArtifactType)
    objects = ArtifactSpec.output("Nuclei", ObjectLabelsArtifactType)
    specs = PrimaryObjectDiagnosticPlanes.artifact_specs(source_image=source, objects=objects)
    assert len(specs) == len(PrimaryObjectDiagnosticPlanes._fields)
    for field, spec in zip(PrimaryObjectDiagnosticPlanes._fields, specs, strict=True):
        assert spec.name.endswith(f"__{field}")
        assert spec.artifact_type is ImageArtifactType
        assert spec.sidecar_role is ArtifactSidecarRole.QA_CHECKPOINT
        assert not spec.participates_in_main_flow
        assert spec.viewer_streaming is ArtifactViewerStreaming.ON_DEMAND
        assert spec.materialization.participates_in_persistent_materialization()
        assert not spec.materialization.participates_in_runtime_export_observation()
        assert spec.materialization.outputs == (
            ImageFileOptions(
                filename_suffix=".tif",
                filename_identity=MaterializedFilenameIdentity.ARTIFACT_NAME,
            ),
        )
        assert spec.source_context_sources() == (source.ref(),)
        assert ArtifactSidecarSourceRelation(source=objects.ref()) in spec.relations
    assert len(get_args(PrimaryObjectsRuntimeTuple)) == 3 + len(specs)
    assert get_args(PrimaryObjectsRuntimeTuple)[3:] == (MaskedImagePayload,) * len(specs)


def test_ordinary_image_contextualization_preserves_unexecuted_masks():
    from openhcs.core.artifacts import ArtifactOutputPlan


    source = _source()
    objects = _objects(source)
    diagnostics = PrimaryObjectDiagnosticPlanes.from_execution(
        image=source, threshold_support=source.data > 15,
        initial_components=objects.labels,
        declumping=UnexecutedDeclumpingEvidence(), objects=objects,
    )
    specs = PrimaryObjectDiagnosticPlanes.artifact_specs(
        source_image=ArtifactSpec.input("DNA", ImageArtifactType),
        objects=ArtifactSpec.output("Nuclei", ObjectLabelsArtifactType),
    )
    for spec, plane in zip(specs, diagnostics, strict=True):
        plan = ArtifactOutputPlan(
            name=spec.name, path=f"/memory/{spec.name}.pkl",
            artifact_type=spec.artifact_type, sidecar_role=spec.sidecar_role,
            relations=spec.relations,
        )
        value = (ImageArtifactType if plan is None else plan.artifact_type).contextualize_output(
            source, plane, plan, None
        )
        np.testing.assert_array_equal(value.mask, plane.mask)
        np.testing.assert_array_equal(value.data, plane.data)
        assert value.metadata.source_provenance == source.metadata.source_provenance
        assert value.metadata.intensity_scale is None


def test_existing_pure2d_aggregation_retains_stage_pixels_masks_and_plane_identity():
    from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
    from openhcs.processing.backends.lib_registry.unified_registry import Pure2DAuxiliaryOutputAggregator
    from openhcs.processing.backends.cellprofiler.primary_object_diagnostics import DiagnosticPlaneSource

    first = _source()
    second = MaskedImagePayload(
        first.data + 10, ~first.mask,
        ImagePayloadMetadata(
            source_path="/synthetic/A01_s002_DNA.tif", source_image_names=("DNA",),
            source_spatial_domain=first.metadata.source_spatial_domain,
        ),
    )
    planes = [DiagnosticPlaneSource.from_image(source).plane(source.data)
              for source in (first, second)]
    value = Pure2DAuxiliaryOutputAggregator.aggregate(
        planes, "numpy", plane_axis=RuntimePlaneAxis.RUNTIME_SLICE
    )
    import pickle
    from openhcs.core.aligned_image_payload import ProducedImageStack
    from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

    assert isinstance(value, ProducedImageStack)
    assert value._composed_payload is None
    assert value.shape == (2, *first.data.shape)
    value = pickle.loads(pickle.dumps(value))
    assert value._composed_payload is None
    composed = RuntimeSliceProjection.full_stack_value(value)
    assert RuntimeSliceProjection.full_stack_value(value) is composed
    np.testing.assert_array_equal(composed.data, np.stack([first.data, second.data]))
    np.testing.assert_array_equal(composed.mask, np.stack([first.mask, second.mask]))
    assert value.metadata.plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
    assert value.metadata.source_provenance.source_plane_count == 2
    reloaded = pickle.loads(pickle.dumps(value))
    assert np.shares_memory(reloaded.slices[0].data, reloaded.compose().data)
    assert np.shares_memory(reloaded.slices[0].mask, reloaded.compose().mask)
    independent = value.copy_input_cohort(memory_type="numpy", device_id=None)
    assert not np.shares_memory(independent.slices[0].data, composed.data)
    assert not np.shares_memory(independent.slices[0].mask, composed.mask)


def test_typed_stage_payloads_roundtrip_existing_pickle_boundary():
    import pickle

    source = _source()
    diagnostics = PrimaryObjectDiagnosticPlanes.from_execution(
        image=source, threshold_support=source.data > 15,
        initial_components=_objects(source).labels,
        declumping=UnexecutedDeclumpingEvidence(), objects=_objects(source),
    )
    reloaded = pickle.loads(pickle.dumps(diagnostics))
    for before, after in zip(diagnostics, reloaded, strict=True):
        np.testing.assert_array_equal(before.data, after.data)
        np.testing.assert_array_equal(before.mask, after.mask)
        assert before.metadata == after.metadata


def test_new_stage_declaration_needs_no_catalog_or_dispatch_edit():
    # Run the actual declaration projection with a new nominal record field.
    class ExtendedPlanes(NamedTuple):
        additional_stage: MaskedImagePayload

    specs = PrimaryObjectDiagnosticPlanes.artifact_specs.__func__(
        ExtendedPlanes,
        source_image=ArtifactSpec.input("DNA", ImageArtifactType),
        objects=ArtifactSpec.output("Nuclei", ObjectLabelsArtifactType),
    )
    assert len(specs) == 1
    assert specs[0].name.endswith("__additional_stage")


def test_focused_real_source_antipattern_guards():
    root = Path(__file__).resolve().parents[2]
    source = root / "openhcs/processing/backends/cellprofiler/primary_object_diagnostics.py"
    tree = ast.parse(source.read_text())
    # IMPL-1/2/3/7 and BOUND-1/2/7: evidence owners have no kind/type
    # dispatcher, raw string-key consumers or duck-typed fallback readers.
    assert not any(isinstance(node, ast.Match) for node in ast.walk(tree))
    assert not any(
        isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
        and node.func.id in {"isinstance", "getattr", "hasattr", "eval", "exec"}
        for node in ast.walk(tree)
    )
    assert not any(
        isinstance(node, ast.Subscript) and isinstance(node.slice, ast.Constant)
        and isinstance(node.slice.value, str)
        for node in ast.walk(tree)
    )
    projection = next(
        node for node in ast.walk(tree)
        if isinstance(node, ast.FunctionDef) and node.name == "artifact_specs"
    )
    # MEMB-1/3: no hand-maintained roster alongside the typed stage record.
    assert not any(isinstance(node, (ast.List, ast.Set, ast.Dict)) for node in ast.walk(projection))
    assert any(
        isinstance(node, ast.Attribute) and node.attr == "_fields"
        for node in ast.walk(projection)
    )


def test_processing_body_is_unchanged_except_same_run_evidence_capture():
    root = Path(__file__).resolve().parents[2]
    relative = "openhcs/processing/backends/cellprofiler/primary_objects.py"
    baseline = subprocess.run(
        ["git", "show", f"a0263e82a1b3296f34f8c5cdd50ffae5c33ef7dd:{relative}"],
        cwd=root, check=True, capture_output=True, text=True,
    ).stdout
    before = next(n for n in ast.parse(baseline).body if isinstance(n, ast.FunctionDef)
                  and n.name == "identify_primary_objects")
    after = next(n for n in ast.parse((root / relative).read_text()).body
                 if isinstance(n, ast.FunctionDef) and n.name == before.name)

    class RemoveEvidence(ast.NodeTransformer):
        def visit_Assign(self, node):
            if any(isinstance(target, ast.Name) and target.id in {
                "threshold_support", "initial_components", "declumping", "diagnostics"
            } for target in node.targets):
                return None
            return self.generic_visit(node)

    after = RemoveEvidence().visit(after)
    # Compare the original algorithm, not docstring, signature or output ABI.
    assert ast.dump(ast.Module(body=before.body[1:-1], type_ignores=[])) == ast.dump(
        ast.Module(body=after.body[1:-1], type_ignores=[]))
