"""Execute the canonical public usage code, rather than a copied example."""

import re
import runpy
import sys
from pathlib import Path
from types import ModuleType

import numpy as np
import pytest

from openhcs.agent.dto.knowledge import (
    KnowledgeBaseDocumentRequest,
    KnowledgeBaseSearchRequest,
)
from openhcs.agent.knowledge_manifest import (
    DEFAULT_KNOWLEDGE_BASE_MANIFEST_PATH,
    knowledge_base_source_paths_from_manifest,
)
from openhcs.agent.services.knowledge_base_service import KnowledgeBaseService
from openhcs.core.artifacts import (
    ArtifactInputPlan,
    ArtifactOutputPlan,
    ArtifactSpec,
    ArtifactSpecCollection,
    ImageArtifactType,
    ObjectLabelsArtifactType,
)
from openhcs.core.callable_contract import CallableContract
from openhcs.core.function_patterns import (
    compile_function_pattern,
    normalize_function_pattern,
)
from openhcs.core.invocation_artifacts import (
    ArtifactDeclarationStepContext,
    MainFlowArtifactContractProvider,
    PIPELINE_INPUT_ARTIFACT,
)
from openhcs.core.runtime_image_values import ImageMetadataPayload, ImagePayloadMetadata
from openhcs.core.runtime_object_label_domains import ObjectLabelDomainScope
from openhcs.core.runtime_object_labels import (
    ObjectLabelPayload,
    ObjectLabelValue,
    ObjectLabelVariantData,
)
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisValueProjection,
)
from openhcs.core.steps.function_runtime import FunctionOutputContextStrategy
from openhcs.processing.custom_functions import manager as custom_manager
from openhcs.processing.materialization import materialize
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
from polystore.roi import load_rois_from_zip

ROOT = Path(__file__).resolve().parents[3]
DOCUMENT_PATH = "docs/source/development/callable_artifact_authoring.rst"
DOCUMENT_ID = "openhcs_callable_artifact_authoring"


def _reference_block(name):
    text = (ROOT / DOCUMENT_PATH).read_text(encoding="utf-8")
    match = re.search(
        rf"\.\. code-block:: python\n   :name: {re.escape(name)}\n\n"
        r"((?:   [^\n]*\n|\n)+)",
        text,
    )
    assert match is not None, f"Missing canonical example block: {name}"
    return "\n".join(
        line[3:] if line.startswith("   ") else line
        for line in match.group(1).splitlines()
    )


@pytest.fixture
def reference_namespace():
    module = ModuleType("_openhcs_public_artifact_reference")
    sys.modules[module.__name__] = module
    try:
        for block in ("callable-artifact-reference", "callable-artifact-input-reference"):
            exec(compile(_reference_block(block), DOCUMENT_PATH, "exec"), module.__dict__)
        yield module.__dict__
    finally:
        sys.modules.pop(module.__name__, None)


def test_canonical_reference_is_unique_searchable_and_fully_readable():
    service = KnowledgeBaseService(repo_root=ROOT)
    catalog = service.list_documents()
    matches = [
        document
        for document in catalog.documents
        if document.source_path == DOCUMENT_PATH
    ]
    assert len(matches) == 1
    assert matches[0].document_id == DOCUMENT_ID
    assert ROOT / DOCUMENT_PATH in knowledge_base_source_paths_from_manifest(
        ROOT / DEFAULT_KNOWLEDGE_BASE_MANIFEST_PATH
    )
    result = service.search(
        KnowledgeBaseSearchRequest(
            query="RuntimeMeasurementFeatureOwner DataclassMeasurementColumnarRows",
            limit=10,
        )
    )
    assert DOCUMENT_ID in {hit.document.document_id for hit in result.hits}
    document = service.get_document(
        KnowledgeBaseDocumentRequest.from_fields(
            document_id=DOCUMENT_ID,
            max_chars=30_000,
        )
    )
    assert not document.truncated
    for line in _reference_block("callable-artifact-reference").splitlines():
        if line.strip():
            assert line in document.content
    assert "from openhcs.core.memory import numpy" in document.content


def test_reference_executes_and_compiles_actual_function_step(reference_namespace):
    namespace = reference_namespace
    exec(
        compile(
            _reference_block("callable-artifact-reference-check"), DOCUMENT_PATH, "exec"
        ),
        namespace,
    )
    contract = namespace["contract"]
    assert contract.input_memory_type == contract.output_memory_type == "numpy"
    assert contract.processing_contract == namespace["ProcessingContract"].PURE_2D
    specs = contract.artifact_outputs.specs
    assert tuple(spec.name for spec in specs) == (
        "fixture_image",
        "fixture_labels",
        "fixture_object_rows",
    )
    assert specs[1].artifact_type is ObjectLabelsArtifactType
    assert specs[2].measurement_feature_owner is namespace["FixtureFeatureOwner"]
    plans = {
        spec.ref(): ArtifactOutputPlan(
            name=spec.name,
            path=f"/memory/{spec.name}.pkl",
            artifact_type=spec.artifact_type,
            relations=spec.relations,
        )
        for spec in specs
    }
    subject = plans[specs[2].ref()].measurement_subject()
    assert subject.name == "fixture_labels"
    assert subject.id_field == "object_label"
    compiled = compile_function_pattern(namespace["step"].func, {}, plans)
    assert len(compiled.groups[0].invocations) == 1
    assert compiled.groups[0].invocations[0].contract.artifact_outputs == (
        contract.artifact_outputs
    )
    empty = namespace["inspect_label_fixture"](np.zeros((8, 8), dtype=np.uint16))[2]
    assert empty.row_count() == 0
    assert tuple(field.name for field in empty.fields) == (
        "slice_index",
        "object_label",
        "pixel_count",
    )
    assert namespace["FixtureFeatureOwner"].owns_primary_measurement_feature_name(
        "pixel_count"
    )
    assert not namespace["FixtureFeatureOwner"].owns_measurement_feature_name("unknown")


def test_input_reference_compiles_nominal_binding_and_repairs_wrong_annotation(
    reference_namespace,
):
    namespace = reference_namespace
    function = namespace["mask_declared_objects"]
    declaration = namespace["STORED_LABELS"]
    contract = CallableContract.from_callable(function)
    assert declaration.artifact_type.runtime_parameter_types() == (ObjectLabelValue,)
    assert contract.artifact_input_parameter_names == ("objects",)
    contract.validate_artifact_input_parameter_bindings()
    plan = ArtifactInputPlan(
        declaration.name, "/synthetic/fixture-labels.pkl",
        artifact_type=declaration.artifact_type,
    )
    compiled = compile_function_pattern(function, {plan.ref(): plan}, {})
    assert compiled.groups[0].invocations[0].contract.artifact_inputs.specs == (
        declaration,
    )
    pixels = np.asarray([[0, 2], [7, 0]], dtype=np.int32)
    labels = ObjectLabelPayload(variant_data=ObjectLabelVariantData(labels=pixels))
    image = np.asarray([[1, 3], [5, 9]], dtype=np.uint16)
    np.testing.assert_array_equal(function(image, objects=labels), [[0, 3], [5, 0]])
    np.testing.assert_array_equal(labels.labels, pixels)

    # Exercise the original admission boundary, not a word-match assertion.
    raw = contract.resolve_canonical_raw_callable()
    original_annotation = raw.__annotations__["objects"]
    try:
        raw.__annotations__["objects"] = np.ndarray
        from openhcs.core.pipeline.function_contracts import resolved_callable_type_hints
        resolved_callable_type_hints.cache_clear()
        with pytest.raises(TypeError, match="does not accept object_labels artifact payloads"):
            compile_function_pattern(function, {plan.ref(): plan}, {})
    finally:
        raw.__annotations__["objects"] = original_annotation
        resolved_callable_type_hints.cache_clear()
    compile_function_pattern(function, {plan.ref(): plan}, {})


def test_complete_reference_prepares_in_real_custom_namespace(tmp_path, monkeypatch):
    def fixture_storage(_name, *, create):
        assert create is False
        return tmp_path / "custom_functions"

    monkeypatch.setattr(
        custom_manager,
        "get_data_file_path",
        fixture_storage,
    )
    manager = custom_manager.CustomFunctionManager()
    metadata = manager._prepare_source(_reference_block("callable-artifact-reference"))
    contract = CallableContract.from_callable(metadata.func)
    assert contract.artifact_outputs.specs[-1].measurement_feature_owner is not None
    fixture = np.zeros((8, 8), dtype=np.uint16)
    fixture[2:6, 3:7] = 1
    returned = metadata.func(fixture)
    assert returned[2].row_mappings()[0]["pixel_count"] == 16
    stack = ImageMetadataPayload(
        data=np.stack((fixture, fixture)),
        metadata=ImagePayloadMetadata(plane_axis=RuntimePlaneAxis.RUNTIME_SLICE),
    )
    stacked = metadata.func(stack)
    assert stacked[2].row_mappings() == (
        {"slice_index": 0, "object_label": 1, "pixel_count": 16},
        {"slice_index": 1, "object_label": 1, "pixel_count": 16},
    )
    assert list(manager.storage_dir.iterdir()) == []


@pytest.mark.parametrize("plane_count", (None, 1, 2))
def test_reference_retains_plane_domain_until_raw_numpy_invocation(
    tmp_path, monkeypatch, plane_count,
):
    monkeypatch.setattr(
        custom_manager, "get_data_file_path",
        lambda _name, *, create: tmp_path / "custom_functions",
    )
    manager = custom_manager.CustomFunctionManager(create_storage=False)
    prepared = manager._prepare_source(_reference_block("callable-artifact-reference"))
    contract = CallableContract.from_callable(prepared.func)
    fixture = np.zeros((8, 8), dtype=np.uint16)
    fixture[2:6, 3:7] = 1
    stack = ImageMetadataPayload(
        data=fixture if plane_count is None else np.stack((fixture,) * plane_count),
        metadata=ImagePayloadMetadata(
            source_dtype="uint16",
            source_path="/synthetic/label-fixture.tif",
            plane_axis=None if plane_count is None else RuntimePlaneAxis.RUNTIME_SLICE,
        ),
    )
    call_argument = contract.main_flow_call_argument(stack)
    assert call_argument is stack
    image, labels, rows = prepared.func(call_argument)
    np.testing.assert_array_equal(image, stack.data)
    np.testing.assert_array_equal(labels, stack.data)
    assert rows.row_mappings() == tuple(
        {"slice_index": plane, "object_label": 1, "pixel_count": 16}
        for plane in range(1 if plane_count is None else plane_count)
    )
    projection = (
        None if plane_count is None else RuntimePlaneAxisValueProjection(
            axis=RuntimePlaneAxis.RUNTIME_SLICE, source_aliases=(),
            plane_index=None, axis_size=plane_count,
        )
    )
    label_payload = FunctionOutputContextStrategy.for_context(
        ObjectLabelsArtifactType,
    ).contextualize(stack, labels, None, projection)
    assert isinstance(label_payload, ObjectLabelPayload)
    np.testing.assert_array_equal(label_payload.labels, stack.data)
    assert label_payload.plane_axis is (
        None if plane_count is None else RuntimePlaneAxis.RUNTIME_SLICE
    )
    assert label_payload.source_provenance == stack.metadata.source_provenance
    assert label_payload.source_spatial_domain.source_shape_yx == (8, 8)
    assert label_payload.domain.scope is (
        ObjectLabelDomainScope.PAYLOAD
        if plane_count is None else ObjectLabelDomainScope.PLANE
    )
    if plane_count is not None:
        assert label_payload.domain.declared_object_id_domains == ((1,),) * plane_count
        wrong_spatial_shape = ImagePayloadMetadata(
            plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        ).payload_with(stack.data[:, :-1, :])
        with pytest.raises(ValueError, match="Object-label spatial shape"):
            FunctionOutputContextStrategy.for_context(
                ObjectLabelsArtifactType,
            ).contextualize(stack, wrong_spatial_shape, None, projection)
    assert not manager.storage_dir.exists()


@pytest.mark.parametrize(
    "source",
    (
        PIPELINE_INPUT_ARTIFACT,
        ArtifactSpec.input("filtered_fixture", ImageArtifactType),
    ),
)
def test_reference_binds_all_output_lineage_to_current_image(
    reference_namespace, source,
):
    invocation = next(
        normalize_function_pattern(
            reference_namespace["inspect_label_fixture"]
        ).iter_items()
    )
    plan = MainFlowArtifactContractProvider()(
        invocation,
        ArtifactDeclarationStepContext(
            main_flow_artifacts=ArtifactSpecCollection((source,)),
        ),
    )
    assert plan is not None
    contract = plan.contract
    assert contract.group_scope_inputs.specs == (source,)
    assert contract.output_group_scope_sources == (source.ref(),)
    for output in contract.artifact_outputs:
        assert output.source_stack_scope_sources() == (source.ref(),)
    assert contract.canonical_return_output_specs.names() == ("fixture_image",)
    assert contract.trailing_return_output_specs.names() == (
        "fixture_labels", "fixture_object_rows",
    )
    rows = contract.artifact_outputs.by_ref(
        reference_namespace["FIXTURE_ROWS"].ref()
    )
    assert rows is not None
    subject = ArtifactOutputPlan(
        name=rows.name,
        path="/memory/fixture_object_rows.csv",
        artifact_type=rows.artifact_type,
        relations=rows.relations,
    ).object_subject_binding()
    assert subject is not None
    assert subject.source == reference_namespace["FIXTURE_LABELS"].ref()
    assert subject.id_field == "object_label"


def test_reference_writes_native_csv_and_roi_files(reference_namespace, tmp_path):
    namespace = reference_namespace
    fixture = np.zeros((8, 8), dtype=np.uint16)
    fixture[2:6, 3:7] = 1
    _image, labels, rows = namespace["inspect_label_fixture"](fixture)
    filemanager = FileManager({"disk": DiskStorageBackend()})
    csv_path = materialize(
        namespace["FIXTURE_ROWS"].materialization,
        data=rows,
        path=str(tmp_path / "fixture_object_rows"),
        filemanager=filemanager,
        backends=["disk"],
        backend_kwargs={},
    )
    assert Path(csv_path).read_text().splitlines() == [
        "slice_index,object_label,pixel_count",
        "0,1,16",
    ]
    payload = ObjectLabelPayload(variant_data=ObjectLabelVariantData(labels=labels))
    roi_path = materialize(
        namespace["FIXTURE_LABELS"].materialization,
        data=payload,
        path=str(tmp_path / "fixture_labels"),
        filemanager=filemanager,
        backends=["disk"],
        backend_kwargs={},
    )
    assert Path(roi_path).is_file()
    rois = load_rois_from_zip(Path(roi_path))
    assert len(rois) == 1


def test_packaged_knowledge_projection_retains_executable_reference(tmp_path):
    helpers = runpy.run_path(str(ROOT / "scripts/build_mcp_knowledge_assets.py"))
    destination = tmp_path / "knowledge_projection"
    paths = helpers["project_knowledge_assets"](ROOT, destination)
    assert destination / DOCUMENT_PATH in paths
    assert (destination / DOCUMENT_PATH).read_bytes() == (
        ROOT / DOCUMENT_PATH
    ).read_bytes()
    service = KnowledgeBaseService(repo_root=destination)
    document = service.get_document(
        KnowledgeBaseDocumentRequest.from_fields(
            document_id=DOCUMENT_ID,
            max_chars=30_000,
        )
    )
    assert "def inspect_label_fixture(" in document.content
    assert "from openhcs.core.memory import numpy" in document.content
