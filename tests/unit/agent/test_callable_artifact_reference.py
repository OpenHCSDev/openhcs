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
from openhcs.agent.knowledge_manifest import knowledge_base_source_paths_from_manifest
from openhcs.agent.services.knowledge_base_service import KnowledgeBaseService
from openhcs.core.artifacts import ArtifactOutputPlan, ObjectLabelsArtifactType
from openhcs.core.callable_contract import CallableContract
from openhcs.core.function_patterns import compile_function_pattern
from openhcs.core.runtime_image_values import ImageMetadataPayload, ImagePayloadMetadata
from openhcs.core.runtime_object_labels import ObjectLabelPayload, ObjectLabelVariantData
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
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
    return "\n".join(line[3:] if line.startswith("   ") else line
                     for line in match.group(1).splitlines())


@pytest.fixture
def reference_namespace():
    module = ModuleType("_openhcs_public_artifact_reference")
    sys.modules[module.__name__] = module
    try:
        exec(compile(_reference_block("callable-artifact-reference"),
                     DOCUMENT_PATH, "exec"), module.__dict__)
        yield module.__dict__
    finally:
        sys.modules.pop(module.__name__, None)


def test_canonical_reference_is_unique_searchable_and_fully_readable():
    service = KnowledgeBaseService(repo_root=ROOT)
    catalog = service.list_documents()
    matches = [document for document in catalog.documents
               if document.source_path == DOCUMENT_PATH]
    assert len(matches) == 1
    assert matches[0].document_id == DOCUMENT_ID
    assert ROOT / DOCUMENT_PATH in knowledge_base_source_paths_from_manifest()
    result = service.search(KnowledgeBaseSearchRequest(
        query="RuntimeMeasurementFeatureOwner DataclassMeasurementColumnarRows",
        limit=10,
    ))
    assert DOCUMENT_ID in {hit.document.document_id for hit in result.hits}
    document = service.get_document(KnowledgeBaseDocumentRequest.from_fields(
        document_id=DOCUMENT_ID, max_chars=30_000,
    ))
    assert not document.truncated
    for line in _reference_block("callable-artifact-reference").splitlines():
        if line.strip():
            assert line in document.content
    assert "from openhcs.core.memory import numpy" in document.content


def test_reference_executes_and_compiles_actual_function_step(reference_namespace):
    namespace = reference_namespace
    exec(compile(_reference_block("callable-artifact-reference-check"),
                 DOCUMENT_PATH, "exec"), namespace)
    contract = namespace["contract"]
    assert contract.input_memory_type == contract.output_memory_type == "numpy"
    assert contract.processing_contract == namespace["ProcessingContract"].PURE_2D
    specs = contract.artifact_outputs.specs
    assert tuple(spec.name for spec in specs) == (
        "fixture_image", "fixture_labels", "fixture_object_rows",
    )
    assert specs[1].artifact_type is ObjectLabelsArtifactType
    assert specs[2].measurement_feature_owner is namespace["FixtureFeatureOwner"]
    plans = {spec.ref(): ArtifactOutputPlan(
        name=spec.name, path=f"/memory/{spec.name}.pkl",
        artifact_type=spec.artifact_type, relations=spec.relations,
    ) for spec in specs}
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
        "slice_index", "object_label", "pixel_count",
    )
    assert namespace["FixtureFeatureOwner"].owns_primary_measurement_feature_name(
        "pixel_count"
    )
    assert not namespace["FixtureFeatureOwner"].owns_measurement_feature_name("unknown")


def test_complete_reference_prepares_in_real_custom_namespace(tmp_path, monkeypatch):
    monkeypatch.setattr(custom_manager, "get_data_file_path",
                        lambda _name: tmp_path / "custom_functions")
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


def test_reference_writes_native_csv_and_roi_files(reference_namespace, tmp_path):
    namespace = reference_namespace
    fixture = np.zeros((8, 8), dtype=np.uint16)
    fixture[2:6, 3:7] = 1
    _image, labels, rows = namespace["inspect_label_fixture"](fixture)
    filemanager = FileManager({"disk": DiskStorageBackend()})
    csv_path = materialize(
        namespace["FIXTURE_ROWS"].materialization, data=rows,
        path=str(tmp_path / "fixture_object_rows"), filemanager=filemanager,
        backends=["disk"], backend_kwargs={},
    )
    assert Path(csv_path).read_text().splitlines() == [
        "slice_index,object_label,pixel_count", "0,1,16",
    ]
    payload = ObjectLabelPayload(variant_data=ObjectLabelVariantData(labels=labels))
    roi_path = materialize(
        namespace["FIXTURE_LABELS"].materialization, data=payload,
        path=str(tmp_path / "fixture_labels"), filemanager=filemanager,
        backends=["disk"], backend_kwargs={},
    )
    assert Path(roi_path).is_file()
    rois = load_rois_from_zip(Path(roi_path))
    assert len(rois) == 1


def test_packaged_knowledge_projection_retains_executable_reference(tmp_path):
    helpers = runpy.run_path(str(ROOT / "scripts/build_mcp_knowledge_assets.py"))
    destination = tmp_path / "knowledge_projection"
    paths = helpers["project_knowledge_assets"](ROOT, destination)
    assert destination / DOCUMENT_PATH in paths
    assert (destination / DOCUMENT_PATH).read_bytes() == (ROOT / DOCUMENT_PATH).read_bytes()
    service = KnowledgeBaseService(repo_root=destination)
    document = service.get_document(KnowledgeBaseDocumentRequest.from_fields(
        document_id=DOCUMENT_ID, max_chars=30_000,
    ))
    assert "def inspect_label_fixture(" in document.content
    assert "from openhcs.core.memory import numpy" in document.content
