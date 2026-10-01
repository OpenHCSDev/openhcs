"""Exercise task retrieval and installable projection, not prose acceptance."""

import hashlib
import re
import runpy
from pathlib import Path

import pytest

from openhcs.agent.authoring_contexts import (
    CustomFunctionAuthoringContext,
    ImageAnalysisWorkflowAuthoringContext,
)
from openhcs.agent.dto.knowledge import (
    KnowledgeBaseDocumentRequest,
    KnowledgeBaseSearchRequest,
)
from openhcs.agent.services.knowledge_base_service import KnowledgeBaseService
from openhcs.agent.services.llm_context_service import AgentAuthoringContextService
from openhcs.agent.skill_bundle import AGENT_PLUGIN_MANIFEST_PATH, AgentSkillBundle
from openhcs.agent.skill_sync import SkillSyncReceipt, sync_skills

ROOT = Path(__file__).resolve().parents[3]
TASKS = (
    ("autonomous analysis strategy", "openhcs_autonomous_analysis_strategy"),
    ("channel identity RGB composite", "openhcs_image_interpretation"),
    ("uneven background additive subtraction", "openhcs_image_preprocessing"),
    ("nucleus split watershed", "openhcs_segmentation_diagnostics"),
    ("zero growth cytoplasm", "openhcs_segmentation_diagnostics"),
    ("all foreground threshold units", "openhcs_segmentation_diagnostics"),
    ("volume anisotropic Z spacing", "openhcs_measurement_interpretation"),
    ("Pearson Manders Costes", "openhcs_measurement_interpretation"),
    ("current processing intensity units", "openhcs_measurement_interpretation"),
    ("recipe error memory", "openhcs_analysis_learning"),
    ("canvas resize recapture", "openhcs_viewer_qa"),
    ("channel switch contrast window", "openhcs_viewer_qa"),
    ("remote desktop compression native capture", "openhcs_viewer_qa"),
    ("diagnostic soma saturation", "openhcs_viewer_qa"),
    ("noise background illumination scan", "openhcs_viewer_qa"),
    ("blind recipe promotion", "openhcs_blind_recipe_promotion"),
    ("missing analysis operation", "openhcs_custom_function_workflow"),
)


@pytest.mark.parametrize(("query", "document_id"), TASKS)
def test_task_retrieval_reaches_a_bounded_canonical_source(query, document_id):
    service = KnowledgeBaseService(repo_root=ROOT)
    hits = service.search(KnowledgeBaseSearchRequest(query=query, limit=10))
    assert not hits.errors
    assert document_id in {hit.document.document_id for hit in hits.hits}

    document = service.get_document(
        KnowledgeBaseDocumentRequest.from_fields(
            document_id=document_id, max_chars=24_000
        )
    )
    assert not document.errors
    assert not document.truncated
    assert document.document is not None
    source = ROOT / document.document.source_path
    assert source.read_text(encoding="utf-8").strip() == document.content.strip()
    assert len(document.sections) > 2

    selected = service.get_document(
        KnowledgeBaseDocumentRequest.from_fields(
            document_id=document_id,
            section_id=document.sections[1].section_id,
            max_chars=400,
        )
    )
    assert not selected.errors
    assert selected.selected_section_id == document.sections[1].section_id
    assert len(selected.content) <= 400
    assert selected.content in document.content
    assert selected.document.source_path == document.document.source_path


def test_packaged_transfer_guides_retain_content_sections_and_skill_links(tmp_path):
    project = runpy.run_path(str(ROOT / "scripts/build_mcp_knowledge_assets.py"))
    destination = tmp_path / "knowledge"
    paths = project["project_knowledge_assets"](ROOT, destination)
    service = KnowledgeBaseService(repo_root=destination)
    for document_id in dict.fromkeys(document_id for _, document_id in TASKS):
        document = service.get_document(
            KnowledgeBaseDocumentRequest.from_fields(
                document_id=document_id, max_chars=24_000
            )
        )
        assert not document.errors
        assert not document.truncated
        source_path = Path(document.document.source_path)
        assert destination / source_path in paths
        assert (destination / source_path).read_bytes() == (
            ROOT / source_path
        ).read_bytes()
        assert document.content.strip() == (ROOT / source_path).read_text(
            encoding="utf-8"
        ).strip()
        # Each local companion link is available in the projected package,
        # rather than depending on the developer's checkout or /tmp sources.
        for link in re.findall(r"\]\(([^)]+\.md)\)", document.content):
            if "://" not in link:
                assert (destination / source_path.parent / link).is_file()

    skill = ROOT / "packaging/codex/openhcs/skills/use-openhcs/SKILL.md"
    for link in re.findall(r"\]\((references/[^)]+\.md)\)", skill.read_text()):
        assert (skill.parent / link).is_file()


def test_domain_knowledge_remains_progressively_retrieved():
    service = KnowledgeBaseService(repo_root=ROOT)
    catalogue = service.list_documents()
    transferred = {
        document.document_id: document
        for document in catalogue.documents
        if document.document_id in {document_id for _, document_id in TASKS}
    }
    assert len(transferred) == 9
    assert len({document.source_path for document in transferred.values()}) == 9
    # Catalogue summaries do not eagerly expand teaching chapters or answers.
    assert all(len(document.summary) < 600 for document in transferred.values())
    assert all(document.section_count > 2 for document in transferred.values())
    strategy = service.get_document(
        KnowledgeBaseDocumentRequest.from_fields(
            document_id="openhcs_autonomous_analysis_strategy"
        )
    )
    links = set(re.findall(r"\]\(([^)]+\.md)\)", strategy.content))
    # A skill-only reader must be able to follow the same topic routes without
    # guessing filenames or needing the live knowledge service.
    for document in transferred.values():
        if document.document_id not in (
            "openhcs_autonomous_analysis_strategy",
            "openhcs_blind_recipe_promotion",
        ):
            assert Path(document.source_path).name in links


def test_complete_projected_skill_sync_preserves_canonical_resource_bytes(tmp_path):
    project = runpy.run_path(str(ROOT / "scripts/build_mcp_knowledge_assets.py"))
    projection = tmp_path / "knowledge"
    project["project_knowledge_assets"](ROOT, projection)
    canonical = AgentSkillBundle.from_manifest(ROOT / AGENT_PLUGIN_MANIFEST_PATH)
    packaged = AgentSkillBundle.from_manifest(projection / AGENT_PLUGIN_MANIFEST_PATH)
    for document_id, section_id in (
        ("openhcs_measurement_interpretation", "current-processing-intensity-units"),
        ("openhcs_segmentation_diagnostics", "foreground-before-unclumping"),
    ):
        request = KnowledgeBaseDocumentRequest.from_fields(
            document_id=document_id, section_id=section_id, max_chars=4_000
        )
        original = KnowledgeBaseService(repo_root=ROOT).get_document(request)
        copied = KnowledgeBaseService(repo_root=projection).get_document(request)
        assert not original.errors and not copied.errors
        assert not original.truncated and not copied.truncated
        assert copied.selected_section_id == original.selected_section_id == section_id
        assert copied.document.source_path == original.document.source_path
        assert copied.content == original.content
    destination = tmp_path / "isolated-harness/skills"

    (result,) = sync_skills(destination, bundle=packaged)
    assert result.status == "installed"
    installed = Path(result.path)
    (source,) = canonical.skill_roots()
    expected = {
        path.relative_to(source).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in canonical.source_paths()
        if path.is_relative_to(source)
    }
    assert SkillSyncReceipt.read(installed).files == expected
    assert {
        path.relative_to(installed).as_posix()
        for path in installed.rglob("*")
        if path.is_file() and path.name != SkillSyncReceipt.filename
    } == expected.keys()
    for relative in expected:
        assert (installed / relative).read_bytes() == (source / relative).read_bytes()
    receipt_time = (installed / SkillSyncReceipt.filename).stat().st_mtime_ns
    assert sync_skills(destination, bundle=packaged)[0].status == "unchanged"
    assert (installed / SkillSyncReceipt.filename).stat().st_mtime_ns == receipt_time


@pytest.mark.parametrize(
    ("declaration", "document_id"),
    (
        (ImageAnalysisWorkflowAuthoringContext, "openhcs_autonomous_analysis_strategy"),
        (CustomFunctionAuthoringContext, "openhcs_custom_function_workflow"),
    ),
)
def test_mcp_analysis_context_routes_from_its_existing_declaration_owner(
    declaration, document_id
):
    targets = declaration.require_route().knowledge_targets
    assert document_id in {
        target.document_id for target in targets
    }
    context = AgentAuthoringContextService().get_authoring_context(
        declaration.require_kind()
    )
    assert document_id in context.content
    guide = KnowledgeBaseService(repo_root=ROOT).get_document(
        KnowledgeBaseDocumentRequest.from_fields(
            document_id=document_id
        )
    )
    assert guide.content not in context.content
