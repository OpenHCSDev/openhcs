"""Exercise task retrieval and installable projection, not prose acceptance."""

import re
import runpy
from pathlib import Path

import pytest

from openhcs.agent.authoring_contexts import ImageAnalysisWorkflowAuthoringContext
from openhcs.agent.dto.knowledge import (
    KnowledgeBaseDocumentRequest,
    KnowledgeBaseSearchRequest,
)
from openhcs.agent.services.knowledge_base_service import KnowledgeBaseService
from openhcs.agent.services.llm_context_service import AgentAuthoringContextService

ROOT = Path(__file__).resolve().parents[3]
TASKS = (
    ("autonomous analysis strategy", "openhcs_autonomous_analysis_strategy"),
    ("channel identity RGB composite", "openhcs_image_interpretation"),
    ("uneven background additive subtraction", "openhcs_image_preprocessing"),
    ("nucleus split watershed", "openhcs_segmentation_diagnostics"),
    ("zero growth cytoplasm", "openhcs_segmentation_diagnostics"),
    ("volume anisotropic Z spacing", "openhcs_measurement_interpretation"),
    ("Pearson Manders Costes", "openhcs_measurement_interpretation"),
    ("recipe error memory", "openhcs_analysis_learning"),
    ("canvas resize recapture", "openhcs_viewer_qa"),
    ("blind recipe promotion", "openhcs_blind_recipe_promotion"),
)


@pytest.mark.parametrize(("query", "document_id"), TASKS)
def test_task_retrieval_reaches_a_bounded_canonical_source(query, document_id):
    service = KnowledgeBaseService(repo_root=ROOT)
    hits = service.search(KnowledgeBaseSearchRequest(query=query, limit=10))
    assert not hits.errors
    assert document_id in {hit.document.document_id for hit in hits.hits}

    document = service.get_document(
        KnowledgeBaseDocumentRequest.from_fields(
            document_id=document_id, max_chars=12_000
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
                document_id=document_id, max_chars=12_000
            )
        )
        assert not document.errors
        assert not document.truncated
        source_path = Path(document.document.source_path)
        assert destination / source_path in paths
        assert (destination / source_path).read_bytes() == (
            ROOT / source_path
        ).read_bytes()
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
    assert len(transferred) == 8
    assert len({document.source_path for document in transferred.values()}) == 8
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


def test_mcp_analysis_context_routes_from_its_existing_declaration_owner():
    declaration = ImageAnalysisWorkflowAuthoringContext
    targets = declaration.require_route().knowledge_targets
    assert "openhcs_autonomous_analysis_strategy" in {
        target.document_id for target in targets
    }
    context = AgentAuthoringContextService().get_authoring_context(
        declaration.require_kind()
    )
    assert "openhcs_autonomous_analysis_strategy" in context.content
    guide = KnowledgeBaseService(repo_root=ROOT).get_document(
        KnowledgeBaseDocumentRequest.from_fields(
            document_id="openhcs_autonomous_analysis_strategy"
        )
    )
    assert guide.content not in context.content
