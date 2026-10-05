"""Actual canonical guide -> package knowledge -> retrieval/managed skill bytes.

This is documentation discovery/delivery proof, not an agent decision or native
retirement test. Only the original projection/retrieval/sync owners do work.
"""
from pathlib import Path

from openhcs.agent.dto.knowledge import KnowledgeBaseDocumentRequest, KnowledgeBaseSearchRequest
from openhcs.agent.services.knowledge_base_service import (
    MAX_DOCUMENT_CHARS, KnowledgeBaseService, load_document_specs_from_manifest,
)
from openhcs.agent.skill_bundle import AGENT_PLUGIN_MANIFEST_PATH, AgentSkillBundle
from openhcs.agent.skill_sync import sync_skills
from scripts.build_mcp_knowledge_assets import (
    KNOWLEDGE_MANIFEST_RELATIVE_PATH, project_knowledge_assets,
)


def test_real_viewer_guide_projection_retrieval_and_skill_delivery(tmp_path):
    root = Path(__file__).resolve().parents[3]
    destination = tmp_path / "package-knowledge"
    projected = project_knowledge_assets(root, destination)
    service = KnowledgeBaseService(
        repo_root=destination,
        document_specs=load_document_specs_from_manifest(
            destination / KNOWLEDGE_MANIFEST_RELATIVE_PATH,
        ),
    )
    paths = []
    for document_id in ("openhcs_viewer_qa", "openhcs_viewer_management"):
        reply = service.get_document(KnowledgeBaseDocumentRequest.from_fields(
            document_id=document_id, max_chars=50000,
        ))
        assert not reply.errors and not reply.truncated
        path = Path(reply.document.source_path)
        assert destination / path in projected
        assert (destination / path).read_bytes() == (root / path).read_bytes()
        # The original renderer joins source lines; compare all content, not a
        # wording substring that would pretend to prove the guide's decisions.
        assert reply.content == "\n".join((root / path).read_text().splitlines())
        if document_id == "openhcs_viewer_qa":
            section = next(item for item in reply.sections
                           if item.section_id == "keep-iterative-review-within-its-resource-budget")
            excerpt = service.get_document(KnowledgeBaseDocumentRequest.from_fields(
                document_id=document_id, section_id=section.section_id,
                max_chars=MAX_DOCUMENT_CHARS,
            ))
            assert not excerpt.errors and not excerpt.truncated
            assert excerpt.content == "\n".join(
                (root / path).read_text().splitlines()[section.start_line - 1:section.end_line]
            )
        paths.append(path)
    found = service.search(KnowledgeBaseSearchRequest(query="viewer layer retirement", limit=5))
    assert any(hit.document.document_id == "openhcs_viewer_qa" for hit in found.hits)
    bundle = AgentSkillBundle.from_manifest(destination / AGENT_PLUGIN_MANIFEST_PATH)
    guide = destination / paths[0]
    assert guide in bundle.source_paths()
    managed = tmp_path / "isolated-managed-skills"
    (receipt,) = sync_skills(managed, bundle=bundle)
    assert receipt.status == "installed"
    assert (Path(receipt.path) / "references/viewer-qa.md").read_bytes() == guide.read_bytes()
    assert sync_skills(managed, bundle=bundle)[0].status == "unchanged"
