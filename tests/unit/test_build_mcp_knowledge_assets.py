"""Tests for build-only MCP knowledge projection."""

import glob
import json
import tomllib
from pathlib import Path

import pytest

from scripts.build_mcp_knowledge_assets import (
    KNOWLEDGE_MANIFEST_RELATIVE_PATH,
    PACKAGED_KNOWLEDGE_ROOT_RELATIVE_PATH,
    project_knowledge_assets,
)


def _project_with_document(tmp_path):
    project_root = tmp_path / "project"
    manifest_path = project_root / KNOWLEDGE_MANIFEST_RELATIVE_PATH
    document_path = project_root / "docs" / "guide.rst"
    manifest_path.parent.mkdir(parents=True)
    document_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(
        json.dumps(
            {
                "documents": [
                    {
                        "document_id": "guide",
                        "title": "Guide",
                        "summary": "Guide summary",
                        "source_path": "docs/guide.rst",
                        "tags": ["guide"],
                        "section_count": 1,
                    }
                ]
            }
        ),
        encoding="utf-8",
    )
    document_path.write_text("Guide\n=====\n", encoding="utf-8")
    return project_root, manifest_path, document_path


def test_projection_copies_only_manifest_declared_sources(tmp_path):
    project_root, manifest_path, document_path = _project_with_document(tmp_path)
    destination = tmp_path / "wheel" / "knowledge"

    projected = project_knowledge_assets(project_root, destination)

    assert projected == (
        destination / manifest_path.relative_to(project_root),
        destination / document_path.relative_to(project_root),
    )
    assert (destination / "docs" / "guide.rst").read_text(encoding="utf-8") == (
        "Guide\n=====\n"
    )


def test_projection_rejects_checked_in_mirror(tmp_path):
    project_root, _, _ = _project_with_document(tmp_path)

    with pytest.raises(ValueError, match="build output"):
        project_knowledge_assets(
            project_root,
            project_root / PACKAGED_KNOWLEDGE_ROOT_RELATIVE_PATH,
        )


def test_projection_rejects_project_ancestor(tmp_path):
    project_root, _, _ = _project_with_document(tmp_path)

    with pytest.raises(ValueError, match="must not own"):
        project_knowledge_assets(project_root, tmp_path)


def test_projection_cannot_delete_a_declared_source_directory(tmp_path):
    project_root, _, document = _project_with_document(tmp_path)
    with pytest.raises(ValueError, match="canonical sources"):
        project_knowledge_assets(project_root, project_root / "docs")
    assert document.read_text() == "Guide\n=====\n"


def test_projection_cannot_delete_a_symlink_referent(tmp_path):
    project_root, _, _ = _project_with_document(tmp_path)
    real = tmp_path / "unmanaged"
    real.mkdir()
    sentinel = real / "sentinel"
    sentinel.write_text("preserve")
    link = tmp_path / "redirected"
    link.symlink_to(real, target_is_directory=True)
    with pytest.raises(ValueError, match="redirected"):
        project_knowledge_assets(project_root, link)
    assert sentinel.read_text() == "preserve"


def test_projection_includes_complete_declared_plugin_skill(tmp_path):
    project_root, _, _ = _project_with_document(tmp_path)
    plugin = project_root / "packaging/codex/openhcs"
    manifest = plugin / ".codex-plugin/plugin.json"
    manifest.parent.mkdir(parents=True)
    manifest.write_text(json.dumps({"skills": "./skills/"}))
    skill = plugin / "skills/use-openhcs"
    (skill / "agents").mkdir(parents=True)
    (skill / "references").mkdir()
    for relative, content in (
        ("SKILL.md", "entrypoint"),
        ("agents/openai.yaml", "metadata"),
        ("references/not-a-knowledge-document.md", "skill-only guidance"),
    ):
        (skill / relative).write_text(content)
    destination = tmp_path / "wheel/knowledge"
    project_knowledge_assets(project_root, destination)
    for relative in (
        "SKILL.md",
        "agents/openai.yaml",
        "references/not-a-knowledge-document.md",
    ):
        source = skill / relative
        assert (
            destination / source.relative_to(project_root)
        ).read_bytes() == source.read_bytes()
    assert (destination / manifest.relative_to(project_root)).is_file()


def test_wheel_globs_include_the_projected_hidden_plugin_manifest(tmp_path):
    project_root = Path(__file__).resolve().parents[2]
    package_root = tmp_path / "openhcs"
    knowledge = package_root / "agent/resources/knowledge"
    projected = project_knowledge_assets(project_root, knowledge)
    plugin_manifest = next(
        path
        for path in projected
        if path.parts[-2:] == (".codex-plugin", "plugin.json")
    )
    config = tomllib.loads((project_root / "pyproject.toml").read_text())
    patterns = config["tool"]["setuptools"]["package-data"]["openhcs"]
    included = {
        Path(path)
        for pattern in patterns
        for path in glob.glob(str(package_root / pattern), recursive=True)
    }
    assert plugin_manifest in included
