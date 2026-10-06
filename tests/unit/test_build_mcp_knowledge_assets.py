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
from openhcs.agent.knowledge_manifest_schema import (
    ComparisonManifestSnapshot,
    PackagedComparisonManifestSnapshot,
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


@pytest.mark.parametrize("native_count", [1, 2])
def test_native_recipe_closure_agrees_across_all_consumers(
    tmp_path, monkeypatch, native_count
):
    from openhcs.agent import knowledge_manifest
    from openhcs.agent.dto.knowledge import KnowledgeBaseDocumentRequest
    from openhcs.agent.services import knowledge_base_service

    project_root, manifest_path, _ = _project_with_document(tmp_path)
    recipe_path = project_root / "benchmark/manifests/synthetic.json"
    recipe_path.parent.mkdir(parents=True)
    native_root = project_root / "native"
    native_root.mkdir()
    native_files = []
    for index in range(native_count):
        path = native_root / f"source{index}.cppipe"
        path.write_text(
            "CellProfiler Pipeline: http://www.cellprofiler.org\nVersion:5\n"
            "ModuleCount:0\nHasImagePlaneDetails:False\n",
            encoding="utf-8",
        )
        native_files.append(path)
    # Non-image sentinels stand for excluded raw/answer files, not scientific data.
    (native_root / "raw.tif").write_text("raw sentinel", encoding="utf-8")
    (native_root / "expected.csv").write_text("answer sentinel", encoding="utf-8")
    payload = {
        "path_roots": {
            "native": {"env": "KNOWLEDGE_TEST_NATIVE_ROOT", "default": "native"},
            "dataset": {"default": "external-data"},
        },
        "cases": [
            {
                "name": f"Synthetic {index}",
                "cppipe_path_root": "native",
                "cppipe_path": path.name,
                "dataset_path_root": "dataset",
                "dataset_path": ".",
            }
            for index, path in enumerate(native_files)
        ],
    }
    recipe_path.write_text(json.dumps(payload), encoding="utf-8")
    catalog = json.loads(manifest_path.read_text(encoding="utf-8"))
    catalog["documents"].append(
        {
            "document_id": "synthetic_recipes",
            "title": "Synthetic sources",
            "summary": "Resource-closure contract",
            "tags": ["synthetic"],
            "source_path": "benchmark/manifests/synthetic.json",
            "section_count": 0,
        }
    )
    manifest_path.write_text(json.dumps(catalog), encoding="utf-8")
    monkeypatch.delenv("KNOWLEDGE_TEST_NATIVE_ROOT", raising=False)
    elsewhere = tmp_path / "unrelated-cwd"
    elsewhere.mkdir()
    monkeypatch.chdir(elsewhere)
    original = ComparisonManifestSnapshot.load(recipe_path, source_root=project_root)
    assert tuple(original.native_source_projections().values()) == tuple(native_files)
    destination = tmp_path / "site-packages/openhcs/agent/resources/knowledge"
    projected = project_knowledge_assets(project_root, destination)
    assert (
        destination / recipe_path.relative_to(project_root)
    ).read_bytes() == recipe_path.read_bytes()
    assert sum(path.suffix == ".cppipe" for path in projected) == native_count
    assert not any(path.suffix in {".tif", ".csv"} for path in projected)
    installed = PackagedComparisonManifestSnapshot.load(
        destination / recipe_path.relative_to(project_root), source_root=destination
    )
    for case, original_file in zip(installed.cases, native_files):
        assert (
            installed.native_source_path(case).read_bytes()
            == original_file.read_bytes()
        )
    monkeypatch.setattr(
        knowledge_manifest, "packaged_knowledge_base_root", lambda: destination
    )
    monkeypatch.setenv(
        "KNOWLEDGE_TEST_NATIVE_ROOT", str(tmp_path / "unavailable-cache")
    )
    membership = knowledge_manifest.knowledge_base_source_paths_from_manifest(
        destination / KNOWLEDGE_MANIFEST_RELATIVE_PATH
    )
    installed_native = tuple(
        installed.native_source_path(case) for case in installed.cases
    )
    assert set(installed_native).issubset(membership)
    specs = knowledge_base_service.load_document_specs_from_manifest(
        destination / KNOWLEDGE_MANIFEST_RELATIVE_PATH
    )
    service = knowledge_base_service.KnowledgeBaseService(
        repo_root=destination, document_specs=specs
    )
    calls = []
    monkeypatch.setattr(
        knowledge_base_service,
        "_official30_public_source",
        lambda path, dataset: calls.append((Path(path), Path(dataset)))
        or "pipeline_config = None\npipeline_steps = []",
    )
    for index, path in enumerate(installed_native):
        result = service.get_document(
            KnowledgeBaseDocumentRequest.from_fields(
                document_id="synthetic_recipes",
                section_id=f"synthetic-{index}-openhcs-python",
                max_chars=50000,
            )
        )
        assert result.errors == ()
        assert result.content and not result.truncated
        assert calls[-1] == (path, destination / "external-data")
        catalog_result = service.get_document(
            KnowledgeBaseDocumentRequest.from_fields(
                document_id="synthetic_recipes",
                section_id=f"synthetic-{index}",
            )
        )
        assert f"resolved_cppipe_path: {path}" in catalog_result.content


@pytest.mark.parametrize(
    "native_path",
    ["missing.cppipe", "../escape.cppipe", "/absolute.cppipe", "expected.csv"],
)
def test_native_closure_failure_preserves_existing_destination(tmp_path, native_path):
    project_root, manifest_path, _ = _project_with_document(tmp_path)
    recipe_path = project_root / "recipe.json"
    recipe_path.write_text(
        json.dumps(
            {
                "cases": [{"name": "Missing", "cppipe_path": native_path}],
            }
        ),
        encoding="utf-8",
    )
    catalog = json.loads(manifest_path.read_text(encoding="utf-8"))
    catalog["documents"].append({"source_path": "recipe.json"})
    manifest_path.write_text(json.dumps(catalog), encoding="utf-8")
    destination = tmp_path / "existing-projection"
    destination.mkdir()
    sentinel = destination / "preserved.txt"
    sentinel.write_text("existing resource", encoding="utf-8")
    with pytest.raises((ValueError, FileNotFoundError)):
        project_knowledge_assets(project_root, destination)
    assert sentinel.read_text(encoding="utf-8") == "existing resource"


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
    plugin_root = plugin_manifest.parent.parent
    assert {path for path in projected if path.is_relative_to(plugin_root)} <= included
