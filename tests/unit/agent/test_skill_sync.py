"""Resource-driven skill installation never clobbers local or redirected trees."""

import json
import os
import shutil
from pathlib import Path

import pytest

from openhcs.agent.skill_bundle import AgentSkillBundle
from openhcs.agent.skill_sync import SkillSyncReceipt, sync_skills


@pytest.fixture
def bundle(tmp_path):
    root = tmp_path / "plugin"
    manifest = root / ".codex-plugin" / "plugin.json"
    manifest.parent.mkdir(parents=True)
    manifest.write_text(json.dumps({"skills": "./skills/"}))
    skill = root / "skills" / "use-openhcs"
    (skill / "references").mkdir(parents=True)
    (skill / "SKILL.md").write_text("source skill\n")
    (skill / "references" / "guide.md").write_text("source guidance\n")
    return AgentSkillBundle.from_manifest(manifest)


def test_complete_install_and_idempotence(bundle, tmp_path):
    destination = tmp_path / "harness" / "skills"
    (result,) = sync_skills(destination, bundle=bundle)
    target = Path(result.path)
    assert result.status == "installed"
    assert (target / "SKILL.md").read_text() == "source skill\n"
    assert (target / "references" / "guide.md").read_text() == "source guidance\n"
    assert SkillSyncReceipt.read(target).files.keys() == {
        "SKILL.md",
        "references/guide.md",
    }
    before = (target / SkillSyncReceipt.filename).stat().st_mtime_ns
    assert sync_skills(destination, bundle=bundle)[0].status == "unchanged"
    assert (target / SkillSyncReceipt.filename).stat().st_mtime_ns == before


def test_dry_run_has_no_filesystem_side_effect(bundle, tmp_path):
    destination = tmp_path / "absent" / "skills"
    assert (
        sync_skills(destination, bundle=bundle, dry_run=True)[0].status
        == "would_install"
    )
    assert not destination.parent.exists()


def test_update_retains_recoverable_previous_tree(bundle, tmp_path):
    destination = tmp_path / "skills"
    (first,) = sync_skills(destination, bundle=bundle)
    (bundle.skill_roots()[0] / "references" / "guide.md").write_text(
        "updated guidance\n"
    )
    (result,) = sync_skills(destination, bundle=bundle)
    assert result.status == "updated"
    assert (
        Path(result.path) / "references" / "guide.md"
    ).read_text() == "updated guidance\n"
    assert (
        Path(result.backup_path) / "references" / "guide.md"
    ).read_text() == "source guidance\n"
    assert first.path == result.path


@pytest.mark.parametrize(
    "mutation", ("custom", "changed", "added", "deleted", "symlink", "dangling")
)
def test_custom_and_modified_skills_are_preserved(bundle, tmp_path, mutation):
    destination = tmp_path / "skills"
    target = destination / "use-openhcs"
    if mutation == "custom":
        target.mkdir(parents=True)
        (target / "SKILL.md").write_text("custom skill")
    elif mutation in ("symlink", "dangling"):
        destination.mkdir()
        referent = (
            bundle.skill_roots()[0] if mutation == "symlink" else tmp_path / "missing"
        )
        target.symlink_to(referent, target_is_directory=True)
    else:
        sync_skills(destination, bundle=bundle)
        if mutation == "changed":
            (target / "SKILL.md").write_text("custom changes")
        elif mutation == "added":
            (target / "extra.md").write_text("custom additions")
        else:
            (target / "references" / "guide.md").unlink()
    before = [
        (path.relative_to(destination), path.lstat().st_mtime_ns)
        for path in destination.rglob("*")
    ]
    with pytest.raises(ValueError):
        sync_skills(destination, bundle=bundle)
    after = [
        (path.relative_to(destination), path.lstat().st_mtime_ns)
        for path in destination.rglob("*")
    ]
    assert before == after
    assert not list(destination.glob(".use-openhcs-*"))


def test_redirected_ancestor_is_not_followed(bundle, tmp_path):
    real = tmp_path / "real"
    real.mkdir()
    redirected = tmp_path / "redirected"
    redirected.symlink_to(real, target_is_directory=True)
    with pytest.raises(ValueError, match="redirected"):
        sync_skills(redirected / "skills", bundle=bundle)
    assert not list(real.iterdir())


@pytest.mark.parametrize("nested", (False, True))
def test_source_destination_overlap_is_rejected(bundle, nested):
    source = bundle.skill_roots()[0]
    destination = source / "nested" if nested else source.parent
    with pytest.raises(ValueError, match="overlap"):
        sync_skills(destination, bundle=bundle)
    assert not (source / "nested").exists()


def test_failed_publication_restores_old_skill(bundle, tmp_path, monkeypatch):
    destination = tmp_path / "skills"
    sync_skills(destination, bundle=bundle)
    (bundle.skill_roots()[0] / "SKILL.md").write_text("new skill\n")
    original = os.replace

    def fail_publish(source, target):
        if Path(source).name.startswith(".use-openhcs-"):
            raise OSError("publication failed")
        return original(source, target)

    monkeypatch.setattr(os, "replace", fail_publish)
    with pytest.raises(OSError, match="publication failed"):
        sync_skills(destination, bundle=bundle)
    assert (destination / "use-openhcs" / "SKILL.md").read_text() == "source skill\n"
    assert not list(destination.glob(".use-openhcs*"))


def test_redirected_source_is_rejected_before_install(bundle, tmp_path):
    source = bundle.skill_roots()[0]
    (source / "references" / "escape.md").symlink_to(tmp_path / "absent")
    destination = tmp_path / "skills"
    with pytest.raises(ValueError, match="symlink"):
        sync_skills(destination, bundle=bundle)
    assert not destination.exists()


def test_source_change_during_copy_cannot_publish_false_receipt(
    bundle, tmp_path, monkeypatch
):
    original = shutil.copytree

    def mutate_source(source, destination, *args, **kwargs):
        if Path(source) == bundle.skill_roots()[0]:
            (Path(source) / "SKILL.md").write_text("changed during staging")
        return original(source, destination, *args, **kwargs)

    monkeypatch.setattr(shutil, "copytree", mutate_source)
    destination = tmp_path / "skills"
    with pytest.raises(ValueError, match="source changed"):
        sync_skills(destination, bundle=bundle)
    assert not list(destination.iterdir())


def test_parent_redirect_during_staging_cannot_publish_or_clean_foreign_tree(
    bundle, tmp_path, monkeypatch
):
    destination = tmp_path / "skills"
    sync_skills(destination, bundle=bundle)
    (bundle.skill_roots()[0] / "SKILL.md").write_text("new skill")
    foreign = tmp_path / "foreign"
    shutil.copytree(destination, foreign)
    original = shutil.copytree

    def redirect_parent(source, stage, *args, **kwargs):
        result = original(source, stage, *args, **kwargs)
        if Path(source) != bundle.skill_roots()[0]:
            return result
        destination.rename(tmp_path / "original-skills")
        destination.symlink_to(foreign, target_is_directory=True)
        (foreign / Path(stage).name).mkdir()
        (foreign / Path(stage).name / "sentinel").write_text("preserve")
        return result

    monkeypatch.setattr(shutil, "copytree", redirect_parent)
    with pytest.raises(ValueError, match="redirected"):
        sync_skills(destination, bundle=bundle)
    assert (foreign / "use-openhcs" / "SKILL.md").read_text() == "source skill\n"
    assert next(foreign.glob(".use-openhcs-*/sentinel")).read_text() == "preserve"
    assert (
        tmp_path / "original-skills/use-openhcs/SKILL.md"
    ).read_text() == "source skill\n"


def test_redirected_stage_cannot_overwrite_foreign_receipt(
    bundle, tmp_path, monkeypatch
):
    foreign = tmp_path / "foreign"
    shutil.copytree(bundle.skill_roots()[0], foreign)
    (foreign / SkillSyncReceipt.filename).write_text("foreign receipt sentinel")
    original = shutil.copytree

    def redirect_stage(source, stage, *args, **kwargs):
        result = original(source, stage, *args, **kwargs)
        if Path(source) != bundle.skill_roots()[0]:
            return result
        Path(stage).rename(Path(stage).with_name(Path(stage).name + "-original"))
        Path(stage).symlink_to(foreign, target_is_directory=True)
        return result

    monkeypatch.setattr(shutil, "copytree", redirect_stage)
    destination = tmp_path / "skills"
    with pytest.raises(ValueError, match="redirected"):
        sync_skills(destination, bundle=bundle)
    assert not (destination / "use-openhcs").exists()
    assert (
        foreign / SkillSyncReceipt.filename
    ).read_text() == "foreign receipt sentinel"
