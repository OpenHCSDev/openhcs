"""Setup opt-in and receipt-enrolled updates share the client declaration owners."""

import json
import shutil
from pathlib import Path

import pytest

from openhcs.agent import skill_sync
from openhcs.agent.runtime_platform import AgentRuntimePlatformKey
from openhcs.agent.skill_bundle import AgentSkillBundle
from openhcs.agent.skill_sync import SkillSyncReceipt, sync_skills
from openhcs.mcp import client_registration
from openhcs.mcp.client_registration import (
    ClientRegistrationEnvironment,
    CodexClientRegistrationTarget,
    McpClientRegistrationTarget,
    McpLauncherSpec,
    refresh_managed_client_skills,
    register_mcp_clients,
)


@pytest.fixture
def bundle(tmp_path, monkeypatch):
    plugin = tmp_path / "plugin"
    manifest = plugin / ".codex-plugin" / "plugin.json"
    manifest.parent.mkdir(parents=True)
    manifest.write_text(json.dumps({"skills": "./skills/"}))
    source = plugin / "skills" / "use-openhcs"
    source.mkdir(parents=True)
    (source / "SKILL.md").write_text("original instructions\n")
    owner = AgentSkillBundle.from_manifest(manifest)
    monkeypatch.setattr(client_registration, "installed_skill_bundle", lambda: owner)
    return owner


@pytest.fixture
def environment(tmp_path):
    def no_process(*args, **kwargs):
        pytest.fail("Skill registration must not launch a process.")

    return ClientRegistrationEnvironment(
        home=tmp_path / "home",
        environ={"CODEX_HOME": str(tmp_path / "custom-codex")},
        platform_key=AgentRuntimePlatformKey.LINUX,
        executable_resolver=lambda _: None,
        process_runner=no_process,
    )


def register(environment, *, sync=False, target="codex"):
    return register_mcp_clients(
        McpLauncherSpec(str(environment.home / "launch-openhcs")),
        required_target_ids=(target,),
        sync_client_skills=sync,
        environment=environment,
    )


def test_setup_without_opt_in_only_registers_mcp(bundle, environment):
    report = register(environment)
    assert report.ok
    assert not report.skill_sync
    assert CodexClientRegistrationTarget.config_path(environment).is_file()
    assert not (environment.home / ".agents").exists()


def test_codex_opt_in_uses_documented_home_not_codex_configuration_home(
    bundle, environment
):
    report = register(environment, sync=True)
    assert report.ok
    (skill_result,) = report.skill_sync
    assert skill_result.target_id == "codex"
    assert skill_result.required
    assert not skill_result.error
    (skill,) = skill_result.results
    assert skill.status == "installed"
    assert skill.path == str(environment.home / ".agents/skills/use-openhcs")
    assert not (
        CodexClientRegistrationTarget.config_path(environment).parent / "skills"
    ).exists()
    assert (
        register(environment, sync=True).skill_sync[0].results[0].status == "unchanged"
    )
    assert report.as_dict()["skill_sync"][0]["results"][0]["status"] == "installed"


def test_unsupported_mcp_client_is_not_assumed_to_support_skills(bundle, environment):
    report = register(environment, sync=True, target="cursor")
    assert report.ok
    assert not report.skill_sync
    assert not (environment.home / ".agents").exists()


@pytest.mark.parametrize("kind", ("custom", "symlink", "dangling"))
def test_legacy_skill_prevents_duplicate_discovery(bundle, environment, kind):
    legacy = (
        CodexClientRegistrationTarget.config_path(environment).parent
        / "skills/use-openhcs"
    )
    legacy.parent.mkdir(parents=True)
    if kind == "custom":
        legacy.mkdir()
        (legacy / "SKILL.md").write_text("user instructions")
    else:
        referent = (
            bundle.skill_roots()[0] if kind == "symlink" else legacy.parent / "absent"
        )
        legacy.symlink_to(referent, target_is_directory=True)
    before = legacy.lstat()
    report = register(environment, sync=True)
    assert not report.ok
    assert not report.required_ok
    assert report.results[0].status == "registered"  # MCP did succeed.
    assert "duplicate discovery" in report.skill_sync[0].error
    assert legacy.lstat() == before
    assert not (environment.home / ".agents").exists()


def test_custom_default_skill_is_preserved_and_failure_is_separate(bundle, environment):
    skill = environment.home / ".agents/skills/use-openhcs"
    skill.mkdir(parents=True)
    (skill / "SKILL.md").write_text("user instructions")
    report = register(environment, sync=True)
    assert report.results[0].status == "registered"
    assert not report.required_ok
    assert "Unmanaged" in report.skill_sync[0].error
    assert (skill / "SKILL.md").read_text() == "user instructions"
    assert not (skill / SkillSyncReceipt.filename).exists()


def test_refresh_does_not_enrol_absent_or_unmanaged_skills(bundle, environment):
    assert refresh_managed_client_skills(environment=environment) == ()
    assert not environment.home.exists()
    skill = environment.home / ".agents/skills/use-openhcs"
    skill.mkdir(parents=True)
    (skill / "SKILL.md").write_text("user instructions")
    assert refresh_managed_client_skills(environment=environment) == ()
    assert (skill / "SKILL.md").read_text() == "user instructions"
    assert not CodexClientRegistrationTarget.config_path(environment).exists()


def test_receipt_enrolled_refresh_updates_and_keeps_backup_without_registering_mcp(
    bundle, environment
):
    directory = CodexClientRegistrationTarget.skill_directory(environment)
    sync_skills(directory, bundle=bundle)
    (bundle.skill_roots()[0] / "SKILL.md").write_text("new instructions\n")
    (result,) = refresh_managed_client_skills(environment=environment)
    assert not result.error
    (skill,) = result.results
    assert skill.status == "updated"
    assert (Path(skill.path) / "SKILL.md").read_text() == "new instructions\n"
    assert (
        Path(skill.backup_path) / "SKILL.md"
    ).read_text() == "original instructions\n"
    assert not CodexClientRegistrationTarget.config_path(environment).exists()
    assert (
        refresh_managed_client_skills(environment=environment)[0].results[0].status
        == "unchanged"
    )


@pytest.mark.parametrize("kind", ("modified", "malformed", "symlink"))
def test_refresh_refuses_changed_receipt_enrolled_tree(
    bundle, environment, tmp_path, kind
):
    directory = CodexClientRegistrationTarget.skill_directory(environment)
    sync_skills(directory, bundle=bundle)
    target = directory / "use-openhcs"
    if kind == "modified":
        (target / "SKILL.md").write_text("user edit")
    elif kind == "malformed":
        (target / SkillSyncReceipt.filename).write_text("bad json")
    else:
        referent = tmp_path / "referent"
        target.rename(referent)
        target.symlink_to(referent, target_is_directory=True)
    before = (target / "SKILL.md").read_bytes()
    (result,) = refresh_managed_client_skills(environment=environment)
    assert result.error
    assert not result.results
    assert (target / "SKILL.md").read_bytes() == before
    assert not list(directory.glob(".use-openhcs.openhcs-backup-*"))


def test_skill_failure_does_not_erase_successful_mcp_registration(
    bundle, environment, monkeypatch
):
    def failed_sync(*args, **kwargs):
        raise PermissionError("destination not writable")

    monkeypatch.setattr(client_registration, "sync_skills", failed_sync)
    report = register(environment, sync=True)
    assert report.results[0].status == "registered"
    assert not report.ok
    assert "not writable" in report.skill_sync[0].error


def test_empty_exception_message_still_reports_failure(bundle, environment, monkeypatch):
    def failure(*args, **kwargs):
        raise RuntimeError()

    monkeypatch.setattr(client_registration, "sync_skills", failure)
    report = register(environment, sync=True)
    assert report.skill_sync[0].error == ""
    assert not report.ok
    assert not report.required_ok


@pytest.mark.parametrize("unmanaged_sibling", (False, True))
def test_receipt_refresh_does_not_install_or_modify_unenrolled_sibling(
    bundle,
    environment,
    unmanaged_sibling,
):
    directory = CodexClientRegistrationTarget.skill_directory(environment)
    sync_skills(directory, bundle=bundle)
    new_source = bundle.skills_root / "z-next"
    new_source.mkdir()
    (new_source / "SKILL.md").write_text("new optional skill")
    sibling = directory / new_source.name
    if unmanaged_sibling:
        sibling.mkdir()
        (sibling / "SKILL.md").write_text("user-owned sibling")
    (bundle.skill_roots()[0] / "SKILL.md").write_text("updated instructions")
    (result,) = refresh_managed_client_skills(environment=environment)
    assert not result.error
    assert len(result.results) == 1
    assert result.results[0].status == "updated"
    assert Path(result.results[0].path).name == "use-openhcs"
    if unmanaged_sibling:
        assert (sibling / "SKILL.md").read_text() == "user-owned sibling"
    else:
        assert not sibling.exists()


def test_later_skill_failure_keeps_earlier_publication_in_report(
    bundle, environment, monkeypatch
):
    second = bundle.skills_root / "z-next"
    second.mkdir()
    (second / "SKILL.md").write_text("second skill")
    original = shutil.copytree

    def fail_second(source, target, **kwargs):
        if Path(source).name == "z-next":
            raise PermissionError("second skill not writable")
        return original(source, target, **kwargs)

    monkeypatch.setattr(shutil, "copytree", fail_second)
    report = register(environment, sync=True)
    assert not report.ok
    (result,) = report.skill_sync
    assert "second skill not writable" in result.error
    assert len(result.results) == 1
    assert result.results[0].status == "installed"
    assert (Path(result.results[0].path) / SkillSyncReceipt.filename).is_file()
    assert not (
        CodexClientRegistrationTarget.skill_directory(environment) / "z-next"
    ).exists()


def test_failed_mcp_registration_does_not_install_skills(bundle, environment):
    config = CodexClientRegistrationTarget.config_path(environment)
    config.parent.mkdir(parents=True)
    config.write_text("[broken toml")
    report = register(environment, sync=True)
    assert report.results[0].status == "failed"
    assert not report.skill_sync
    assert not (environment.home / ".agents").exists()


def test_explicit_sync_cli_reports_earlier_publications_on_later_failure(
    bundle,
    environment,
    monkeypatch,
    capsys,
):
    second = bundle.skills_root / "z-next"
    second.mkdir()
    (second / "SKILL.md").write_text("second skill")
    original = shutil.copytree

    def fail_second(source, target, **kwargs):
        if Path(source).name == "z-next":
            raise PermissionError("second skill not writable")
        return original(source, target, **kwargs)

    monkeypatch.setattr(shutil, "copytree", fail_second)
    monkeypatch.setattr(skill_sync, "installed_skill_bundle", lambda: bundle)
    directory = CodexClientRegistrationTarget.skill_directory(environment)
    assert skill_sync.main(["sync", "--skills-dir", str(directory)]) == 1
    report = json.loads(capsys.readouterr().out)
    assert not report["ok"]
    assert "second skill not writable" in report["error"]
    assert report["results"][0]["status"] == "installed"
    assert Path(report["results"][0]["path"]).name == "use-openhcs"


def test_new_client_skill_capability_is_driven_by_its_declaration(
    bundle, environment, monkeypatch
):
    monkeypatch.setattr(
        McpClientRegistrationTarget,
        "__registry__",
        dict(McpClientRegistrationTarget.__registry__),
    )

    class TestHarness(McpClientRegistrationTarget):
        target_id = "test-harness-skills"
        display_name = "Test harness"

        @classmethod
        def detected(cls, environment):
            return False

        @classmethod
        def skill_directory(cls, environment):
            return environment.home / "test-harness/skills"

        @classmethod
        def register(cls, launcher, environment):
            return client_registration.ClientConfigMutation(
                client_registration.ClientRegistrationStatus.REGISTERED,
                None,
                None,
                "registered test harness",
            )

    report = register(environment, sync=True, target=TestHarness.target_id)
    assert report.ok
    assert report.skill_sync[0].results[0].path == str(
        environment.home / "test-harness/skills/use-openhcs"
    )
    assert not (environment.home / ".agents").exists()


def test_cli_requires_explicit_skill_sync_flag(
    bundle, environment, monkeypatch, capsys
):
    monkeypatch.setattr(
        ClientRegistrationEnvironment, "current", classmethod(lambda cls: environment)
    )
    assert (
        client_registration.main(
            [
                "--command",
                str(environment.home / "launch-openhcs"),
                "--register",
                "codex",
                "--sync-skills",
                "--json",
            ]
        )
        == 0
    )
    report = json.loads(capsys.readouterr().out)
    assert report["ok"]
    assert report["skill_sync"][0]["results"][0]["status"] == "installed"
