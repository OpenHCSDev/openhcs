"""Guardrail-tool tests, independent of the application test environment."""

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest
import yaml

from scripts.check_refactor_r1 import compare, git, scan_counts

REPO = Path(__file__).resolve().parents[2]


def commit(repo: Path, path: str, text: str) -> str:
    file = repo / path
    file.parent.mkdir(parents=True, exist_ok=True)
    file.write_text(text)
    git(repo, "add", path)
    git(
        repo,
        "-c",
        "user.name=R0 fixture",
        "-c",
        "user.email=r0@example.invalid",
        "commit",
        "-qm",
        "controlled source",
    )
    return git(repo, "rev-parse", "HEAD").decode().strip()


@pytest.fixture
def repository(tmp_path: Path) -> Path:
    repo = tmp_path / "repo"
    repo.mkdir()
    git(repo, "init", "-q")
    commit(repo, "openhcs/__init__.py", "")
    return repo


SCHEMA = """from dataclasses import dataclass
@dataclass
class Record:
    alpha: str
    beta: int
    gamma: str
"""
RAW = "def consume(row):\n    return row['alpha'], row.get('beta'), row['gamma']\n"
DECODE = """from openhcs.model import Record
def consume(row):
    return Record(alpha=row['alpha'], beta=int(row['beta']), gamma=row.get('gamma'))
"""


def test_r1_uses_cross_module_schema_and_original_constructor_descent(
    repository, tmp_path
):
    commit(repository, "openhcs/model.py", SCHEMA)
    base = commit(repository, "openhcs/consumer.py", DECODE)
    head = commit(repository, "openhcs/consumer.py", RAW)
    result = compare(repository, base, head, tmp_path / "scratch")
    assert not result.before
    assert [(item.check, item.file, item.count) for item in result.increased] == [
        ("mapping_read", "openhcs/consumer.py", 1)
    ]
    # Unchanged schema context is retained, so this is NOT unmodeled_record_shape.
    assert {item.check for item in result.after} == {"mapping_read"}
    restored = commit(repository, "openhcs/consumer.py", DECODE)
    assert not compare(repository, head, restored, tmp_path / "scratch").increased
    assert not tuple((tmp_path / "scratch").iterdir())


def test_r1_unmodeled_and_declared_attribute_checks_are_native_findings(
    repository, tmp_path
):
    base = git(repository, "rev-parse", "HEAD").decode().strip()
    commit(repository, "openhcs/raw.py", RAW)
    head = commit(
        repository,
        "openhcs/typed.py",
        SCHEMA
        + """
def check(row: Record):
    return isinstance(row.alpha, str)
""",
    )
    result = compare(repository, base, head, tmp_path / "scratch")
    assert {(item.check, item.file) for item in result.increased} == {
        ("mapping_read", "openhcs/raw.py"),
        ("redundant_type_check", "openhcs/typed.py"),
    }
    # Removing the declared schema changes the same read to genuinely unmodeled.
    git(repository, "rm", "openhcs/typed.py")
    git(
        repository,
        "-c",
        "user.name=R0 fixture",
        "-c",
        "user.email=r0@example.invalid",
        "commit",
        "-qm",
        "remove schema",
    )
    unmodeled = compare(repository, head, "HEAD", tmp_path / "scratch")
    assert {item.check for item in unmodeled.increased} == set()
    # An unchanged consumer is not reported just because its context changed.
    snapshot = tmp_path / "source"
    (snapshot / "openhcs").mkdir(parents=True)
    (snapshot / "openhcs" / "raw.py").write_text(RAW)
    assert {
        item.check for item in scan_counts(snapshot, ("openhcs",), ("openhcs/raw.py",))
    } == {"unmodeled_record_shape"}


def test_no_changed_python_is_explicit_empty_scope_without_dependency_start(
    repository, tmp_path
):
    base = git(repository, "rev-parse", "HEAD").decode().strip()
    head = commit(repository, "docs/note.md", "planning only")
    result = compare(repository, base, head, tmp_path / "not-created")
    assert result.changed == ()
    assert not result.increased
    assert not (tmp_path / "not-created").exists()


@pytest.mark.parametrize("source,increased", [("", False), (RAW, True)])
def test_actual_r1_cli_json_and_exit_status(repository, tmp_path, source, increased):
    base = git(repository, "rev-parse", "HEAD").decode().strip()
    head = commit(repository, "openhcs/read.py", source)
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "scripts.check_refactor_r1",
            "--base",
            base,
            "--head",
            head,
            "--scratch-root",
            str(tmp_path / "scratch"),
        ],
        cwd=repository,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == int(increased), result.stderr
    payload = json.loads(result.stdout)
    assert bool(payload["increased"]) is increased
    assert payload["head"] == head


def test_missing_recorded_dependency_is_not_silently_parent_source(
    repository, tmp_path
):
    base = git(repository, "rev-parse", "HEAD").decode().strip()
    commit(repository, "openhcs/read.py", RAW)
    git(
        repository,
        "update-index",
        "--add",
        "--cacheinfo",
        f"160000,{base},external/dependency",
    )
    git(
        repository,
        "-c",
        "user.name=R0 fixture",
        "-c",
        "user.email=r0@example.invalid",
        "commit",
        "-qm",
        "record missing dependency",
    )
    (repository / "external" / "dependency").mkdir(parents=True)
    with pytest.raises(RuntimeError, match="not initialized"):
        compare(repository, base, "HEAD", tmp_path / "scratch")


def test_r1_parse_failure_and_deadline_are_not_clean_results(repository, tmp_path):
    base = git(repository, "rev-parse", "HEAD").decode().strip()
    bad = commit(repository, "openhcs/bad.py", "def broken(:\n")
    with pytest.raises(SyntaxError):
        compare(repository, base, bad, tmp_path / "scratch")
    good = commit(repository, "openhcs/bad.py", RAW)
    with pytest.raises(TimeoutError):
        compare(repository, base, good, tmp_path / "scratch", budget_seconds=0)
    assert not tuple((tmp_path / "scratch").iterdir())


def test_per_file_growth_cannot_be_hidden_by_another_file_reduction(
    repository, tmp_path
):
    commit(repository, "openhcs/a.py", RAW)
    base = commit(repository, "openhcs/b.py", "")
    commit(repository, "openhcs/a.py", "")
    head = commit(repository, "openhcs/b.py", RAW)
    result = compare(repository, base, head, tmp_path / "scratch")
    assert [(item.file, item.count) for item in result.increased] == [
        ("openhcs/b.py", 1)
    ]


def workflow() -> dict:
    return yaml.load(
        (REPO / ".github/workflows/integration-tests.yml").read_text(),
        Loader=yaml.BaseLoader,
    )


@pytest.mark.parametrize(
    "path,relevant",
    [
        ("openhcs/core/fixture.py", "true"),
        ("openhcs/processing/fixture.py", "true"),
        ("openhcs/formats/fixture.py", "true"),
        ("openhcs/interop/cellprofiler/fixture.py", "true"),
        ("docs/note.md", "false"),
    ],
)
def test_actual_parity_scope_shell(repository, tmp_path, path, relevant):
    base = git(repository, "rev-parse", "HEAD").decode().strip()
    head = commit(repository, path, "# controlled fixture\n")
    output = tmp_path / "output"
    step = workflow()["jobs"]["parity-scope"]["steps"][1]
    subprocess.run(
        ["bash", "-c", step["run"]],
        cwd=repository,
        check=True,
        env={
            **os.environ,
            "EVENT": "pull_request",
            "BASE": base,
            "HEAD": head,
            "GITHUB_OUTPUT": str(output),
        },
    )
    assert output.read_text().strip() == f"relevant={relevant}"


@pytest.mark.parametrize(
    "scope,relevant,parity,accepted",
    [
        ("success", "true", "success", True),
        ("success", "true", "failure", False),
        ("success", "true", "skipped", False),
        ("success", "false", "skipped", True),
        ("failure", "false", "skipped", False),
        ("success", "", "skipped", False),
    ],
)
def test_actual_required_parity_shell_fails_closed(scope, relevant, parity, accepted):
    step = workflow()["jobs"]["official30-parity-required"]["steps"][0]
    result = subprocess.run(
        ["bash", "-e", "-c", step["run"]],
        check=False,
        env={**os.environ, "SCOPE": scope, "RELEVANT": relevant, "PARITY": parity},
    )
    assert (result.returncode == 0) is accepted


def test_workflow_reuses_canonical_parity_and_packaged_tools():
    jobs = workflow()["jobs"]
    parity = jobs["official30-headless-parity"]
    assert parity["needs"] == "parity-scope"
    assert any(
        "test_official30_compile_execute_and_match_native_references_over_zmq"
        in step.get("run", "")
        for step in parity["steps"]
    )
    guards = yaml.load(
        (REPO / ".github/workflows/refactor-guardrails.yml").read_text(),
        Loader=yaml.BaseLoader,
    )
    assert "pull_request" in guards["on"]
    assert set(guards["jobs"]) == {"structural-ratchet", "nra-r1"}
    ratchet = guards["jobs"]["structural-ratchet"]["steps"][-1]["run"]
    assert (
        "uvx --python 3.14 --from git+https://github.com/OpenHCSDev/agent-comms@"
        in ratchet
    )
    assert "agent-comms-ratchet --root" in ratchet
