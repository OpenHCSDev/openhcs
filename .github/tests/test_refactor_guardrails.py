"""Guardrail-tool tests, independent of the application test environment."""

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest
import yaml

from scripts import check_refactor_r1 as policy
from scripts.check_refactor_r1 import (
    R1EmptyReportScope,
    SourceRevision,
    StagedSourceRevision,
    compare,
    git,
    json_report_object,
    scan_counts,
)

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
        item.check
        for item in scan_counts(
            snapshot, ("openhcs",), ("openhcs/raw.py",), cache_root=tmp_path / "nra"
        )
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


@pytest.mark.parametrize("path", ["openhcs/read.py", "openhcs/[read]\t*.py"])
def test_deleted_source_scope_is_unmeasured_and_never_parsed(
    repository, tmp_path, monkeypatch, path
):
    # Invalid deleted source is no longer a report target, not a zero baseline.
    base = commit(repository, path, "def broken(:\n")
    git(repository, "rm", "--", path)
    head = commit(repository, "docs/note.md", "remove unused source")

    def unexpected_snapshot(*args, **kwargs):
        pytest.fail("Empty head report scope must not materialize/parse context")

    monkeypatch.setattr(SourceRevision, "materialize", unexpected_snapshot)
    scratch = tmp_path / "not-created"
    result = compare(repository, base, head, scratch, budget_seconds=0)
    assert isinstance(result, R1EmptyReportScope)
    assert result.changed == (path,)
    assert not result.increased
    payload = json_report_object(result)
    assert payload["reason"] == "no_surviving_changed_python"
    assert "before" not in payload and "after" not in payload
    assert not scratch.exists()

    # The real CLI must also return a scoped result without invoking the scanner.
    command = subprocess.run(
        [
            sys.executable,
            policy.__file__,
            "--base",
            base,
            "--head",
            head,
            "--scratch-root",
            str(scratch),
            "--budget-seconds",
            "0",
        ],
        cwd=repository,
        capture_output=True,
        text=True,
        check=False,
    )
    assert command.returncode == 0, command.stderr
    assert json.loads(command.stdout)["reason"] == result.reason
    assert not scratch.exists()


@pytest.mark.parametrize("destination", ["openhcs/moved.py", "openhcs/[moved]\t*.py"])
def test_moved_surviving_source_is_scanned_as_a_new_report_target(
    repository, tmp_path, destination
):
    base = commit(repository, "openhcs/original.py", RAW)
    git(repository, "rm", "openhcs/original.py")
    head = commit(repository, destination, RAW)
    result = compare(repository, base, head, tmp_path / "scratch")
    assert [(item.file, item.count) for item in result.increased] == [(destination, 1)]
    assert [(item.file, item.count) for item in result.before] == [
        ("openhcs/original.py", 1)
    ]


def test_empty_scope_rejects_an_uninitialized_repository_child(repository, tmp_path):
    base = git(repository, "rev-parse", "HEAD").decode().strip()
    child = repository / "external" / "not-initialized"
    child.mkdir(parents=True)
    with pytest.raises(RuntimeError, match="not initialized"):
        compare(child, base, base, tmp_path / "not-created")
    assert not (tmp_path / "not-created").exists()


@pytest.mark.parametrize(
    "source,increased",
    [
        ("", False),
        (RAW, True),
        (
            SCHEMA
            + "\ndef check(row: Record):\n    return isinstance(row.alpha, str)\n",
            True,
        ),
        (
            SCHEMA
            + "\ndef check(row: Record):\n    return isinstance(row.beta, int)\n",
            True,
        ),
    ],
)
def test_actual_r1_cli_json_and_exit_status(repository, tmp_path, source, increased):
    base = git(repository, "rev-parse", "HEAD").decode().strip()
    head = commit(repository, "openhcs/read.py", source)
    result = subprocess.run(
        [
            sys.executable,
            policy.__file__,
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


def test_original_nra_reuse_invalidates_changed_schema_context(
    repository, tmp_path, capsys
):
    commit(repository, "openhcs/model.py", SCHEMA)
    base = commit(repository, "openhcs/consumer.py", RAW)
    commit(repository, "openhcs/model.py", SCHEMA.replace("beta: int", "delta: int"))
    head = commit(repository, "openhcs/consumer.py", RAW + "\n")
    result = compare(repository, base, head, tmp_path / "scratch")
    assert {item.check for item in result.before} == {"mapping_read"}
    assert {item.check for item in result.after} == {"unmodeled_record_shape"}
    assert [(item.check, item.file) for item in result.increased] == [
        ("unmodeled_record_shape", "openhcs/consumer.py")
    ]
    assert "NRA cache=" in capsys.readouterr().err


def test_staging_keeps_source_identity_and_removes_deleted_members(
    repository, tmp_path
):
    commit(repository, "openhcs/model.py", SCHEMA)
    base = commit(repository, "openhcs/old.py", RAW)
    snapshot = tmp_path / "source"
    StagedSourceRevision(repository, base).materialize(snapshot, ("openhcs",))
    model = snapshot / "openhcs/model.py"
    identity = model.stat()
    git(repository, "rm", "openhcs/old.py")
    head = commit(repository, "openhcs/new.py", RAW)
    members = StagedSourceRevision(repository, head).materialize(snapshot, ("openhcs",))
    assert model.stat() == identity
    assert not (snapshot / "openhcs/old.py").exists()
    assert (snapshot / "openhcs/new.py").read_text() == RAW
    assert set(members) == set(snapshot.rglob("*.py"))


@pytest.mark.parametrize("transition", ["added", "removed", "ambiguous"])
def test_staged_schema_membership_matches_fresh_original_analysis(
    repository, tmp_path, monkeypatch, transition
):
    from nominal_refactor_advisor.semantic_descent import SemanticAuthorityKind

    if transition != "added":
        commit(repository, "openhcs/model.py", SCHEMA)
    base = commit(repository, "openhcs/consumer.py", RAW)
    if transition == "removed":
        git(repository, "rm", "openhcs/model.py")
    elif transition == "ambiguous":
        commit(repository, "openhcs/other.py", SCHEMA.replace("Record", "OtherRecord"))
    else:
        commit(repository, "openhcs/model.py", SCHEMA)
    head = commit(repository, "openhcs/consumer.py", RAW + "# changed report target\n")
    results = []
    original = policy.analyze_compact_roots_with_cache

    def observed(*args, **kwargs):
        result = original(*args, **kwargs)
        # Retain only names from the original schema inventory, not its graph.
        results.append(
            tuple(
                sorted(
                    authority.name
                    for authority in result.semantic_descent_graph.authorities
                    if authority.kind is SemanticAuthorityKind.DATACLASS_SCHEMA
                )
            )
        )
        return result

    monkeypatch.setattr(policy, "analyze_compact_roots_with_cache", observed)
    result = compare(repository, base, head, tmp_path / "scratch")
    staged_resolution = results[-1]
    snapshot = tmp_path / "fresh"
    SourceRevision(repository, head).materialize(snapshot, ("openhcs",))
    fresh = scan_counts(
        snapshot, ("openhcs",), result.changed, cache_root=tmp_path / "fresh-nra"
    )
    assert result.after == fresh
    assert staged_resolution == results[-1]
    if transition == "added":
        assert {item.check for item in result.before} == {"unmodeled_record_shape"}
        assert {item.check for item in result.after} == {"mapping_read"}
    elif transition == "removed":
        assert {item.check for item in result.before} == {"mapping_read"}
        assert {item.check for item in result.after} == {"unmodeled_record_shape"}
        assert {item.check for item in result.increased} == {"unmodeled_record_shape"}
    else:
        assert len(results[0]) == 1
        assert len(staged_resolution) == 2
        assert result.before != result.after


def test_fixed_address_reuses_original_projection_cache(
    repository, tmp_path, monkeypatch
):
    from nominal_refactor_advisor.analysis import CompactProjectionCacheSource

    commit(repository, "openhcs/model.py", SCHEMA)
    base = commit(repository, "openhcs/consumer.py", DECODE)
    head = commit(repository, "openhcs/consumer.py", DECODE + "# comment only\n")
    snapshots = []
    parsed = []
    original_scan = policy.scan_counts
    original_parse = CompactProjectionCacheSource.parsed_module

    def observed_parse(self):
        parsed.append(self.path)
        return original_parse(self)

    def observed_scan(snapshot, *args, **kwargs):
        start = len(parsed)
        result = original_scan(snapshot, *args, **kwargs)
        snapshots.append((snapshot, len(parsed) - start))
        return result

    monkeypatch.setattr(CompactProjectionCacheSource, "parsed_module", observed_parse)
    monkeypatch.setattr(policy, "scan_counts", observed_scan)
    result = compare(repository, base, head, tmp_path / "scratch")
    assert not result.increased
    assert snapshots[0][0] == snapshots[1][0]
    assert snapshots[0][1] > 0
    assert snapshots[1][1] == 0


@pytest.mark.parametrize("remove_dependency", [False, True])
def test_recursive_git_dependency_transition_invalidates_schema(
    repository, tmp_path, remove_dependency
):
    dependency = repository / "external/dep"
    nested = dependency / "external/nested"
    nested.mkdir(parents=True)
    git(dependency, "init", "-q")
    git(nested, "init", "-q")
    schema_base = commit(nested, "nested/model.py", SCHEMA)
    git(
        dependency,
        "update-index",
        "--add",
        "--cacheinfo",
        f"160000,{schema_base},external/nested",
    )
    dependency_base = commit(dependency, "dep/__init__.py", "")
    git(
        repository,
        "update-index",
        "--add",
        "--cacheinfo",
        f"160000,{dependency_base},external/dep",
    )
    base = commit(repository, "openhcs/consumer.py", RAW)
    if remove_dependency:
        git(repository, "update-index", "--force-remove", "external/dep")
    else:
        schema_head = commit(
            nested, "nested/model.py", SCHEMA.replace("beta: int", "delta: int")
        )
        git(
            dependency,
            "update-index",
            "--cacheinfo",
            f"160000,{schema_head},external/nested",
        )
        dependency_head = commit(
            dependency, "dep/__init__.py", "# dependency changed\n"
        )
        git(
            repository,
            "update-index",
            "--cacheinfo",
            f"160000,{dependency_head},external/dep",
        )
    head = commit(repository, "openhcs/consumer.py", RAW + "# changed report\n")
    result = compare(repository, base, head, tmp_path / "scratch")
    assert {item.check for item in result.before} == {"mapping_read"}
    assert {item.check for item in result.after} == {"unmodeled_record_shape"}
    assert {(item.check, item.file) for item in result.increased} == {
        ("unmodeled_record_shape", "openhcs/consumer.py")
    }
    snapshot = tmp_path / "fresh"
    SourceRevision(repository, head).materialize(snapshot, ("openhcs",))
    assert result.after == scan_counts(
        snapshot, ("openhcs",), result.changed, cache_root=tmp_path / "fresh-nra"
    )


def test_transition_releases_original_graph_before_next_analysis(
    repository, tmp_path, monkeypatch
):
    import weakref

    commit(repository, "openhcs/model.py", SCHEMA)
    base = commit(repository, "openhcs/consumer.py", RAW)
    head = commit(repository, "openhcs/consumer.py", RAW + "# changed\n")
    graphs = []
    original = policy.analyze_compact_roots_with_cache

    def observed(*args, **kwargs):
        assert all(graph() is None for graph in graphs)
        result = original(*args, **kwargs)
        graphs.append(weakref.ref(result.semantic_descent_graph))
        return result

    monkeypatch.setattr(policy, "analyze_compact_roots_with_cache", observed)
    compare(repository, base, head, tmp_path / "scratch")
    assert len(graphs) == 2
    assert all(graph() is None for graph in graphs)


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
