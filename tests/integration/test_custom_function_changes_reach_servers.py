"""Registering a custom function tells the running servers.

Registering is making a function usable, and usable includes acquired on every
server that will run it. One session (the driver) holds a connected client and
only calls the manager: create, edit, create a source that cannot be acquired,
delete. A real execution server with fork workers follows. Counts only.

What this cannot see: a server on another machine with its own store (the
change carries the source for that; here both share one store), spawn workers,
and the Qt dialog, which shows what ``list_custom_functions`` returns.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

REPOSITORY = Path(__file__).resolve().parents[2]
HELPERS = Path(__file__).resolve().parent / "helpers" / "prepared_resource"


@pytest.fixture(scope="module")
def events(tmp_path_factory: pytest.TempPathFactory) -> list[dict]:
    root = tmp_path_factory.mktemp("custom_function_changes")
    trace = root / "trace.jsonl"
    completed = subprocess.run(
        [sys.executable, str(HELPERS / "run_custom_function_changes.py"), str(root)],
        cwd=REPOSITORY,
        env={
            **os.environ,
            "PYTHONPATH": os.pathsep.join(
                (str(HELPERS), str(REPOSITORY), os.environ.get("PYTHONPATH", ""))
            ),
            "OPENHCS_PREPARED_RESOURCE_TRACE": str(trace),
            "NUMBA_CACHE_DIR": str(root / "numba"),
            "XDG_DATA_HOME": str(root / "data"),
            "OPENHCS_CPU_ONLY": "1",
            "QT_QPA_PLATFORM": "offscreen",
            "DISPLAY": "",
            "WAYLAND_DISPLAY": "",
        },
        capture_output=True,
        text=True,
        timeout=1800,
    )
    assert completed.returncode == 0, completed.stdout[-2000:] + completed.stderr[-4000:]
    return sorted(
        (json.loads(line) for line in trace.read_text().splitlines()),
        key=lambda event: event["time"],
    )


def _one(events: list[dict], kind: str, **facts: object) -> dict:
    [event] = _all(events, kind, **facts)
    return event


def _all(events: list[dict], kind: str, **facts: object) -> list[dict]:
    return [
        event
        for event in events
        if event["kind"] == kind
        and all(event.get(name) == value for name, value in facts.items())
    ]


def _at(events: list[dict], event: dict) -> int:
    return next(index for index, other in enumerate(events) if other is event)


def _timed(events: list[dict]) -> list[dict]:
    """Every event inside a compile or an execute window."""
    timed: list[dict] = []
    open_windows = 0
    for event in events:
        if event["kind"] in ("compile_start", "execute_start"):
            open_windows += 1
        elif event["kind"] in ("compile_end", "execute_end"):
            open_windows -= 1
        elif open_windows:
            timed.append(event)
    return timed


def test_a_function_created_while_the_server_is_ready_is_acquired_by_the_server(
    events: list[dict],
) -> None:
    create = _one(events, "create")
    acquired = _one(events, "acquire", function="followed", revision="one")
    settled = _one(events, "server_state", moment="created")
    session = create["pid"]
    workers = {event["pid"]: event["parent"] for event in _all(events, "call")}

    assert _at(events, create) < _at(events, acquired) < _at(events, settled)
    assert acquired["pid"] != session, "the session that stores a source acquires nothing"
    assert {acquired["pid"]} == set(workers.values()), (
        "the server that forks the workers is the process that acquired"
    )
    assert not settled["pending"] and not settled["failed"]
    assert [name for name, _revision in settled["loaded"]] == ["followed"]


def test_the_manager_lists_the_function_as_preparing_until_the_server_holds_it(
    events: list[dict],
) -> None:
    told = _one(events, "listed", moment="told")
    created = _one(events, "listed", moment="created")
    acquired = _one(events, "acquire", function="followed", revision="one")

    assert created["entries"] == [["followed", "Loaded"]]
    if _at(events, told) < _at(events, acquired):
        assert told["entries"] == [
            ["followed (preparing)", "Preparing on the execution server"]
        ]


def test_no_compile_or_execute_contains_an_acquisition(events: list[dict]) -> None:
    timed = _timed(events)
    calls = [event for event in timed if event["kind"] == "call"]
    assert {event["revision"] for event in calls} == {"one", "two"}, (
        "the pipelines did not call both revisions, so the count proves nothing"
    )
    late = [
        f"{event['kind']} {event['function']} pid {event['pid']}"
        for event in timed
        if event["kind"] == "acquire"
    ]
    assert late == [], "an acquisition ran inside a compile or an execute:\n" + "\n".join(late)


def test_an_edit_is_acquired_again_and_the_old_revision_is_withdrawn(
    events: list[dict],
) -> None:
    edit = _one(events, "edit")
    acquired = _one(events, "acquire", function="followed", revision="two")
    before = _one(events, "server_state", moment="created")
    after = _one(events, "server_state", moment="edited")

    assert _at(events, edit) < _at(events, acquired) < _at(events, after)
    [[name, old_content]] = before["loaded"]
    [[same_name, new_content]] = after["loaded"]
    assert name == same_name == "followed" and old_content != new_content, (
        "the server publishes the new revision only"
    )
    calls_after = [
        event
        for event in _all(events, "call", function="followed")
        if _at(events, event) > _at(events, after)
    ]
    assert calls_after and {event["revision"] for event in calls_after} == {"two"}
    assert len(_all(events, "acquire", function="followed")) == 2, (
        "one acquisition per revision, none repeated"
    )


def test_an_acquisition_that_fails_on_the_server_is_listed_as_failed_to_load(
    events: list[dict],
) -> None:
    state = _one(events, "server_state", moment="not_acquirable")
    listed = _one(events, "listed", moment="not_acquirable")
    session = _one(events, "create_not_acquirable")["pid"]

    assert [event["pid"] for event in _all(events, "acquire", function="not_acquirable")] != [
        session
    ], "the session did not run the acquisition; the server did"
    [[name, message]] = state["failed"]
    assert name == "not_acquirable" and "weights are unreachable" in message
    entries = dict(listed["entries"])
    assert "weights are unreachable" in entries["not_acquirable (failed to load)"]
    assert entries["followed"] == "Loaded", "one failed source hides no other"


def test_a_deleted_function_is_withdrawn_and_a_compile_naming_it_is_refused(
    events: list[dict],
) -> None:
    state = _one(events, "server_state", moment="deleted")
    refused = _one(events, "refused", function="followed")

    assert "followed" not in [name for name, _revision in state["loaded"]]
    assert "followed" in refused["message"]
    assert "custom function" in refused["message"].lower()


# --- A declared value that could not be acquired (function "valued") ---


def _between(events: list[dict], start: dict, end: dict) -> list[dict]:
    return events[_at(events, start) + 1 : _at(events, end)]


def test_a_function_is_published_without_the_value_that_could_not_be_acquired(
    events: list[dict],
) -> None:
    state = _one(events, "server_state", moment="valued_created")
    listed = _one(events, "listed", moment="valued_created")
    cause = "model='large' (ConnectionError: weights are unreachable)"

    assert "valued" in [name for name, _revision in state["loaded"]]
    assert "valued" not in [name for name, _message in state["failed"]]
    assert state["unacquired"] == [["valued", [cause]]]
    assert dict(listed["entries"])["valued (values not acquired)"] == (
        f"Loaded; not acquired: on the execution server: {cause}"
    )
    before_compile = events[: _at(events, _one(events, "valued_compile_start"))]
    assert [
        event["model"] for event in _all(before_compile, "acquire", function="valued")
    ] == ["small", "large"], "every declared value is tried once when the source loads"


def test_a_compile_selecting_the_unacquired_value_passes_and_acquires_nothing(
    events: list[dict],
) -> None:
    compile_window = _between(
        events, _one(events, "valued_compile_start"), _one(events, "valued_compile_end")
    )
    assert [event["kind"] for event in compile_window if event["function"] == "valued"] == []


def test_preparing_the_pipeline_fails_naming_the_value_while_it_is_unreachable(
    events: list[dict],
) -> None:
    failed = _one(events, "prepare_failed", function="valued")
    window = _between(
        events,
        _one(events, "valued_prepare_start", attempt="unreachable"),
        _one(events, "valued_prepare_end", attempt="unreachable"),
    )
    server = _one(events, "acquire", function="followed", revision="one")["pid"]

    assert "'valued' could not be acquired for model='large'" in failed["message"]
    assert "ConnectionError: weights are unreachable" in failed["message"]
    assert [
        (event["kind"], event["model"], event["pid"])
        for event in window
        if event["function"] == "valued" and event["kind"] != "prepare_failed"
    ] == [("acquire", "large", server)], "tried once, in the server; no worker loaded"


def test_once_reachable_the_next_preparation_acquires_once_and_the_execution_nothing(
    events: list[dict],
) -> None:
    prepare_window = _between(
        events,
        _one(events, "valued_prepare_start", attempt="reachable"),
        _one(events, "valued_prepare_end", attempt="reachable"),
    )
    execute_window = _between(
        events, _one(events, "valued_execute_start"), _one(events, "valued_execute_end")
    )
    server = _one(events, "acquire", function="followed", revision="one")["pid"]
    acquisitions = [event for event in prepare_window if event["kind"] == "acquire"]
    loads = [event for event in prepare_window if event["kind"] == "load"]
    calls = [event for event in execute_window if event["kind"] == "call"]

    assert [(event["model"], event["pid"]) for event in acquisitions] == [
        ("large", server)
    ], "acquired exactly once, by the server"
    assert loads and all(
        event["model"] == "large"
        and event["parent"] == server
        and _at(events, event) > _at(events, acquisitions[0])
        for event in loads
    ), "the workers load after the server acquired"
    assert calls and {event["pid"] for event in calls} <= {event["pid"] for event in loads}
    assert [
        event["kind"] for event in execute_window if event["kind"] in ("acquire", "load")
    ] == [], "the execution contains no acquisition and no load"
    assert len(_all(events, "acquire", function="valued", model="large")) == 3, (
        "source load, failed preparation, successful preparation: nothing else retried"
    )
    assert _one(events, "server_state", moment="valued_acquired")["unacquired"] == []
