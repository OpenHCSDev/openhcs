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
        event for event in _all(events, "call") if _at(events, event) > _at(events, after)
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
