"""Every Numba kernel is compiled by catalog preparation, never after readiness.

Benchmarks time pipeline compilation and execution, so neither may contain a
one-time cost. One cold run (empty Numba cache, empty catalog cache) of two
pipelines over a real execution server is counted with Numba's own compile
event, in every process: the server, the workers it forks and the client.

What this cannot see: a kernel reached only with a signature (dtype, rank,
layout) or on a branch that neither pipeline nor any preparation exercises; the
second test narrows that to signatures, since it fails for any kernel that
preparation leaves with no compiled signature at all. GPU kernels (CuPy,
pyclesperanto program builds) are not counted: the run is CPU-only.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

REPOSITORY = Path(__file__).resolve().parents[2]
TRACER = Path(__file__).resolve().parent / "helpers" / "numba_trace"
PIPELINES = (
    "tests/integration/test_main.py",
    "tests/integration/test_cellprofiler_generated_pipeline.py"
    "::test_cppipe_import_executes_through_canonical_zmq_path",
)


@pytest.fixture(scope="module")
def cold_run_events(tmp_path_factory: pytest.TempPathFactory) -> list[dict]:
    """Run the pipelines from empty caches and return what each process recorded."""
    root = tmp_path_factory.mktemp("cold_run")
    trace = root / "trace"
    trace.mkdir()
    environment = {
        **os.environ,
        "PYTHONPATH": os.pathsep.join(
            (str(TRACER), str(REPOSITORY), os.environ.get("PYTHONPATH", ""))
        ),
        "OPENHCS_NUMBA_TRACE_DIR": str(trace),
        "NUMBA_CACHE_DIR": str(root / "numba"),
        "XDG_DATA_HOME": str(root / "data"),
        "OPENHCS_CPU_ONLY": "1",
        "QT_QPA_PLATFORM": "offscreen",
        "DISPLAY": "",
        "WAYLAND_DISPLAY": "",
    }
    completed = subprocess.run(
        [
            sys.executable, "-m", "pytest", *PIPELINES,
            "--it-backends", "disk", "--it-microscopes", "ImageXpress",
            "--it-dims", "3d", "--it-exec-mode", "multiprocessing",
            "--it-zmq-mode", "zmq", "--it-visualizers", "none",
            "-q", "--tb=short", "-p", "no:cacheprovider", "-p", "no:randomly",
            f"--basetemp={root / 'pipelines'}",
        ],
        cwd=REPOSITORY,
        env=environment,
        capture_output=True,
        text=True,
        timeout=1800,
    )
    assert completed.returncode == 0, completed.stdout[-4000:] + completed.stderr[-2000:]
    return sorted(
        (
            json.loads(line)
            for path in trace.glob("*.jsonl")
            for line in path.read_text().splitlines()
        ),
        key=lambda event: event["time"],
    )


def _readiness_by_server(events: list[dict]) -> dict[int, dict]:
    """The first readiness mark of each execution server, by its process id."""
    ready: dict[int, dict] = {}
    for event in events:
        if event["kind"] == "ready":
            ready.setdefault(event["pid"], event)
    assert ready, "no execution server reported readiness; the tracer saw no server"
    return ready


def _is_after_readiness(event: dict, ready: dict[int, dict]) -> bool:
    """A server and the children it forks are judged against its own readiness.

    Any other process is a client: it executes nothing, so it has no reason to
    compile or load a kernel at any time.
    """
    server = ready.get(event["pid"]) or ready.get(event["parent"])
    return server is None or event["time"] > server["time"]


def test_no_kernel_is_compiled_or_loaded_after_readiness(
    cold_run_events: list[dict],
) -> None:
    ready = _readiness_by_server(cold_run_events)
    numba_events = [
        event for event in cold_run_events if event["kind"] in ("compiled", "loaded")
    ]
    assert any(
        event["kind"] == "compiled" and not _is_after_readiness(event, ready)
        for event in numba_events
    ), "preparation compiled nothing, so the counter proves nothing"

    late = [
        f"{event['kind']} pid {event['pid']} {event['kernel']} {event['signature']}"
        for event in numba_events
        if _is_after_readiness(event, ready)
    ]
    assert late == [], (
        "Numba worked after the server was ready, or in a client. Extend the "
        "preparation of the kernel's owner so catalog preparation compiles it:\n"
        + "\n".join(late)
    )


def test_preparation_compiles_every_kernel(cold_run_events: list[dict]) -> None:
    """Derived from the code, not from a pipeline: every kernel has a signature."""
    unprepared = sorted(
        {
            kernel
            for event in _readiness_by_server(cold_run_events).values()
            for kernel in event["unprepared"]
        }
    )
    assert unprepared == [], (
        "No preparation reaches these kernels, so their first use would compile "
        "them. Reach each from its owner's preparation, or delete it if nothing "
        "calls it:\n" + "\n".join(unprepared)
    )


# --- A resource that is not a Numba kernel: a custom function's preparation ---

PREPARED_RESOURCE = Path(__file__).resolve().parent / "helpers" / "prepared_resource"
STORED_BEFORE_START = "resource_stored_before_start"
STORED_WHILE_READY = "resource_stored_while_ready"


@pytest.fixture(scope="module")
def custom_function_events(tmp_path_factory: pytest.TempPathFactory) -> list[dict]:
    """Two custom functions with a preparation, over one server with fork workers."""
    root = tmp_path_factory.mktemp("prepared_resource")
    trace = root / "trace.jsonl"
    completed = subprocess.run(
        [sys.executable, str(PREPARED_RESOURCE / "run_custom_function_pipelines.py"), str(root)],
        cwd=REPOSITORY,
        env={
            **os.environ,
            "PYTHONPATH": os.pathsep.join(
                (str(PREPARED_RESOURCE), str(REPOSITORY), os.environ.get("PYTHONPATH", ""))
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


def _kinds(events: list[dict], kind: str, function: str | None = None) -> list[dict]:
    return [
        event
        for event in events
        if event["kind"] == kind and function in (None, event["function"])
    ]


def _position(events: list[dict], event: dict) -> int:
    return next(index for index, other in enumerate(events) if other is event)


def test_custom_functions_are_prepared_before_the_server_reports_them_usable(
    custom_function_events: list[dict],
) -> None:
    """Each function is prepared once, by the server, before its readiness report."""
    events = custom_function_events
    first_ready, ready_again = _kinds(events, "ready")
    [stored_while_ready] = _kinds(events, "stored_while_ready")
    [before_start] = _kinds(events, "prepare", STORED_BEFORE_START)
    [while_ready] = _kinds(events, "prepare", STORED_WHILE_READY)

    assert _position(events, before_start) < _position(events, first_ready)
    assert (
        _position(events, stored_while_ready)
        < _position(events, while_ready)
        < _position(events, ready_again)
    ), "a function stored while the server is ready is prepared when the server learns of it"
    workers = {event["pid"]: event["parent"] for event in _kinds(events, "call")}
    assert {before_start["pid"], while_ready["pid"]} == set(workers.values()), (
        "the server that forks the workers is the process that prepares"
    )


def test_nothing_is_prepared_or_loaded_during_compile_or_execute(
    custom_function_events: list[dict],
) -> None:
    """Counts only: timed windows hold calls, never a preparation or a load."""
    events = custom_function_events
    timed: list[dict] = []
    open_windows = 0
    for event in events:
        if event["kind"] in ("compile_start", "execute_start"):
            open_windows += 1
        elif event["kind"] in ("compile_end", "execute_end"):
            open_windows -= 1
        elif open_windows:
            timed.append(event)
    calls = [event for event in timed if event["kind"] == "call"]
    assert {event["function"] for event in calls} == {
        STORED_BEFORE_START, STORED_WHILE_READY,
    }, "the pipelines did not call both functions, so the counter proves nothing"
    assert len({event["pid"] for event in calls}) >= 2, "expected several worker processes"

    late = [
        f"{event['kind']} {event['function']} pid {event['pid']}"
        for event in timed
        if event["kind"] in ("prepare", "load")
    ]
    assert late == [], (
        "A custom function was prepared or loaded its resource during a timed "
        "compile or execute:\n" + "\n".join(late)
    )


def test_each_process_holds_exactly_one_load_of_each_resource(
    custom_function_events: list[dict],
) -> None:
    """The server loads once; every worker inherits that one load and adds none."""
    events = custom_function_events
    for function in (STORED_BEFORE_START, STORED_WHILE_READY):
        [prepared] = _kinds(events, "prepare", function)
        assert [event["pid"] for event in _kinds(events, "load", function)] == [
            prepared["pid"]
        ]
        calls = _kinds(events, "call", function)
        assert calls and {event["loads"] for event in calls} == {1}
