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

The last three tests count a resource that is not a Numba kernel: two custom
functions whose declared preparation loads something into memory, one stored
before the server starts and one stored while it is ready. They run with fork
workers only; with spawn workers every execution still starts new processes.
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
PROBE = "probe"


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
        STORED_BEFORE_START, STORED_WHILE_READY, PROBE,
    }, "the pipelines did not call every function, so the counter proves nothing"
    assert len({event["pid"] for event in calls}) >= 2, "expected several worker processes"

    late = [
        f"{event['kind']} {event['function']} pid {event['pid']}"
        for event in timed
        if event["kind"] in ("prepare", "acquire", "load")
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


# --- The two parts of a preparation: acquired per machine, loaded per pipeline ---


def test_every_declared_value_is_acquired_before_readiness_by_the_server(
    custom_function_events: list[dict],
) -> None:
    events = custom_function_events
    first_ready = _kinds(events, "ready")[0]
    acquired = _kinds(events, "acquire", PROBE)
    assert sorted(event["model"] for event in acquired) == ["large", "small"], (
        "one acquisition per value the acquire hook declares, and no other"
    )
    workers = {event["pid"]: event["parent"] for event in _kinds(events, "call", PROBE)}
    for event in acquired:
        assert _position(events, event) < _position(events, first_ready)
        assert {event["pid"]} == set(workers.values())


def test_a_pipeline_is_loaded_once_in_each_of_its_workers_when_it_is_prepared(
    custom_function_events: list[dict],
) -> None:
    """Two prepared runs with two workers: two loads, both in the first "prepare"."""
    events = custom_function_events
    loads = _kinds(events, "load", PROBE)
    calls = _kinds(events, "call", PROBE)
    assert [event["model"] for event in loads] == ["large", "large"], (
        "only the value the pipeline selects is loaded"
    )
    assert len({event["pid"] for event in loads}) == 2, "one load per worker"
    assert {event["pid"] for event in calls} == {event["pid"] for event in loads}, (
        "the workers that were prepared are the workers that execute, in both runs"
    )
    first_start, second_start = _kinds(events, "pipeline_preparation_start")
    first_end, second_end = _kinds(events, "pipeline_preparation_end")
    for event in loads:
        assert (
            _position(events, first_start)
            < _position(events, event)
            < _position(events, first_end)
        ), "a load happens inside the pipeline's own preparation, before execution"
    assert _position(events, second_start) < _position(events, second_end)


def test_a_value_that_was_not_acquired_is_refused_at_compile(
    custom_function_events: list[dict],
) -> None:
    [refused] = _kinds(custom_function_events, "refused", PROBE)
    assert "undeclared" in refused["message"]
    assert "model='large'" in refused["message"] and "model='small'" in refused["message"]
    assert not [
        event
        for event in custom_function_events
        if event["kind"] in ("acquire", "load") and event.get("model") == "undeclared"
    ]


# --- Timing is honest: a record reports its load phase apart from its duration ---

UNPREPARED_PROBE = "probe_unprepared"


def _run_times(events: list[dict], function: str) -> tuple[dict, dict]:
    first, second = _kinds(events, "run_times", function)
    return first, second


def _inside(events: list[dict], windows: list[tuple[float, float]], *kinds: str) -> list[dict]:
    return [
        event
        for event in events
        if event["kind"] in kinds
        and any(start <= event["time"] <= end for start, end in windows)
    ]


def _without(window: tuple[float, float], *holes: tuple[float, float]) -> list[tuple[float, float]]:
    """The window minus the intervals inside it, each strictly excluded."""
    parts = [window]
    for hole_start, hole_end in holes:
        parts = [
            part
            for start, end in parts
            for part in (
                [(start, end)]
                if hole_end < start or end < hole_start
                else [(start, hole_start - 1e-9), (hole_end + 1e-9, end)]
            )
        ]
    return [(start, end) for start, end in parts if start <= end]


def _timed_windows(run: dict) -> dict[str, list[tuple[float, float]]]:
    """Compile, execute and total of one run as its records report them."""
    load_phase = (run["load_started_at"], run["load_ended_at"])
    return {
        "compile": [(run["compile_started_at"], run["compile_ended_at"])],
        "execute": _without(
            (run["execution_started_at"], run["execution_ended_at"]), load_phase
        ),
        "total": _without(
            (run["client_started_at"], run["client_ended_at"]),
            load_phase,
            *(tuple(interval) for interval in run["outside_total"]),
        ),
    }


@pytest.mark.parametrize("function", [PROBE, UNPREPARED_PROBE])
def test_load_phase_is_outside_what_a_record_reports_as_compile_execute_and_total(
    custom_function_events: list[dict], function: str
) -> None:
    """Prepared or not, first run or second: the reported windows hold no load."""
    events = custom_function_events
    for run in _run_times(events, function):
        assert (
            run["execution_started_at"]
            <= run["load_started_at"]
            <= run["load_ended_at"]
            <= run["execution_ended_at"]
        ), "the load phase is a part of the execution's time bounds"
        assert run["execution_seconds"] == pytest.approx(
            (run["execution_ended_at"] - run["execution_started_at"])
            - (run["load_ended_at"] - run["load_started_at"])
        ), "an execution's duration is its time bounds without its load phase"
        windows = _timed_windows(run)
        assert _inside(events, windows["execute"], "call"), (
            "the execute window holds no call, so the counter proves nothing"
        )
        for name, window in windows.items():
            late = [
                f"{event['kind']} {event['function']} pid {event['pid']}"
                for event in _inside(events, window, "prepare", "acquire", "load")
            ]
            assert late == [], f"inside the reported {name} window:\n" + "\n".join(late)


def test_load_phase_of_an_unprepared_pipeline_is_reported_by_its_first_execution_only(
    custom_function_events: list[dict],
) -> None:
    """Two workers load in the first execution's load phase; the second has none."""
    events = custom_function_events
    first, second = _run_times(events, UNPREPARED_PROBE)
    loads = _kinds(events, "load", UNPREPARED_PROBE)
    calls = _kinds(events, "call", UNPREPARED_PROBE)

    assert first["loads"] == 2 and first["load_ended_at"] > first["load_started_at"]
    assert loads == _inside(
        loads, [(first["load_started_at"], first["load_ended_at"])], "load"
    ), "every load of the pipeline is inside the load phase its first execution reports"
    assert len(loads) == first["loads"] and len({event["pid"] for event in loads}) == 2
    assert {event["pid"] for event in calls} == {event["pid"] for event in loads}, (
        "the workers that loaded are the workers that execute, in both runs"
    )
    assert first["execution_seconds"] < first["job_seconds"]

    assert second["loads"] == 0, "the second execution finds the loads held"
    assert not _inside(
        events,
        [(second["load_started_at"], second["load_ended_at"])],
        "prepare", "acquire", "load",
    )


def test_load_phase_of_a_prepared_pipeline_is_empty_in_both_executions(
    custom_function_events: list[dict],
) -> None:
    """The loads ran in "prepare this pipeline", so no execution reports one."""
    for run in _run_times(custom_function_events, PROBE):
        assert run["prepared"] and run["loads"] == 0


# Spawn workers: a worker inherits nothing, prepares itself when it starts and
# is kept by the server from "prepare this pipeline" through every execution
# of the pipeline.
SPAWN_STAGES = (
    "prepared 1", "prepared 2", "unprepared 1", "unprepared 2",
    "other worker count", "kernel 1", "kernel 2",
)


@pytest.fixture(scope="module")
def spawn_worker_run(tmp_path_factory: pytest.TempPathFactory) -> dict[str, list[dict]]:
    """The probe pipelines over one server with spawn workers, Numba counted too."""
    root = tmp_path_factory.mktemp("spawned_workers")
    trace = root / "trace.jsonl"
    numba_trace = root / "numba_trace"
    numba_trace.mkdir()
    completed = subprocess.run(
        [sys.executable, str(PREPARED_RESOURCE / "run_spawned_worker_pipelines.py"), str(root)],
        cwd=REPOSITORY,
        env={
            **os.environ,
            "PYTHONPATH": os.pathsep.join(
                (
                    str(PREPARED_RESOURCE), str(TRACER), str(REPOSITORY),
                    os.environ.get("PYTHONPATH", ""),
                )
            ),
            "OPENHCS_PREPARED_RESOURCE_TRACE": str(trace),
            "OPENHCS_NUMBA_TRACE_DIR": str(numba_trace),
            "NUMBA_CACHE_DIR": str(root / "numba"),
            "XDG_DATA_HOME": str(root / "data"),
            "OPENHCS_CPU_ONLY": "1",
            "QT_QPA_PLATFORM": "offscreen",
            "DISPLAY": "",
            "WAYLAND_DISPLAY": "",
        },
        capture_output=True,
        text=True,
        timeout=3600,
    )
    assert completed.returncode == 0, completed.stdout[-2000:] + completed.stderr[-4000:]

    def by_time(lines) -> list[dict]:
        return sorted(map(json.loads, lines), key=lambda event: event["time"])

    return {
        "events": by_time(trace.read_text().splitlines()),
        "numba": by_time(
            line
            for path in numba_trace.glob("*.jsonl")
            for line in path.read_text().splitlines()
        ),
    }


@pytest.fixture(scope="module")
def spawn_worker_events(spawn_worker_run: dict[str, list[dict]]) -> list[dict]:
    return spawn_worker_run["events"]


def _stage(events: list[dict], name: str) -> list[dict]:
    """The events from this stage's marker to the next stage's."""
    markers = _kinds(events, "stage")
    [start] = [marker for marker in markers if marker["function"] == name]
    later = [marker["time"] for marker in markers if marker["time"] > start["time"]]
    end = min(later, default=float("inf"))
    return [event for event in events if start["time"] <= event["time"] < end]


def _pids(events: list[dict], kind: str) -> set[int]:
    return {event["pid"] for event in _kinds(events, kind)}


def test_spawn_workers_of_a_prepared_pipeline_load_once_and_execute_both_runs(
    spawn_worker_events: list[dict],
) -> None:
    first, second = (_stage(spawn_worker_events, f"prepared {run}") for run in (1, 2))
    loads = _kinds(first, "load", PROBE)
    assert [event["model"] for event in loads] == ["large", "large"]
    assert len(_pids(loads, "load")) == 2, "one load per worker"
    [start] = _kinds(first, "pipeline_preparation_start")
    [end] = _kinds(first, "pipeline_preparation_end")
    assert all(start["time"] < event["time"] < end["time"] for event in loads), (
        "the loads happen inside the pipeline's own preparation"
    )
    assert _kinds(second, "load") == [], "the second run loads nothing"
    assert _pids(first, "call") == _pids(second, "call") == _pids(loads, "load"), (
        "the workers that were prepared are the workers that execute, in both runs"
    )
    assert all(
        run["loads"] == 0 for run in _kinds(first + second, "run_times")
    ), "no execution of a prepared pipeline reports a load"


def test_spawn_workers_of_an_unprepared_pipeline_load_once_in_the_first_load_phase(
    spawn_worker_events: list[dict],
) -> None:
    first, second = (_stage(spawn_worker_events, f"unprepared {run}") for run in (1, 2))
    [first_run] = _kinds(first, "run_times")
    [second_run] = _kinds(second, "run_times")
    loads = _kinds(first, "load", UNPREPARED_PROBE)
    assert len(loads) == first_run["loads"] == 2 and len(_pids(loads, "load")) == 2
    assert loads == _inside(
        loads, [(first_run["load_started_at"], first_run["load_ended_at"])], "load"
    ), "every load is inside the load phase the first execution reports"
    assert _kinds(second, "load") == [] and second_run["loads"] == 0
    assert _pids(first, "call") == _pids(second, "call") == _pids(loads, "load"), (
        "the workers that loaded are the workers that execute, in both runs"
    )


def test_spawn_reported_windows_hold_no_load_and_no_acquisition(
    spawn_worker_events: list[dict],
) -> None:
    events = spawn_worker_events
    runs = _kinds(events, "run_times")
    assert [run["stage"] for run in runs] == list(SPAWN_STAGES)
    for run in runs:
        windows = _timed_windows(run)
        assert _inside(events, windows["execute"], "call"), (
            "the execute window holds no call, so the counter proves nothing"
        )
        for name, window in windows.items():
            late = [
                f"{event['kind']} {event['function']} pid {event['pid']}"
                for event in _inside(events, window, "prepare", "acquire", "load")
            ]
            assert late == [], (
                f"inside the reported {name} window of {run['stage']}:\n" + "\n".join(late)
            )
    [ready] = _kinds(events, "ready")
    acquisitions = _kinds(events, "acquire")
    assert acquisitions and all(
        event["time"] < ready["time"] for event in acquisitions
    ), "every acquisition is before readiness"
    assert len(_pids(acquisitions, "acquire")) == 1, "only the server acquires"
    assert not _pids(acquisitions, "acquire") & _pids(events, "call"), (
        "a spawned worker loads the sources without acquiring"
    )


def test_spawn_workers_are_replaced_when_the_worker_count_changes(
    spawn_worker_events: list[dict],
) -> None:
    events = spawn_worker_events
    before = _pids(_stage(events, "unprepared 2"), "call")
    stage = _stage(events, "other worker count")
    workers = _pids(stage, "call")
    assert len(workers) == 4 and not workers & before, "four new worker processes"
    loads = _kinds(stage, "load", UNPREPARED_PROBE)
    assert sorted(event["pid"] for event in loads) == sorted(workers), (
        "each new worker loads exactly once"
    )
    [census] = _kinds(stage, "worker_census")
    assert set(map(int, census["alive"])) == workers, (
        "the workers kept for the old worker count are gone"
    )
    [earlier] = _kinds(_stage(events, "unprepared 2"), "worker_census")
    assert set(map(int, earlier["alive"])) == before, (
        "a pipeline that selects other loads ended the workers that held them"
    )
