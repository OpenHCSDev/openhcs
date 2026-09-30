"""Worker profiling reports the owning thread and releases its event lease."""

import json
import os
import pstats
import subprocess
import sys
import threading
import time
from pathlib import Path

import pytest

from openhcs.core.orchestrator.worker_profiling import (
    CProfileWorkerProfilingPolicy,
    DisabledWorkerProfilingPolicy,
)
from openhcs.utils.environment import OpenHCSProcessEnvironment


def profile_arguments():
    return {
        "execution_id": "execution",
        "plate_id": "plate",
        "worker_slot": "worker_0",
        "owned_wells": ["W001"],
    }


def test_disabled_profiling_does_not_claim_an_event_lease(monkeypatch):
    monkeypatch.delenv(
        OpenHCSProcessEnvironment.worker_profile_directory_key, raising=False
    )
    assert isinstance(
        CProfileWorkerProfilingPolicy.from_environment(), DisabledWorkerProfilingPolicy
    )


@pytest.mark.parametrize("raises", (False, True))
def test_profile_excludes_concurrent_polling_and_cleans_up(
    monkeypatch, tmp_path, raises
):
    monkeypatch.setenv(
        OpenHCSProcessEnvironment.worker_profile_directory_key, str(tmp_path)
    )
    policy = CProfileWorkerProfilingPolicy.from_environment()
    active = threading.Event()
    stop = threading.Event()
    observed = threading.Event()

    def foreign_polling_thread():
        active.wait()
        while not stop.is_set():
            time.sleep(0.001)
            observed.set()

    def owning_thread_operation():
        sum(range(100))
        time.sleep(0.02)

    thread = threading.Thread(target=foreign_polling_thread)
    thread.start()
    try:
        if raises:
            with (
                pytest.raises(ValueError, match="execution failed"),
                policy.profile(**profile_arguments()),
            ):
                active.set()
                owning_thread_operation()
                assert observed.wait(1)
                raise ValueError("execution failed")
        else:
            with policy.profile(**profile_arguments()):
                active.set()
                owning_thread_operation()
                assert observed.wait(1)
    finally:
        stop.set()
        active.set()
        thread.join(2)
    assert not thread.is_alive()
    stats = pstats.Stats(str(next(tmp_path.glob("*.prof"))))
    assert not any(key[2] == "foreign_polling_thread" for key in stats.stats)
    (operation,) = (
        value
        for key, value in stats.stats.items()
        if key[2] == "owning_thread_operation"
    )
    assert operation[1] == 1
    (sleeps,) = (value for key, value in stats.stats.items() if "time.sleep" in key[2])
    assert sleeps[1] == 1
    if hasattr(sys, "monitoring"):
        assert sys.monitoring.get_tool(sys.monitoring.PROFILER_ID) is None
        for event in vars(sys.monitoring.events).values():
            if isinstance(event, int) and event > 0 and event & (event - 1) == 0:
                assert (
                    sys.monitoring.register_callback(
                        sys.monitoring.PROFILER_ID, event, None
                    )
                    is None
                )
    # A subsequent profile must acquire a fresh clean lease.
    with policy.profile(**profile_arguments()):
        owning_thread_operation()


def test_profile_event_setup_failure_releases_lease(monkeypatch, tmp_path):
    monkeypatch.setenv(
        OpenHCSProcessEnvironment.worker_profile_directory_key, str(tmp_path)
    )
    policy = CProfileWorkerProfilingPolicy.from_environment()

    def fail_setup(self):
        raise RuntimeError("cannot bind events")

    monkeypatch.setattr(type(policy), "configure_profile_event_scope", fail_setup)
    with (
        pytest.raises(RuntimeError, match="cannot bind events"),
        policy.profile(**profile_arguments()),
    ):
        raise AssertionError("profile body must not run")
    assert next(tmp_path.glob("*.prof")).is_file()
    if hasattr(sys, "monitoring"):
        assert sys.monitoring.get_tool(sys.monitoring.PROFILER_ID) is None


def test_process_bootstrap_profiles_numba_kernel_without_polling_events(tmp_path):
    program = """
import json,pstats,threading,time
import openhcs
from numba import njit
from openhcs.core.orchestrator.worker_profiling import CProfileWorkerProfilingPolicy
@njit(nogil=True)
def profiled_kernel(n):
    value=0.
    for i in range(n):value=value*1.00000001+i*0.000001
    return value
profiled_kernel(1)
stop=threading.Event()
def foreign_polling_thread():
    while not stop.is_set():time.sleep(.001)
thread=threading.Thread(target=foreign_polling_thread);thread.start()
policy=CProfileWorkerProfilingPolicy.from_environment()
try:
    with policy.profile(execution_id='kernel',plate_id='plate',worker_slot='worker_0',owned_wells=['W001']):
        for _ in range(10):profiled_kernel(1_000_000)
finally:
    stop.set();thread.join()
s=pstats.Stats(str(next(policy.output_dir.glob('*.prof'))))
kernels=[v for k,v in s.stats.items() if k[2]=='profiled_kernel']
assert len(kernels)==1 and kernels[0][1]==10,kernels
assert kernels[0][3]>0,kernels
assert not any('sleep' in k[2] or k[2]=='foreign_polling_thread' for k in s.stats),s.stats
print(json.dumps({'kernel_calls':kernels[0][1],'kernel_seconds':kernels[0][3],'foreign_polling_events':0}))
"""
    environment = os.environ.copy()
    environment[OpenHCSProcessEnvironment.worker_profile_directory_key] = str(tmp_path)
    environment[OpenHCSProcessEnvironment.numba_sys_monitoring_key] = "0"
    result = subprocess.run(
        [sys.executable, "-c", program],
        cwd=Path(__file__).resolve().parents[2],
        env=environment,
        capture_output=True,
        text=True,
        timeout=30,
        check=True,
    )
    assert json.loads(result.stdout)["kernel_calls"] == 10


@pytest.mark.parametrize("directory", (None, "", "profiles"))
def test_worker_profile_import_policy_is_derived_from_activation(directory):
    environment = {}
    if directory is not None:
        environment[OpenHCSProcessEnvironment.worker_profile_directory_key] = directory
    OpenHCSProcessEnvironment.project_numba_worker_profiling_policy(environment)
    assert environment.get(OpenHCSProcessEnvironment.numba_sys_monitoring_key) == (
        "1" if directory else None
    )
