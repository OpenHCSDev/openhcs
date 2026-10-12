from __future__ import annotations

import pytest

from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.config import MultiprocessingStartMethod
from openhcs.core.pipeline.framework_device_assignment import assign_framework_devices
from openhcs.utils.environment import OpenHCSProcessEnvironment
from openhcs.core.worker_start_policy import (
    WorkerStartPlatform,
    WorkerStartExecutionFacts,
    resolve_worker_start_context,
)
from tests.context_support import (
    executing_context,
)


def test_linux_cpu_server_honors_configured_fork() -> None:
    decision = resolve_worker_start_context(
        MultiprocessingStartMethod.FORK,
        server_mode=True,
        gpu_enabled=False,
        platform=WorkerStartPlatform("linux"),
    )

    assert decision.resolved is MultiprocessingStartMethod.FORK
    assert decision.context.get_start_method() == "fork"


def test_linux_gpu_execution_downgrades_fork_to_spawn() -> None:
    decision = resolve_worker_start_context(
        MultiprocessingStartMethod.FORK,
        server_mode=True,
        gpu_enabled=True,
        platform=WorkerStartPlatform("linux"),
    )

    assert decision.requested is MultiprocessingStartMethod.FORK
    assert decision.resolved is MultiprocessingStartMethod.SPAWN
    assert decision.changed
    assert decision.context.get_start_method() == "spawn"


def test_windows_rejects_fork_request() -> None:
    with pytest.raises(ValueError, match="Windows only supports"):
        resolve_worker_start_context(
            MultiprocessingStartMethod.FORK,
            server_mode=True,
            gpu_enabled=False,
            platform=WorkerStartPlatform("win32"),
        )


def test_macos_downgrades_fork_without_unsafe_override() -> None:
    decision = resolve_worker_start_context(
        MultiprocessingStartMethod.FORK,
        server_mode=True,
        gpu_enabled=False,
        platform=WorkerStartPlatform("darwin"),
    )

    assert decision.resolved is MultiprocessingStartMethod.SPAWN
    assert "macOS" in decision.reason


@pytest.mark.parametrize(
    ("declared", "accelerators", "uses_accelerator"),
    [
        ("cupy", 1, True),
        ("torch", 1, True),
        # torch is declared but assigned its host device: nothing uses a GPU.
        ("torch", 0, False),
        ("numpy", None, False),
    ],
)
def test_execution_facts_follow_the_assigned_devices(
    stand_in_library, monkeypatch, declared, accelerators, uses_accelerator
) -> None:
    if accelerators is not None:
        stand_in_library(declared, accelerators)
    monkeypatch.delenv(OpenHCSProcessEnvironment.cpu_only_key, raising=False)
    step_plans = {
        0: CompiledStepPlan(
            step_index=0,
            step_name="first",
            axis_id="A01",
            input_memory_type="numpy",
            output_memory_type="numpy",
        ),
        1: CompiledStepPlan(
            step_index=1,
            step_name="second",
            axis_id="A01",
            output_memory_type=declared,
        ),
    }
    assign_framework_devices(step_plans)
    compiled_contexts = {"A01": executing_context(step_plans=step_plans)}

    assert (
        WorkerStartExecutionFacts.from_compiled_contexts(compiled_contexts).gpu_enabled
        is uses_accelerator
    )
