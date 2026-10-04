from contextlib import contextmanager
from types import SimpleNamespace

import numpy as np

from arraybridge import MemoryType
from openhcs.core.compiled_step_plan import FrameworkDeviceAssignment
from openhcs.core.function_patterns import compile_function_pattern
from openhcs.core.runtime_plane_projection import RuntimePlaneProjection
from openhcs.core.steps.function_runtime import (
    ComponentArtifactPlans,
    FunctionCoreExecutor,
)


def test_function_invocation_enters_declared_execution_memory_scope(
    monkeypatch,
) -> None:
    events = []

    def process(image):
        events.append(("call", id(image)))
        return image

    process.input_memory_type = "numpy"
    process.output_memory_type = "numpy"
    process.execution_memory_type = "torch"
    invocation = next(
        compile_function_pattern(process, {}, {}).iter_invocations()
    ).with_device_assignment(
        FrameworkDeviceAssignment.from_mapping({MemoryType.TORCH: 4})
    )

    @contextmanager
    def memory_device_scope(memory_type, device_id):
        assert device_id == 4
        events.append(("enter", memory_type.value))
        yield
        events.append(("exit", memory_type.value))

    monkeypatch.setattr(MemoryType, "device_scope", memory_device_scope)

    executor = FunctionCoreExecutor(
        group_data=SimpleNamespace(),
        invocation=invocation,
        artifacts=ComponentArtifactPlans(inputs={}, outputs={}),
        group_key=None,
        plane_projection=RuntimePlaneProjection.stack(),
        main_data_arg=np.zeros((1, 2, 2)),
        source_memory_type="numpy",
    )

    result = executor.invoke(
        executor.main_data_arg,
        {},
        loaded_artifact_payloads={},
        debug_sink=None,
    )

    assert result is executor.main_data_arg
    assert events == [
        ("enter", "torch"),
        ("call", id(executor.main_data_arg)),
        ("exit", "torch"),
    ]
