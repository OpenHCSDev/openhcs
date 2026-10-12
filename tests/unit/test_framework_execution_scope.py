"""An invocation runs inside the device scope of the library it executes in."""

from contextlib import contextmanager
from types import SimpleNamespace

import numpy as np
import pytest
from arraybridge.devices import HOST, AcceleratorDevice

from openhcs.core.function_patterns import compile_function_pattern
from openhcs.core.runtime_plane_projection import RuntimePlaneProjection
from openhcs.core.steps.function_runtime import (
    FunctionCoreExecutor,
)
from openhcs.utils.environment import OpenHCSProcessEnvironment
from tests.artifact_graphs import admitted_graph
from tests.device_assignment_support import assign_invocation_devices


@pytest.mark.parametrize(
    ("execution_library", "accelerators", "excluded", "device"),
    [
        ("torch", 5, False, AcceleratorDevice(0)),
        ("torch", 0, False, HOST),
        ("torch", 5, True, HOST),
        ("cupy", 2, False, AcceleratorDevice(0)),
        ("numpy", None, False, HOST),
    ],
)
def test_an_invocation_runs_inside_the_scope_of_its_assigned_execution_device(
    stand_in_library, monkeypatch, execution_library, accelerators, excluded, device
) -> None:
    events = []

    def process(image):
        events.append(("call", id(image)))
        return image

    process.input_memory_type = "numpy"
    process.output_memory_type = "numpy"
    process.execution_memory_type = execution_library
    if accelerators is not None:
        stand_in_library(execution_library, accelerators)
    monkeypatch.setenv(OpenHCSProcessEnvironment.cpu_only_key, "1" if excluded else "0")
    invocation = assign_invocation_devices(
        next(compile_function_pattern(admitted_graph(process), {}, {}).iter_invocations())
    )
    library = invocation.execution_placement.library

    @contextmanager
    def recorded_scope(entered_library, entered_device):
        events.append(("enter", str(entered_library.name), entered_device))
        yield
        events.append(("exit", str(entered_library.name), entered_device))

    monkeypatch.setattr(type(library), "device_scope", recorded_scope)

    executor = FunctionCoreExecutor(
        group_data=SimpleNamespace(),
        invocation=invocation,
        artifact_inputs={},
        artifact_outputs={},
        group_key=None,
        plane_projection=RuntimePlaneProjection.stack(),
        main_data_arg=np.zeros((1, 2, 2)),
    )

    result = executor.invoke(
        executor.main_data_arg,
        {},
        loaded_artifact_payloads={},
        debug_sink=None,
    )

    assert result is executor.main_data_arg
    assert events == [
        ("enter", execution_library, device),
        ("call", id(executor.main_data_arg)),
        ("exit", execution_library, device),
    ]
