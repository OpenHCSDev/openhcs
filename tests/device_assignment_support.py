"""Shared test support: plans and invocations get their devices from the real rules.

A test that builds a ``CompiledStepPlan`` or a compiled invocation by hand runs
``assign_devices`` on it, which is the compiler's own assignment step. A test
that needs a library this environment lacks (or a chosen accelerator count)
installs ``stand_in_module``: a module with only the accelerator-count entry
points the real ``arraybridge`` library class reads, so the real family code
and the real OpenHCS rules run.
"""

from __future__ import annotations

from importlib.machinery import ModuleSpec

import numpy as np
from arraybridge import MemoryType
from types import ModuleType, SimpleNamespace

from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.device_assignment import DeviceAssignment, DevicePreference
from openhcs.core.function_patterns import (
    CompiledFunctionInvocation,
    CompiledFunctionPattern,
    compile_function_pattern,
)
from openhcs.core.pipeline.framework_device_assignment import assign_framework_devices


def stand_in_module(name: str, accelerator_count) -> ModuleType:
    """A module answering only how many accelerators there are."""

    count = accelerator_count if callable(accelerator_count) else lambda: accelerator_count
    module = ModuleType(name)
    module.__spec__ = ModuleSpec(name, None)
    module.cuda = SimpleNamespace(
        is_available=lambda: count() > 0,
        device_count=count,
        runtime=SimpleNamespace(getDeviceCount=count),
    )
    return module


def assign_devices(plan: CompiledStepPlan) -> CompiledStepPlan:
    """Run the compiler's device assignment on one hand-built step plan."""

    assign_framework_devices({plan.step_index: plan})
    return plan


def devices_for(*declarations: str) -> DeviceAssignment:
    """The real assignment for the named libraries (``"numpy"``, ``"torch"`` ...)."""

    return DeviceAssignment.for_libraries(
        (MemoryType(declaration).library for declaration in declarations),
        DevicePreference(),
    )


def assign_pattern_devices(pattern: CompiledFunctionPattern) -> CompiledFunctionPattern:
    """Assign the libraries one compiled pattern declares, by the real rules."""

    return pattern.with_device_assignment(
        DeviceAssignment.for_libraries(pattern.declared_libraries, DevicePreference())
    )


def compile_assigned_pattern(*args, **kwargs) -> CompiledFunctionPattern:
    """``compile_function_pattern`` followed by the real device assignment."""

    return assign_pattern_devices(compile_function_pattern(*args, **kwargs))


def assign_invocation_devices(
    invocation: CompiledFunctionInvocation,
) -> CompiledFunctionInvocation:
    """Assign the libraries one compiled invocation declares, by the real rules."""

    return invocation.with_device_assignment(
        DeviceAssignment.for_libraries(
            (
                memory_type.library
                for memory_type in invocation.contract.declared_memory_types
            ),
            DevicePreference(),
        )
    )


def recording_cupy_module():
    """A stand-in CuPy whose arrays record their device; the real library class runs.

    Returns the module, its array class and a state dict holding the current
    device and every download from, and upload to, a device.
    """

    state = {'device': 0, 'downloads': [], 'uploads': []}

    class DeviceScope:
        def __init__(self, device_id):
            self.device_id = device_id

        def __enter__(self):
            self.previous = state['device']
            state['device'] = self.device_id

        def __exit__(self, *exc):
            state['device'] = self.previous

    class DeviceArray:
        __module__ = 'cupy'

        def __init__(self, values, device_id=1):
            self.values = np.asarray(values)
            self.device = SimpleNamespace(id=device_id)

        @property
        def shape(self):
            return self.values.shape

        @property
        def dtype(self):
            return self.values.dtype

        @property
        def ndim(self):
            return self.values.ndim

        def __array__(self, dtype=None, copy=None):
            raise TypeError('Implicit device-to-host conversion is forbidden')

        def get(self):
            state['downloads'].append(self.device.id)
            return self.values

        def __getitem__(self, key):
            return type(self)(self.values[key], self.device.id)

        def astype(self, dtype, copy=False):
            return type(self)(self.values.astype(dtype, copy=copy), self.device.id)

        def __truediv__(self, scalar):
            return type(self)(self.values / scalar, self.device.id)

        def reshape(self, shape):
            return type(self)(self.values.reshape(shape), self.device.id)

    def upload(values):
        state['uploads'].append(state['device'])
        return DeviceArray(values, state['device'])

    module = SimpleNamespace(
        cuda=SimpleNamespace(
            runtime=SimpleNamespace(getDeviceCount=lambda: 2), Device=DeviceScope,
        ),
        array=upload,
        broadcast_to=lambda value, shape: DeviceArray(
            np.broadcast_to(value.values, shape), value.device.id,
        ),
        ones=lambda shape, dtype=bool: DeviceArray(
            np.ones(shape, dtype=dtype), state['device'],
        ),
        stack=lambda values, axis=0: DeviceArray(
            np.stack([value.values for value in values], axis=axis), state['device'],
        ),
        logical_and=lambda left, right: DeviceArray(
            np.logical_and(left.values, right.values), state['device'],
        ),
    )
    return module, DeviceArray, state
