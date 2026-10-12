"""Compile framework-local devices from FunctionStep memory declarations."""

from __future__ import annotations

from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.device_assignment import DeviceAssignment, DevicePreference


def assign_framework_devices(
    step_plans: dict[int, CompiledStepPlan],
) -> None:
    """Assign a device to every library the pipeline declares, then to each step.

    A library has one device for the whole pipeline; a step's plan holds the
    assignments of the libraries that step declares.
    """

    pipeline_assignment = DeviceAssignment.for_libraries(
        (
            library
            for step_plan in step_plans.values()
            for library in step_plan.declared_libraries
        ),
        DevicePreference(),
    )
    for step_plan in step_plans.values():
        step_plan.device_assignment = pipeline_assignment.select(
            step_plan.declared_libraries
        )
        pattern = step_plan.compiled_function_pattern
        if pattern is not None:
            step_plan.compiled_function_pattern = pattern.with_device_assignment(
                step_plan.device_assignment
            )
