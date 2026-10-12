"""The compiled plan states each array conversion a pipeline will make.

No test here needs an accelerator: the route between two libraries and devices
is asked of ArrayBridge, which reads only declarations.
"""

from __future__ import annotations

import pytest
from arraybridge.conversion import (
    ConversionCounters,
    ConversionObserver,
    ConversionRecord,
    ConversionRoute,
)
from arraybridge.devices import HOST, AcceleratorDevice, Device
from arraybridge.types import MemoryType

from openhcs.constants.constants import Backend
from openhcs.core import memory
from openhcs.core.array_conversions import (
    PlannedConversion,
    StepConversions,
    format_planned_and_observed,
    format_planned_conversions,
    planned_conversions,
)
from openhcs.core.callable_contract import CallableContract
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.device_assignment import (
    AssignedDevice,
    DeviceAssignment,
    NoAcceleratorPresent,
    OnlyHostDevices,
    PreferredAcceleratorPresent,
)
from openhcs.core.function_patterns import (
    CompiledFunctionGroup,
    CompiledFunctionInvocation,
    CompiledFunctionPattern,
    FunctionInvocationKey,
)
from openhcs.core.runtime_array_values import ArrayPlacement
from openhcs.core.step_dependencies import PipelineStartInput, StepOutputInput

ACCELERATOR = AcceleratorDevice(0)


@memory.cupy
def normalize(image):
    return image


@memory.torch
def segment(image):
    return image


@memory.numpy
def measure(image):
    return image


@memory.jax
def smooth(image):
    return image


def _assigned(name: str, device: Device) -> AssignedDevice:
    library = MemoryType(name).library
    rule = (
        OnlyHostDevices()
        if name == "numpy"
        else PreferredAcceleratorPresent()
        if device == ACCELERATOR
        else NoAcceleratorPresent()
    )
    return AssignedDevice(ArrayPlacement(library, device), rule)


def _plans(
    *steps: tuple, devices: dict[str, Device], written: frozenset[int] = frozenset()
) -> dict[int, CompiledStepPlan]:
    """One plan per step; a step is the tuple of functions it chains."""
    plans = {}
    for index, functions in enumerate(steps):
        contracts = [CallableContract.from_callable(function) for function in functions]
        assignment = DeviceAssignment(
            tuple(
                _assigned(name, devices[name])
                for name in sorted(
                    {
                        declared.value
                        for contract in contracts
                        for declared in contract.declared_memory_types
                    }
                )
            )
        )
        invocations = tuple(
            CompiledFunctionInvocation(
                key=FunctionInvocationKey.from_contract(contract, "default", position),
                contract=contract,
            ).with_device_assignment(assignment)
            for position, contract in enumerate(contracts)
        )
        plans[index] = CompiledStepPlan(
            step_index=index,
            step_name=f"step {index}",
            axis_id="A01",
            main_input_dependency=(
                PipelineStartInput()
                if index == 0
                else StepOutputInput(index - 1, f"scope-{index - 1}")
            ),
            compiled_function_pattern=CompiledFunctionPattern(
                groups=(CompiledFunctionGroup("default", invocations),),
                is_grouped=False,
            ),
            write_backend=(
                Backend.DISK.value if index in written else Backend.MEMORY.value
            ),
            device_assignment=assignment,
        )
    return plans


def _rows(conversions: tuple[PlannedConversion, ...]) -> list[tuple[int, str, str, str]]:
    return [
        (each.step_index, each.source.describe(), each.target.describe(), each.mechanism)
        for each in conversions
    ]


GPU = {"numpy": HOST, "cupy": ACCELERATOR, "torch": ACCELERATOR}


def test_the_three_demo_boundaries_are_planned_literally() -> None:
    plans = _plans((normalize,), (segment,), (measure,), devices=GPU, written=frozenset({2}))

    assert _rows(planned_conversions(plans)) == [
        (0, "numpy on host", "cupy on accelerator:0", "host copy"),
        (1, "cupy on accelerator:0", "torch on accelerator:0", "dlpack"),
        (2, "torch on accelerator:0", "numpy on host", "host copy"),
        (2, "numpy on host", "numpy on host", "none"),
    ]


@pytest.mark.parametrize(
    "devices",
    [
        GPU,
        {"numpy": HOST, "cupy": ACCELERATOR, "torch": HOST},
        {"numpy": HOST, "torch": HOST, "jax": HOST},
        {"numpy": HOST, "torch": ACCELERATOR, "jax": ACCELERATOR},
    ],
)
def test_every_planned_mechanism_is_the_route_arraybridge_plans(devices) -> None:
    middle = normalize if "cupy" in devices else smooth
    plans = _plans(
        (middle,), (segment,), (measure,), devices=devices, written=frozenset({1, 2})
    )

    conversions = planned_conversions(plans)

    assert len(conversions) == 5
    for each in conversions:
        expected = (
            "none"
            if each.source == each.target
            else ConversionRoute.planned(
                each.source.library,
                each.source.device,
                each.target.library,
                each.target.device,
            ).mechanism
        )
        assert each.mechanism == expected


def test_a_host_torch_step_is_copied_to_numpy_on_host() -> None:
    plans = _plans(
        (segment,), (measure,), devices={"numpy": HOST, "torch": HOST}
    )

    assert _rows(planned_conversions(plans)) == [
        (0, "numpy on host", "torch on host", "host copy"),
        (1, "torch on host", "numpy on host", "host copy"),
    ]


def test_functions_chained_in_one_step_are_boundaries_too() -> None:
    plans = _plans((normalize, segment, measure), devices=GPU)

    conversions = planned_conversions(plans)

    assert [each.boundary for each in conversions] == [
        "stored planes -> normalize",
        "normalize -> segment",
        "segment -> measure",
    ]
    assert [each.mechanism for each in conversions] == ["host copy", "dlpack", "host copy"]
    assert {each.step_index for each in conversions} == {0}


def test_a_written_step_output_is_copied_to_host_for_the_file() -> None:
    plans = _plans((segment,), devices=GPU, written=frozenset({0}))

    assert _rows(planned_conversions(plans))[-1] == (
        0,
        "torch on accelerator:0",
        "numpy on host",
        "host copy",
    )
    assert planned_conversions(plans)[-1].boundary == "segment -> stored planes"


def test_the_pipeline_table_names_every_boundary() -> None:
    plans = _plans((normalize,), (segment,), (measure,), devices=GPU)

    table = format_planned_conversions(planned_conversions(plans))

    assert "cupy on accelerator:0" in table
    assert "dlpack" in table
    assert len(table.splitlines()) == 4


def _record(source: str, source_device: str, target: str, target_device: str, mechanism: str):
    return ConversionRecord(source, source_device, target, target_device, mechanism, 1_000_000, 0.5)


def test_observed_conversions_are_kept_by_step_and_merge_across_workers() -> None:
    first, second = StepConversions(), StepConversions()
    with first.during_step(1):
        ConversionObserver.current.record(
            _record("cupy", "accelerator:0", "torch", "accelerator:0", "dlpack")
        )
    second.by_step[1] = ConversionCounters()
    second.by_step[1].record(
        _record("cupy", "accelerator:0", "torch", "accelerator:0", "dlpack")
    )
    second.by_step[2] = ConversionCounters()
    second.by_step[2].record(_record("torch", "accelerator:0", "numpy", "host", "host copy"))

    merged = StepConversions().merge(first).merge(second)

    assert {
        (step, key, total.count)
        for step, counters in merged.by_step.items()
        for key, total in counters.totals.items()
    } == {
        (1, ("cupy", "accelerator:0", "torch", "accelerator:0", "dlpack"), 2),
        (2, ("torch", "accelerator:0", "numpy", "host", "host copy"), 1),
    }
    assert StepConversions.from_json(merged.to_json()).to_json() == merged.to_json()
    assert merged.total().totals[
        ("cupy", "accelerator:0", "torch", "accelerator:0", "dlpack")
    ].count == 2


def test_the_observer_is_installed_only_while_a_step_executes() -> None:
    before = ConversionObserver.current
    conversions = StepConversions()
    with conversions.during_step(0):
        assert ConversionObserver.current.wants_records
        with conversions.during_step(1):
            pass
        assert ConversionObserver.current.wants_records
    assert ConversionObserver.current is before
    assert not before.wants_records


def test_planned_and_observed_are_shown_side_by_side() -> None:
    plans = _plans((normalize,), (segment,), (measure,), devices=GPU)
    observed = StepConversions()
    observed.by_step[1] = ConversionCounters()
    observed.by_step[1].record(
        _record("cupy", "accelerator:0", "torch", "accelerator:0", "host copy")
    )

    table = format_planned_and_observed(planned_conversions(plans), observed)

    [line] = [line for line in table.splitlines() if "normalize -> segment" in line]
    assert "dlpack" in line and "host copy" in line
    assert line.rstrip().endswith("0.500")


def test_the_plan_summary_shows_each_conversion_and_one_pipeline_table() -> None:
    from openhcs.agent.dto.execution import (
        CompiledStepPlanSummary,
        PlannedConversionSummary,
    )
    from openhcs.mcp.dev_client_renderers.pipeline import PipelineArtifactPlanRenderer

    conversion = PlannedConversionSummary(
        boundary="normalize -> segment",
        source_library="cupy",
        source_device="accelerator:0",
        target_library="torch",
        target_device="accelerator:0",
        mechanism="dlpack",
    )
    steps = tuple(
        CompiledStepPlanSummary(
            step_index=1,
            step_name="segment",
            axis_id=axis_id,
            output_dir=None,
            conversions=(conversion,),
        )
        for axis_id in ("A01", "A02")
    )

    assert (
        "  conversion: normalize -> segment: cupy on accelerator:0 -> "
        "torch on accelerator:0 by dlpack"
    ) in PipelineArtifactPlanRenderer._step_lines(steps)
    assert PipelineArtifactPlanRenderer._conversion_table_lines(steps) == [
        "Conversions:",
        "  step  boundary              source                 target                  mechanism",
        "  1     normalize -> segment  cupy on accelerator:0  torch on accelerator:0  dlpack",
    ]
