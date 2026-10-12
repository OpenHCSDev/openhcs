"""The compiled plan states each array conversion a pipeline will make.

No test here needs an accelerator: the route between two libraries and devices
is asked of ArrayBridge, which reads only declarations.
"""

from __future__ import annotations

import contextvars
import json
import threading
from importlib.util import find_spec

import numpy as np
import pytest
from arraybridge.conversion import (
    ConversionObserver,
    ConversionRecord,
    ConversionRoute,
)
from arraybridge.devices import HOST, AcceleratorDevice, Device
from arraybridge.libraries import ArrayLibrary
from arraybridge.types import MemoryType

from openhcs.constants.constants import Backend
from openhcs.core import memory
from openhcs.core.array_conversions import (
    ComparedConversions,
    PlannedConversion,
    StepConversions,
    compare_with_plan,
    format_compared_conversions,
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
        (2, "numpy on host", "numpy on host", "stays in place"),
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
        assert each.mechanism == ConversionRoute.planned(
            each.source.library,
            each.source.device,
            each.target.library,
            each.target.device,
        ).mechanism


def test_a_host_torch_step_shares_its_buffer_with_numpy_on_host() -> None:
    plans = _plans(
        (segment,), (measure,), devices={"numpy": HOST, "torch": HOST}
    )

    assert _rows(planned_conversions(plans)) == [
        (0, "numpy on host", "torch on host", "shared host buffer"),
        (1, "torch on host", "numpy on host", "shared host buffer"),
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


def _record(
    source: str,
    source_device: str,
    target: str,
    target_device: str,
    mechanism: str,
    declined: tuple[str, ...] = (),
):
    return ConversionRecord(
        source, source_device, target, target_device, mechanism, 1_000_000, 0.5, declined
    )


def _seen(step_index: int, *records: ConversionRecord) -> StepConversions:
    conversions = StepConversions()
    with conversions.during_step(step_index):
        for record in records:
            ConversionObserver.current.record(record)
    return conversions


def _counts(conversions: StepConversions) -> set[tuple]:
    return {
        (seen.step_index, *seen.placements, seen.mechanism, seen.declined_mechanisms, seen.count)
        for seen in conversions.observed()
    }


DLPACK = ("cupy", "accelerator:0", "torch", "accelerator:0", "dlpack")
DOWNLOAD = ("torch", "accelerator:0", "numpy", "host", "host copy")


def test_observed_conversions_are_kept_by_step_and_merge_across_workers() -> None:
    first = _seen(1, _record(*DLPACK))
    second = _seen(1, _record(*DLPACK)).merge(_seen(2, _record(*DOWNLOAD)))

    merged = StepConversions().merge(first).merge(second)

    assert _counts(merged) == {(1, *DLPACK, (), 2), (2, *DOWNLOAD, (), 1)}


def test_the_routes_a_record_lists_as_declined_survive_counting_and_merging() -> None:
    copied = _record("numpy", "host", "jax", "host", "host copy", ("shared host buffer",))
    plain = _record("numpy", "host", "jax", "host", "host copy")

    merged = _seen(0, copied, plain).merge(_seen(0, copied))

    assert _counts(merged) == {
        (0, "numpy", "host", "jax", "host", "host copy", ("shared host buffer",), 2),
        (0, "numpy", "host", "jax", "host", "host copy", (), 1),
    }


def test_the_observer_is_installed_only_while_a_step_executes() -> None:
    before = ConversionObserver.current
    conversions = StepConversions()
    with conversions.during_step(0):
        assert ConversionObserver.current.wants_records
        with conversions.during_step(1):
            ConversionObserver.current.record(_record(*DLPACK))
        assert ConversionObserver.current.wants_records
        ConversionObserver.current.record(_record(*DOWNLOAD))
    assert ConversionObserver.current is before
    assert not before.wants_records
    assert _counts(conversions) == {(1, *DLPACK, (), 1), (0, *DOWNLOAD, (), 1)}


def _float32_plane(aligned_to_64_bytes: bool) -> np.ndarray:
    """A C-contiguous plane whose first byte is, or is not, on a 64-byte boundary."""
    spare = np.zeros(16 * 16 + 32, np.float32)
    for offset in range(32):
        plane = spare[offset : offset + 256].reshape(16, 16)
        if (plane.ctypes.data % 64 == 0) == aligned_to_64_bytes:
            return plane
    raise AssertionError("no such offset")


@pytest.mark.skipif(find_spec("jax") is None, reason="needs JAX")
def test_steps_executing_at_once_in_threads_each_keep_their_own_conversions() -> None:
    """Each thread converts real arrays while the other is inside its step."""
    lanes = {"A01": StepConversions(), "A02": StepConversions()}
    planes = {"A01": 3, "A02": 5}
    both_inside = threading.Barrier(2)
    after: dict[str, bool] = {}
    numpy_library = ArrayLibrary.of(np.zeros(1))
    # Imported here: two threads that first use a library at once can be handed
    # its half-imported module by ArrayBridge (AB1 issue 7).
    assert MemoryType.JAX.library.module is not None

    def lane(axis_id: str) -> None:
        with lanes[axis_id].during_step(int(axis_id[-1])):
            both_inside.wait(timeout=30)
            for _ in range(planes[axis_id]):
                numpy_library.convert_to(
                    _float32_plane(True), MemoryType.JAX.library, HOST
                )
        after[axis_id] = ConversionObserver.current.wants_records

    threads = [threading.Thread(target=lane, args=(axis_id,)) for axis_id in lanes]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join(timeout=60)

    assert after == {"A01": False, "A02": False}
    assert not ConversionObserver.current.wants_records
    for axis_id, conversions in lanes.items():
        assert {
            (seen.step_index, seen.placements) for seen in conversions.observed()
        } == {(int(axis_id[-1]), ("numpy", "host", "jax", "host"))}
        assert sum(seen.count for seen in conversions.observed()) == planes[axis_id]


def test_a_thread_started_inside_a_step_is_counted_only_in_a_copy_of_the_context() -> None:
    """ArrayBridge's observer belongs to the context: this is why each lane installs its own."""
    conversions = StepConversions()

    def convert() -> None:
        ConversionObserver.current.record(_record(*DLPACK))

    with conversions.during_step(0):
        plain = threading.Thread(target=convert)
        plain.start()
        plain.join()
        assert _counts(conversions) == set()
        copied = threading.Thread(target=contextvars.copy_context().run, args=(convert,))
        copied.start()
        copied.join()

    assert _counts(conversions) == {(0, *DLPACK, (), 1)}


def _compared(plans, observed: StepConversions) -> list[tuple]:
    return [
        (
            row.step_index,
            row.boundaries,
            row.planned,
            row.observed,
            row.declined_mechanisms,
            row.agreement,
            row.count,
        )
        for row in compare_with_plan(planned_conversions(plans), observed)
    ]


def test_a_run_that_did_what_the_plan_states_matches() -> None:
    plans = _plans((normalize,), (segment,), (measure,), devices=GPU, written=frozenset({2}))
    observed = (
        _seen(0, _record("numpy", "host", "cupy", "accelerator:0", "host copy"))
        .merge(_seen(1, _record(*DLPACK)))
        .merge(_seen(2, _record(*DOWNLOAD)))
    )

    assert _compared(plans, observed) == [
        (0, ("stored planes -> normalize",), "host copy", "host copy", (), "matches", 1),
        (1, ("normalize -> segment",), "dlpack", "dlpack", (), "matches", 1),
        (2, ("segment -> measure",), "host copy", "host copy", (), "matches", 1),
        (2, ("measure -> stored planes",), "stays in place", "no record", (), "matches", 0),
    ]


def test_a_declined_planned_route_followed_by_the_next_one_is_an_explained_difference() -> None:
    plans = _plans((normalize,), (segment,), devices=GPU)
    observed = _seen(
        0, _record("numpy", "host", "cupy", "accelerator:0", "host copy")
    ).merge(_seen(1, _record(*DLPACK[:4], "host copy", ("dlpack",))))

    assert _compared(plans, observed)[1] == (
        1,
        ("normalize -> segment",),
        "dlpack",
        "host copy",
        ("dlpack",),
        "explained difference",
        1,
    )


def test_a_difference_the_record_does_not_explain_is_a_mismatch() -> None:
    plans = _plans((normalize,), (segment,), (measure,), devices=GPU)
    observed = _seen(
        1,
        _record(*DLPACK[:4], "host copy"),
        _record(*DLPACK[:4], "host copy", ("device move",)),
        _record("torch", "accelerator:0", "jax", "host", "host copy"),
    )
    mismatch = "unexplained mismatch"

    assert _compared(plans, observed) == [
        (0, ("stored planes -> normalize",), "host copy", "no record", (), mismatch, 0),
        (1, ("normalize -> segment",), "dlpack", "host copy", (), mismatch, 1),
        (1, ("normalize -> segment",), "dlpack", "host copy", ("device move",), mismatch, 1),
        (2, ("segment -> measure",), "host copy", "no record", (), mismatch, 0),
        (1, (), "not planned", "host copy", (), mismatch, 1),
    ]


def test_boundaries_of_one_step_between_the_same_placements_share_their_records() -> None:
    plans = _plans(
        (segment, measure, segment, measure), devices={"numpy": HOST, "torch": HOST}
    )
    observed = _seen(
        0,
        _record("numpy", "host", "torch", "host", "shared host buffer"),
        _record("torch", "host", "numpy", "host", "shared host buffer"),
    )
    shared = "shared host buffer"

    assert _compared(plans, observed) == [
        (0, ("stored planes -> segment", "measure -> segment"), shared, shared, (), "matches", 1),
        (0, ("segment -> measure",), shared, shared, (), "matches", 1),
    ]


@pytest.mark.skipif(find_spec("jax") is None, reason="needs JAX")
def test_numpy_to_jax_on_host_is_shared_when_aligned_and_an_explained_copy_when_not() -> None:
    """Real conversions: the plan says shared, and JAX copies a buffer it cannot wrap."""
    plans = _plans((smooth,), devices={"jax": HOST})
    numpy_library = ArrayLibrary.of(np.zeros(1))
    observed = StepConversions()
    with observed.during_step(0):
        for aligned in (True, False, False):
            numpy_library.convert_to(_float32_plane(aligned), MemoryType.JAX.library, HOST)

    rows = compare_with_plan(planned_conversions(plans), observed)

    shared = "shared host buffer"
    assert sorted(
        (row.planned, row.observed, row.declined_mechanisms, row.agreement, row.count)
        for row in rows
    ) == [
        (shared, "host copy", (shared,), "explained difference", 2),
        (shared, shared, (), "matches", 1),
    ]
    table = format_compared_conversions(rows)
    [explained] = [line for line in table.splitlines() if "explained difference" in line]
    assert "host copy" in explained and "stored planes -> smooth" in explained


def test_compared_rows_are_plain_json_and_the_table_shows_every_outcome() -> None:
    plans = _plans((normalize,), (segment,), (measure,), devices=GPU)
    rows = compare_with_plan(
        planned_conversions(plans),
        _seen(1, _record(*DLPACK[:4], "host copy", ("dlpack",))).merge(
            _seen(2, _record(*DOWNLOAD))
        ),
    )

    assert (
        tuple(
            ComparedConversions.from_json(row)
            for row in json.loads(json.dumps([row.to_json() for row in rows]))
        )
        == rows
    )
    lines = format_compared_conversions(rows).splitlines()
    assert lines[0].split() == [
        "step",
        "boundary",
        "source",
        "target",
        "planned",
        "observed",
        "declined",
        "agreement",
        "calls",
        "MB",
        "seconds",
    ]
    outcomes = ("unexplained mismatch", "explained difference", "matches")
    assert [
        next(label for label in outcomes if label in line) for line in lines[1:]
    ] == list(outcomes)
    assert lines[2].split()[-3:] == ["1", "1.0", "0.500"]


def test_a_client_reads_the_compared_rows_the_server_attached_to_the_run() -> None:
    from types import MappingProxyType

    from zmqruntime.messages import ExecutionRecord, ExecutionStatus

    from openhcs.core.orchestrator.bundle_execution import BundleExecutionExtras
    from openhcs.runtime.zmq_execution_client import ZMQCompiledPipelineRun
    from openhcs.runtime.zmq_server_hooks import ZMQResultsSummaryEnricher

    plans = _plans((normalize,), (segment,), devices=GPU)
    rows = compare_with_plan(
        planned_conversions(plans),
        _seen(1, _record(*DLPACK[:4], "host copy", ("dlpack",))),
    )
    served = ExecutionRecord(
        execution_id="run", subject_id="plate", status=ExecutionStatus.COMPLETE.value
    )
    served.set_extra(
        BundleExecutionExtras.EXECUTION_RECORD_KEY,
        BundleExecutionExtras(viewer_states_by_port=MappingProxyType({}), conversions=rows),
    )
    ZMQResultsSummaryEnricher({}).attach(execution_id="run", record=served)
    received = ExecutionRecord(
        execution_id="run",
        subject_id="plate",
        status=ExecutionStatus.COMPLETE.value,
        results_summary=json.loads(json.dumps(served.results_summary)),
    )

    run = ZMQCompiledPipelineRun(
        compile_artifact_id="compiled",
        execution_id="run",
        request=None,
        compile_record=received,
        execution_record=received,
        completion_observed_at=0.0,
    )

    assert run.conversions == rows
    assert [row.agreement for row in run.conversions] == [
        "unexplained mismatch",
        "explained difference",
    ]


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
