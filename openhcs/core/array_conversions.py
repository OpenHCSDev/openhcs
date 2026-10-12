"""The array conversions of a pipeline: those its plan states, and those a run made.

An image changes array library or device where a step reads its input, where one
function of a step hands its output to the next, and where an output is written
to a file. The plan already holds what decides each of these: the libraries the
functions declare and the device assigned to each library. Planned conversions
are therefore computed from the plans whenever they are asked for and never
stored beside them. The mechanism of each is ArrayBridge's answer for the two
placements.

What a run really did is counted by ArrayBridge's conversion observer, which is
installed only while a step executes, and kept by the step that was executing.
"""

from __future__ import annotations

from collections.abc import Iterator, Mapping, Sequence
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field
from threading import Lock
from typing import ClassVar

from arraybridge.conversion import (
    ConversionCounters,
    ConversionKey,
    ConversionObserver,
    ConversionRecord,
    ConversionRoute,
    IgnoreConversions,
)
from arraybridge.devices import HOST
from arraybridge.types import MemoryType

from openhcs.constants.constants import Backend
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.runtime_array_values import ArrayPlacement

STORED_PLANES = "stored planes"
STORED_PLANE_PLACEMENT = ArrayPlacement(MemoryType.NUMPY.library, HOST)
"""Where a plane read from a file store is, and where one must be to be written."""

NO_CONVERSION = "none"
"""The mechanism shown where source and target placement are the same."""


@dataclass(frozen=True, slots=True)
class PlacedArrays:
    """Arrays at one point of a pipeline: what produced them and where they are."""

    producer: str
    placement: ArrayPlacement


@dataclass(frozen=True, slots=True)
class PlannedConversion:
    """One boundary of a compiled pipeline and the conversion made there.

    ``step_index`` is the step during whose execution the conversion happens.
    """

    step_index: int
    boundary: str
    source: ArrayPlacement
    target: ArrayPlacement

    @property
    def makes_a_new_array(self) -> bool:
        return self.source != self.target

    @property
    def mechanism(self) -> str:
        """ArrayBridge's first route for the two placements."""
        if not self.makes_a_new_array:
            return NO_CONVERSION
        return str(
            ConversionRoute.planned(
                self.source.library,
                self.source.device,
                self.target.library,
                self.target.device,
            ).mechanism
        )

    @property
    def key(self) -> ConversionKey:
        """The key ArrayBridge's counters give this conversion when it happens."""
        return (
            str(self.source.library.name),
            self.source.device.label,
            str(self.target.library.name),
            self.target.device.label,
            self.mechanism,
        )

    def describe(self) -> str:
        return (
            f"{self.boundary}: {self.source.describe()} -> "
            f"{self.target.describe()} by {self.mechanism}"
        )


FunctionChain = tuple[tuple[PlacedArrays, PlacedArrays], ...]


def _function_chains(plan: CompiledStepPlan) -> tuple[FunctionChain, ...]:
    """Per group of the step, where each array-declaring function reads and leaves arrays."""
    pattern = plan.compiled_function_pattern
    if pattern is None:
        return ()
    chains = (
        tuple(
            (
                PlacedArrays(name, plan.placement_for(declared_input)),
                PlacedArrays(name, plan.placement_for(declared_output)),
            )
            for name, declared_input, declared_output in (
                (
                    invocation.contract.function_name
                    + (f" [{group.group_key}]" if pattern.is_grouped else ""),
                    invocation.input_memory_type,
                    invocation.output_memory_type,
                )
                for invocation in group.invocations
            )
            if declared_input is not None and declared_output is not None
        )
        for group in pattern.groups
    )
    return tuple(chain for chain in chains if chain)


def _main_flow_output(
    plans: Mapping[int, CompiledStepPlan], step_index: int
) -> tuple[PlacedArrays, ...]:
    """What a step leaves in the main flow; a step declaring no arrays passes its input on."""
    plan = plans[step_index]
    chains = _function_chains(plan)
    if chains:
        return tuple(dict.fromkeys(chain[-1][1] for chain in chains))
    return _main_flow_input(plans, plan)


def _main_flow_input(
    plans: Mapping[int, CompiledStepPlan], plan: CompiledStepPlan
) -> tuple[PlacedArrays, ...]:
    return plan.main_input_dependency.arriving(
        (PlacedArrays(STORED_PLANES, STORED_PLANE_PLACEMENT),),
        lambda step_index: _main_flow_output(plans, step_index),
    )


def _writes_main_flow_to_a_file_store(plan: CompiledStepPlan) -> bool:
    return (
        plan.write_backend != Backend.MEMORY.value
        or plan.materialized_output is not None
    )


def planned_step_conversions(
    plans: Mapping[int, CompiledStepPlan], step_index: int
) -> tuple[PlannedConversion, ...]:
    """Every boundary crossed while one step executes, in order."""
    plan = plans[step_index]
    conversions: list[PlannedConversion] = []
    for chain in _function_chains(plan):
        arriving = _main_flow_input(plans, plan)
        for reads, leaves in chain:
            conversions.extend(
                PlannedConversion(
                    step_index,
                    f"{each.producer} -> {reads.producer}",
                    each.placement,
                    reads.placement,
                )
                for each in arriving
            )
            arriving = (leaves,)
        if _writes_main_flow_to_a_file_store(plan):
            conversions.append(
                PlannedConversion(
                    step_index,
                    f"{chain[-1][1].producer} -> {STORED_PLANES}",
                    chain[-1][1].placement,
                    STORED_PLANE_PLACEMENT,
                )
            )
    return tuple(dict.fromkeys(conversions))


def planned_conversions(
    plans: Mapping[int, CompiledStepPlan],
) -> tuple[PlannedConversion, ...]:
    """Every boundary of a compiled pipeline, in execution order."""
    return tuple(
        conversion
        for step_index in sorted(plans)
        for conversion in planned_step_conversions(plans, step_index)
    )


def _aligned(rows: Sequence[Sequence[str]]) -> str:
    widths = [max(len(row[column]) for row in rows) for column in range(len(rows[0]))]
    return "\n".join(
        "  ".join(cell.ljust(width) for cell, width in zip(row, widths)).rstrip()
        for row in rows
    )


def format_planned_conversions(conversions: Sequence[PlannedConversion]) -> str:
    """One line per boundary of the pipeline."""
    return _aligned(
        [
            ("step", "boundary", "source", "target", "mechanism"),
            *(
                (
                    str(each.step_index),
                    each.boundary,
                    each.source.describe(),
                    each.target.describe(),
                    each.mechanism,
                )
                for each in conversions
            ),
        ]
    )


class ExecutingStepConversions(ConversionObserver):
    """Sends each conversion to the counters of the step executing in the calling thread.

    ArrayBridge has one observer per process, and several steps may execute at
    once in threads. This observer is installed when the first of them starts
    and the one it replaced is restored when the last finishes; the replaced
    observer still receives every record.
    """

    _receiver: ClassVar[ContextVar[ConversionObserver]] = ContextVar(
        "conversions_of_executing_step", default=IgnoreConversions()
    )
    _lock: ClassVar[Lock] = Lock()
    _steps_executing: ClassVar[int] = 0
    _replaced: ClassVar[ConversionObserver] = IgnoreConversions()

    def record(self, record: ConversionRecord) -> None:
        self._receiver.get().record(record)
        self._replaced.record(record)

    @classmethod
    @contextmanager
    def sending_to(cls, counters: ConversionCounters) -> Iterator[None]:
        """Count this thread's conversions into ``counters`` for the duration of a block."""
        with cls._lock:
            if cls._steps_executing == 0:
                cls._replaced = cls().install()
            cls._steps_executing += 1
        token = cls._receiver.set(counters)
        try:
            yield
        finally:
            cls._receiver.reset(token)
            with cls._lock:
                cls._steps_executing -= 1
                if cls._steps_executing == 0:
                    cls._replaced.install()
                    cls._replaced = IgnoreConversions()


@dataclass(slots=True)
class StepConversions:
    """The conversions made while each step executed, by step index.

    Plain data: a worker returns it with its result and the parent merges them.
    """

    RESULTS_SUMMARY_KEY: ClassVar[str] = "array_conversions"
    STEP_INDEX: ClassVar[str] = "step_index"

    by_step: dict[int, ConversionCounters] = field(default_factory=dict)

    @contextmanager
    def during_step(self, step_index: int) -> Iterator[None]:
        """Count the conversions the calling thread makes in a block for one step."""
        counters = self.by_step.setdefault(step_index, ConversionCounters())
        with ExecutingStepConversions.sending_to(counters):
            yield

    def merge(self, other: StepConversions) -> StepConversions:
        """Add another worker's or another axis's counts into these."""
        for step_index, counters in other.by_step.items():
            self.by_step.setdefault(step_index, ConversionCounters()).merge(counters)
        return self

    def total(self) -> ConversionCounters:
        """The counts of the whole run, without the step."""
        total = ConversionCounters()
        for counters in self.by_step.values():
            total.merge(counters)
        return total

    def to_json(self) -> list[dict[str, str | int | float]]:
        """ArrayBridge's rows, each with the index of its step."""
        return [
            {self.STEP_INDEX: step_index, **row}
            for step_index in sorted(self.by_step)
            for row in self.by_step[step_index].to_json()
        ]

    @classmethod
    def from_json(cls, rows: Sequence[Mapping[str, str | int | float]]) -> StepConversions:
        conversions = cls()
        for row in rows:
            conversions.merge(
                cls({int(row[cls.STEP_INDEX]): ConversionCounters.from_json([dict(row)])})
            )
        return conversions


def format_planned_and_observed(
    planned: Sequence[PlannedConversion], observed: StepConversions
) -> str:
    """Each planned boundary beside what the run did between the same two placements.

    A conversion the run made that no boundary of its step plans is listed
    after the boundaries with ``unplanned`` in place of the boundary.
    """
    rows: list[tuple[str, ...]] = [
        (
            "step",
            "boundary",
            "source",
            "target",
            "planned",
            "observed",
            "calls",
            "MB",
            "seconds",
        )
    ]
    remaining = {
        (step_index, key): total
        for step_index, counters in observed.by_step.items()
        for key, total in counters.totals.items()
    }
    for each in planned:
        matching = sorted(
            observed_key
            for observed_key in remaining
            if observed_key[0] == each.step_index and observed_key[1][:4] == each.key[:4]
        )
        totals = [remaining.pop(observed_key) for observed_key in matching]
        rows.append(
            (
                str(each.step_index),
                each.boundary,
                each.source.describe(),
                each.target.describe(),
                each.mechanism,
                ", ".join(observed_key[1][4] for observed_key in matching) or NO_CONVERSION,
                str(sum(total.count for total in totals)),
                f"{sum(total.nbytes for total in totals) / 1e6:.1f}",
                f"{sum(total.seconds for total in totals):.3f}",
            )
        )
    for (step_index, key), total in sorted(remaining.items()):
        rows.append(
            (
                str(step_index),
                "unplanned",
                f"{key[0]} on {key[1]}",
                f"{key[2]} on {key[3]}",
                "",
                key[4],
                str(total.count),
                f"{total.nbytes / 1e6:.1f}",
                f"{total.seconds:.3f}",
            )
        )
    return _aligned(rows)


__all__ = [
    "ExecutingStepConversions",
    "PlannedConversion",
    "StepConversions",
    "format_planned_and_observed",
    "format_planned_conversions",
    "planned_conversions",
    "planned_step_conversions",
]
