"""The array conversions of a pipeline: those its plan states, and those a run made.

An image changes array library or device where a step reads its input, where one
function of a step hands its output to the next, and where an output is written
to a file. The plan already holds what decides each of these: the libraries the
functions declare and the device assigned to each library. Planned conversions
are therefore computed from the plans whenever they are asked for and never
stored beside them. The mechanism of each is ArrayBridge's answer for the two
placements.

What a run really did is counted by ArrayBridge's conversion observer, which the
thread executing a step installs for the duration of that step. The two are then
compared: a row matches the plan, differs in a way ArrayBridge's record explains,
or is a mismatch nothing explains.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Iterator, Mapping, Sequence
from contextlib import contextmanager
from dataclasses import asdict, dataclass, field
from typing import Any, ClassVar

from arraybridge.conversion import (
    ConversionCounters,
    ConversionObserver,
    ConversionRecord,
    ConversionRoute,
)
from arraybridge.devices import HOST
from arraybridge.types import MemoryType
from metaclass_registry import AutoRegisterMeta

from openhcs.constants.constants import Backend
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.runtime_array_values import ArrayPlacement
from openhcs.utils.text_table import aligned_columns

PlacementKey = tuple[str, str, str, str]
"""Source library and device, target library and device, as ArrayBridge's records name them."""

STORED_PLANES = "stored planes"
STORED_PLANE_PLACEMENT = ArrayPlacement(MemoryType.NUMPY.library, HOST)
"""Where a plane read from a file store is, and where one must be to be written."""


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
    def routes(self) -> tuple[type[ConversionRoute], ...]:
        """ArrayBridge's routes for the two placements, the one tried first first."""
        return ConversionRoute.candidates(
            self.source.library,
            self.source.device,
            self.target.library,
            self.target.device,
        )

    @property
    def mechanism(self) -> str:
        """ArrayBridge's first route for the two placements."""
        return str(self.routes[0].mechanism)

    @property
    def placements(self) -> PlacementKey:
        """The two placements as ArrayBridge's records name them."""
        return (
            str(self.source.library.name),
            self.source.device.label,
            str(self.target.library.name),
            self.target.device.label,
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


def format_planned_conversions(conversions: Sequence[PlannedConversion]) -> str:
    """One line per boundary of the pipeline."""
    return "\n".join(
        aligned_columns(
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
    )


NO_RECORD = "no record"
"""The observed mechanism where a run wrote no record between two placements."""

NOT_PLANNED = "not planned"
"""The planned mechanism of a conversion no boundary of its step plans."""


@dataclass(frozen=True, slots=True)
class ObservedConversions:
    """The conversions one step made between two placements in one way, counted.

    ``declined_mechanisms`` are the routes ArrayBridge tried first that did not
    carry these arrays, as its records list them.
    """

    step_index: int
    placements: PlacementKey
    mechanism: str
    declined_mechanisms: tuple[str, ...]
    count: int
    nbytes: int
    seconds: float


@dataclass(frozen=True, slots=True)
class _CountingForStep(ConversionObserver):
    """The observer of the thread executing one step: its records go to that step."""

    conversions: StepConversions
    step_index: int

    def record(self, record: ConversionRecord) -> None:
        self.conversions.counters.setdefault(
            (self.step_index, record.declined_mechanisms), ConversionCounters()
        ).record(record)


@dataclass(slots=True)
class StepConversions:
    """The conversions made while each step executed.

    ArrayBridge's counters do not key on the routes a record lists as declined,
    so there is one set of counters per step and tuple of declined routes.
    Plain data: a worker returns it with its result and the parent merges them.
    """

    counters: dict[tuple[int, tuple[str, ...]], ConversionCounters] = field(
        default_factory=dict
    )

    @contextmanager
    def during_step(self, step_index: int) -> Iterator[None]:
        """Count the conversions the calling thread makes in a block for one step.

        ArrayBridge's observer belongs to the thread that installs it, so this
        is entered in the thread that executes the step.
        """
        with _CountingForStep(self, step_index).installed():
            yield

    def merge(self, other: StepConversions) -> StepConversions:
        """Add another worker's or another axis's counts into these."""
        for key, counters in other.counters.items():
            self.counters.setdefault(key, ConversionCounters()).merge(counters)
        return self

    def observed(self) -> tuple[ObservedConversions, ...]:
        """Every kind of conversion that was recorded, by step."""
        return tuple(
            ObservedConversions(
                step_index,
                key[:4],
                key[4],
                declined,
                total.count,
                total.nbytes,
                total.seconds,
            )
            for (step_index, declined), counters in sorted(self.counters.items())
            for key, total in sorted(counters.totals.items())
        )


class PlanAgreement(ABC, metaclass=AutoRegisterMeta):
    """How what a run recorded between two placements relates to the plan.

    Leaves are asked in the order they are declared here; the first that holds
    names the outcome.
    """

    __registry_key__ = "label"
    label: ClassVar[str | None] = None

    @classmethod
    @abstractmethod
    def holds(
        cls, routes: Sequence[type[ConversionRoute]], seen: ObservedConversions
    ) -> bool:
        """``routes`` are ArrayBridge's for the planned placements, first choice first."""

    @classmethod
    def of(
        cls, routes: Sequence[type[ConversionRoute]], seen: ObservedConversions
    ) -> type[PlanAgreement]:
        return next(
            agreement
            for agreement in cls.__registry__.values()
            if agreement.holds(routes, seen)
        )


class Matches(PlanAgreement):
    """The run did what the plan states; for a route that writes no record, nothing."""

    label = "matches"

    @classmethod
    def holds(
        cls, routes: Sequence[type[ConversionRoute]], seen: ObservedConversions
    ) -> bool:
        planned = routes[0]
        if not planned.writes_a_record:
            return seen.count == 0
        return seen.mechanism == planned.mechanism and not seen.declined_mechanisms


class ExplainedDifference(PlanAgreement):
    """The planned route could not carry these arrays and the next route did.

    ArrayBridge's records say so: every route before the observed one is listed
    as declined, in the order the routes are tried.
    """

    label = "explained difference"

    @classmethod
    def holds(
        cls, routes: Sequence[type[ConversionRoute]], seen: ObservedConversions
    ) -> bool:
        tried = (*seen.declined_mechanisms, seen.mechanism)
        return len(tried) > 1 and tried == tuple(
            str(route.mechanism) for route in routes[: len(tried)]
        )


class UnexplainedMismatch(PlanAgreement):
    """Anything else: a planned conversion never recorded, or one nothing explains."""

    label = "unexplained mismatch"

    @classmethod
    def holds(
        cls, routes: Sequence[type[ConversionRoute]], seen: ObservedConversions
    ) -> bool:
        return True


@dataclass(frozen=True, slots=True)
class ComparedConversions:
    """What a run recorded between two placements in one step, beside the plan.

    ``boundaries`` are the boundaries of the step that plan this crossing; none
    when no boundary does. Plain fields: dumps to JSON.
    """

    RESULTS_SUMMARY_KEY: ClassVar[str] = "array_conversions"

    step_index: int
    boundaries: tuple[str, ...]
    source_library: str
    source_device: str
    target_library: str
    target_device: str
    planned: str
    observed: str
    declined_mechanisms: tuple[str, ...]
    agreement: str
    count: int
    nbytes: int
    seconds: float

    @classmethod
    def of(
        cls,
        boundaries: Sequence[PlannedConversion],
        seen: ObservedConversions,
        planned: str,
        agreement: type[PlanAgreement],
    ) -> ComparedConversions:
        return cls(
            seen.step_index,
            tuple(each.boundary for each in boundaries),
            *seen.placements,
            planned,
            seen.mechanism,
            seen.declined_mechanisms,
            str(agreement.label),
            seen.count,
            seen.nbytes,
            seen.seconds,
        )

    def to_json(self) -> dict[str, str | int | float | list[str]]:
        return {
            **asdict(self),
            "boundaries": list(self.boundaries),
            "declined_mechanisms": list(self.declined_mechanisms),
        }

    @classmethod
    def from_json(cls, row: Mapping[str, Any]) -> ComparedConversions:
        return cls(
            **{
                **row,
                "boundaries": tuple(row["boundaries"]),
                "declined_mechanisms": tuple(row["declined_mechanisms"]),
            }
        )


def compare_with_plan(
    planned: Sequence[PlannedConversion], observed: StepConversions
) -> tuple[ComparedConversions, ...]:
    """Each crossing a step plans beside what the run recorded there, then the rest.

    Boundaries of one step between the same two placements are one crossing:
    the records do not say which boundary a conversion was made at. A crossing
    with no record is one row with ``NO_RECORD``; a recorded conversion no
    boundary of its step plans is a row of its own after the planned ones.
    """
    unplanned = list(observed.observed())
    crossings: dict[tuple[int, PlacementKey], list[PlannedConversion]] = {}
    for each in planned:
        crossings.setdefault((each.step_index, each.placements), []).append(each)
    rows: list[ComparedConversions] = []
    for (step_index, placements), boundaries in crossings.items():
        recorded = [
            seen
            for seen in unplanned
            if (seen.step_index, seen.placements) == (step_index, placements)
        ]
        for seen in recorded:
            unplanned.remove(seen)
        routes = boundaries[0].routes
        rows.extend(
            ComparedConversions.of(
                boundaries,
                seen,
                str(routes[0].mechanism),
                PlanAgreement.of(routes, seen),
            )
            for seen in recorded
            or [ObservedConversions(step_index, placements, NO_RECORD, (), 0, 0, 0.0)]
        )
    rows.extend(
        ComparedConversions.of((), seen, NOT_PLANNED, UnexplainedMismatch)
        for seen in unplanned
    )
    return tuple(rows)


def format_compared_conversions(rows: Sequence[ComparedConversions]) -> str:
    """One line per row: what was planned, what was recorded, and how they agree."""
    return "\n".join(
        aligned_columns(
            [
                (
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
                ),
                *(
                    (
                        str(row.step_index),
                        "; ".join(row.boundaries),
                        f"{row.source_library} on {row.source_device}",
                        f"{row.target_library} on {row.target_device}",
                        row.planned,
                        row.observed,
                        ", ".join(row.declined_mechanisms),
                        row.agreement,
                        str(row.count),
                        f"{row.nbytes / 1e6:.1f}",
                        f"{row.seconds:.3f}",
                    )
                    for row in rows
                ),
            ]
        )
    )


__all__ = [
    "ComparedConversions",
    "ExplainedDifference",
    "Matches",
    "PlanAgreement",
    "PlannedConversion",
    "StepConversions",
    "UnexplainedMismatch",
    "compare_with_plan",
    "format_compared_conversions",
    "format_planned_conversions",
    "planned_conversions",
    "planned_step_conversions",
]
