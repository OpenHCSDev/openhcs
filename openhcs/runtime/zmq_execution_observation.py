"""Runtime-observation export for ZMQ executions."""

from __future__ import annotations

import gzip
import pickle
from collections.abc import Iterable, Mapping
from dataclasses import dataclass, field
from pathlib import Path

from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.orchestrator.execution_result import ExecutionResult, ExecutionStatus
from openhcs.core.runtime_execution_validation import (
    RuntimeArtifactExecutionExpectation,
    RuntimeArtifactExecutionObservation,
    runtime_artifact_execution_failures,
)
from openhcs.core.runtime_exports import RuntimeExportObservation
from openhcs.core.runtime_stores import StoredRuntimeValue
from openhcs.core.source_matching import SourceImageSetIdentityPolicy
from openhcs.runtime.environment_provenance import RuntimeEnvironmentSnapshot

ZMQ_RUNTIME_OBSERVATION_EXPORT_SCHEMA_VERSION = 8
ZMQ_RUNTIME_OUTCOME_EXPORT_SCHEMA_VERSION = 4


def _axis_membership_failures(
    expected_axis_ids: tuple[str, ...] | None,
    observed_axis_ids: Mapping[str, object],
) -> tuple[str, ...]:
    """Compare execution coverage with compiler-owned axis membership."""

    if expected_axis_ids is None:
        return ()  # Archived exports did not retain compiled membership.
    expected = frozenset(expected_axis_ids)
    observed = frozenset(observed_axis_ids)
    failures = []
    if len(expected) != len(expected_axis_ids):
        failures.append("compiled execution contains duplicate axis identities")
    missing = sorted(expected - observed)
    unexpected = sorted(observed - expected)
    if missing:
        failures.append(f"compiled axes have no execution outcome: {missing!r}")
    if unexpected:
        failures.append(f"execution outcomes have no compiled axis: {unexpected!r}")
    return tuple(failures)


def _restore_legacy_axis_expectation(
    expectation: RuntimeArtifactExecutionExpectation,
) -> RuntimeArtifactExecutionExpectation:
    """Rebuild archived expectations before compiled axis ownership existed."""

    return RuntimeArtifactExecutionExpectation(
        artifact_kinds=expectation.artifact_kinds,
        exports=expectation.exports,
        artifact_viewer=getattr(expectation, "artifact_viewer", ()),
    )


@dataclass(frozen=True, slots=True)
class ZMQExecutionAxisOutcome:
    """Small per-axis result retained without worker runtime values."""

    status: ExecutionStatus
    failed_combination: str | None = None
    error_message: str | None = None

    @classmethod
    def from_result(cls, result: ExecutionResult) -> ZMQExecutionAxisOutcome:
        return cls(
            status=result.status,
            failed_combination=result.failed_combination,
            error_message=result.error_message,
        )


@dataclass(frozen=True, slots=True)
class ZMQRuntimeExecutionOutcomeExport:
    """Ordinary execution outcome without parent-side runtime-value retention."""

    schema_version: int
    outcomes_by_axis: Mapping[str, ZMQExecutionAxisOutcome]
    output_roots: tuple[Path, ...]
    server_environment: RuntimeEnvironmentSnapshot | None = None
    execution_id: str | None = None
    compiled_axis_ids: tuple[str, ...] | None = None
    exports: RuntimeExportObservation | None = None

    @classmethod
    def from_execution(
        cls,
        *,
        compiled_axis_ids: Iterable[str],
        execution_results: Mapping[str, ExecutionResult],
        output_roots: tuple[Path, ...],
        server_environment: RuntimeEnvironmentSnapshot | None = None,
        execution_id: str | None = None,
        exports: RuntimeExportObservation | None = None,
    ) -> ZMQRuntimeExecutionOutcomeExport:
        return cls(
            schema_version=ZMQ_RUNTIME_OUTCOME_EXPORT_SCHEMA_VERSION,
            outcomes_by_axis={
                str(axis_id): ZMQExecutionAxisOutcome.from_result(result)
                for axis_id, result in execution_results.items()
            },
            output_roots=tuple(Path(root) for root in output_roots),
            server_environment=server_environment,
            execution_id=execution_id,
            compiled_axis_ids=tuple(str(axis_id) for axis_id in compiled_axis_ids),
            exports=exports,
        )

    @classmethod
    def read(cls, path: Path) -> ZMQRuntimeExecutionOutcomeExport:
        with gzip.open(Path(path), "rb") as handle:
            payload = pickle.load(handle)
        if not isinstance(payload, cls):
            raise TypeError(
                "ZMQ runtime outcome export must contain "
                f"{cls.__name__}, got {type(payload).__name__}."
            )
        if payload.schema_version == 1:
            # Older slotted pickles have no execution identity slot.
            return cls(
                schema_version=payload.schema_version,
                outcomes_by_axis=payload.outcomes_by_axis,
                output_roots=payload.output_roots,
                server_environment=payload.server_environment,
                execution_id=None,
                compiled_axis_ids=None,
                exports=None,
            )
        if payload.schema_version == 2:
            return cls(
                schema_version=payload.schema_version,
                outcomes_by_axis=payload.outcomes_by_axis,
                output_roots=payload.output_roots,
                server_environment=payload.server_environment,
                execution_id=payload.execution_id,
                compiled_axis_ids=None,
                exports=None,
            )
        if payload.schema_version == 3:
            return cls(
                schema_version=payload.schema_version,
                outcomes_by_axis=payload.outcomes_by_axis,
                output_roots=payload.output_roots,
                server_environment=payload.server_environment,
                execution_id=payload.execution_id,
                compiled_axis_ids=payload.compiled_axis_ids,
                exports=None,
            )
        if payload.schema_version != ZMQ_RUNTIME_OUTCOME_EXPORT_SCHEMA_VERSION:
            raise ValueError(
                "Unsupported ZMQ runtime outcome export schema version "
                f"{payload.schema_version!r}."
            )
        return payload

    def write(self, path: Path) -> None:
        target = Path(path)
        target.parent.mkdir(parents=True, exist_ok=True)
        with gzip.open(target, "xb", compresslevel=1) as handle:
            pickle.dump(self, handle, protocol=pickle.HIGHEST_PROTOCOL)

    @property
    def axis_count(self) -> int:
        return len(self.outcomes_by_axis)

    @property
    def successful_axis_count(self) -> int:
        return sum(
            outcome.status is ExecutionStatus.SUCCESS
            for outcome in self.outcomes_by_axis.values()
        )

    def require_successful_axes(self) -> None:
        membership_failures = _axis_membership_failures(
            self.compiled_axis_ids,
            self.outcomes_by_axis,
        )
        unsuccessful = {
            axis_id: outcome.status.value
            for axis_id, outcome in self.outcomes_by_axis.items()
            if outcome.status is not ExecutionStatus.SUCCESS
        }
        failures = list(membership_failures)
        if unsuccessful:
            failures.append(f"Unsuccessful execution axes: {unsuccessful!r}.")
        if failures:
            raise RuntimeError("\n".join(failures))


@dataclass(frozen=True, slots=True)
class ZMQRuntimeExecutionObservationExport:
    """Pickle-safe runtime observation emitted by a ZMQ server execution."""

    schema_version: int
    expectation: RuntimeArtifactExecutionExpectation
    records_by_axis: Mapping[str, tuple[StoredRuntimeValue, ...]]
    exports: RuntimeExportObservation
    output_roots: tuple[Path, ...]
    execution_success_by_axis: Mapping[str, bool]
    source_image_set_identity_policy: SourceImageSetIdentityPolicy = field(
        default_factory=SourceImageSetIdentityPolicy
    )
    server_environment: RuntimeEnvironmentSnapshot | None = None
    execution_id: str | None = None

    @classmethod
    def from_execution(
        cls,
        *,
        compiled_contexts: Mapping[str, ProcessingContext],
        execution_results: Mapping[str, ExecutionResult],
        output_roots: tuple[Path, ...],
        server_environment: RuntimeEnvironmentSnapshot | None = None,
        execution_id: str | None = None,
    ) -> ZMQRuntimeExecutionObservationExport:
        observation = RuntimeArtifactExecutionObservation.from_contexts(
            compiled_contexts
        )
        return cls(
            schema_version=ZMQ_RUNTIME_OBSERVATION_EXPORT_SCHEMA_VERSION,
            expectation=RuntimeArtifactExecutionExpectation.from_compiled_contexts(
                compiled_contexts
            ),
            records_by_axis=dict(observation.records_by_axis),
            exports=observation.exports,
            output_roots=tuple(Path(root) for root in output_roots),
            execution_success_by_axis={
                str(axis_id): result.is_success()
                for axis_id, result in execution_results.items()
            },
            source_image_set_identity_policy=(
                observation.source_image_set_identity_policy
            ),
            server_environment=server_environment,
            execution_id=execution_id,
        )

    @classmethod
    def read(cls, path: Path) -> ZMQRuntimeExecutionObservationExport:
        with gzip.open(Path(path), "rb") as handle:
            payload = pickle.load(handle)
        if not isinstance(payload, cls):
            raise TypeError(
                "ZMQ runtime observation export must contain "
                f"{cls.__name__}, got {type(payload).__name__}."
            )
        if payload.schema_version == 5:
            # Slotted v5 pickles deserialize without the newly declared slot.
            # Rebuild explicitly so archived ordinary observations stay readable.
            return cls(
                schema_version=payload.schema_version,
                expectation=_restore_legacy_axis_expectation(payload.expectation),
                records_by_axis=payload.records_by_axis,
                exports=payload.exports,
                output_roots=payload.output_roots,
                execution_success_by_axis=payload.execution_success_by_axis,
                source_image_set_identity_policy=(
                    payload.source_image_set_identity_policy
                ),
                server_environment=None,
                execution_id=None,
            )
        if payload.schema_version == 6:
            # Version 6 predates the execution identity slot.
            return cls(
                schema_version=payload.schema_version,
                expectation=_restore_legacy_axis_expectation(payload.expectation),
                records_by_axis=payload.records_by_axis,
                exports=payload.exports,
                output_roots=payload.output_roots,
                execution_success_by_axis=payload.execution_success_by_axis,
                source_image_set_identity_policy=(
                    payload.source_image_set_identity_policy
                ),
                server_environment=payload.server_environment,
                execution_id=None,
            )
        if payload.schema_version == 7:
            # Version 7 predates compiled axis ownership expectations. Keep its
            # all-axes validation semantics for archived observations.
            return cls(
                schema_version=payload.schema_version,
                expectation=_restore_legacy_axis_expectation(payload.expectation),
                records_by_axis=payload.records_by_axis,
                exports=payload.exports,
                output_roots=payload.output_roots,
                execution_success_by_axis=payload.execution_success_by_axis,
                source_image_set_identity_policy=(
                    payload.source_image_set_identity_policy
                ),
                server_environment=payload.server_environment,
                execution_id=payload.execution_id,
            )
        if payload.schema_version != ZMQ_RUNTIME_OBSERVATION_EXPORT_SCHEMA_VERSION:
            raise ValueError(
                "Unsupported ZMQ runtime observation export schema version "
                f"{payload.schema_version!r}."
            )
        return payload

    def write(self, path: Path) -> None:
        target = Path(path)
        target.parent.mkdir(parents=True, exist_ok=True)
        with gzip.open(target, "xb", compresslevel=1) as handle:
            pickle.dump(self, handle, protocol=pickle.HIGHEST_PROTOCOL)

    def observation(self) -> RuntimeArtifactExecutionObservation:
        return RuntimeArtifactExecutionObservation(
            records_by_axis={
                str(axis_id): tuple(records)
                for axis_id, records in self.records_by_axis.items()
            },
            exports=self.exports,
            source_image_set_identity_policy=(self.source_image_set_identity_policy),
        )

    @property
    def axis_count(self) -> int:
        return len(self.execution_success_by_axis)

    def execution_failures(self) -> tuple[str, ...]:
        expected_axis_ids = (
            tuple(item.axis_id for item in self.expectation.axis_expectations)
            if self.expectation.axis_expectations is not None
            else None
        )
        membership_failures = _axis_membership_failures(
            expected_axis_ids,
            self.execution_success_by_axis,
        )
        failed = tuple(
            axis_id
            for axis_id, success in self.execution_success_by_axis.items()
            if not success
        )
        if failed:
            return (*membership_failures, f"unsuccessful execution axes: {failed!r}")
        return membership_failures

    def require_valid_observation(self) -> RuntimeArtifactExecutionObservation:
        """Return the observation after validating execution and artifact outputs."""

        observation = self.observation()
        failures = (
            *self.execution_failures(),
            *runtime_artifact_execution_failures(self.expectation, observation),
        )
        if failures:
            raise RuntimeError(
                "ZMQ runtime execution violated compiled expectations:\n"
                + "\n".join(f"- {failure}" for failure in failures)
            )
        return observation
