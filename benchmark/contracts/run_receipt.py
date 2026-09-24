"""Nominal persisted receipt for one comparison-suite run."""

from __future__ import annotations

import json
import os
import platform
import sys
import tempfile
import time
from collections.abc import Mapping
from dataclasses import dataclass, field, fields
from enum import Enum
from pathlib import Path
from typing import Self

from python_introspect import dataclass_from_mapping

from openhcs.serialization.json import to_jsonable

COMPARISON_SUITE_RUN_RECEIPT_SCHEMA_VERSION = (
    "openhcs.benchmark.comparison-suite-run.v1"
)


class ComparisonSuiteRunStatus(Enum):
    """Persisted lifecycle state for one comparison suite run."""

    RUNNING = "running"
    FAILED = "failed"
    COMPLETED = "completed"


@dataclass(frozen=True, slots=True, kw_only=True)
class ComparisonSuiteRunDeclaration:
    """Stable execution declaration shared by runtime context and receipt."""

    suite_id: str
    speedup_target: float
    native_reference_root: Path | None
    require_native_reference: bool
    discard_openhcs_outputs: bool
    continue_on_error: bool
    collect_memory_metric: bool
    openhcs_execution_port: int | None
    manifest_path: Path | None
    case_names: tuple[str, ...]
    repeats: int
    rerun_command: tuple[str, ...]
    rerun_working_directory: Path | None
    created_at_epoch_seconds: float = field(default_factory=time.time)

    def __post_init__(self) -> None:
        if self.speedup_target <= 0:
            raise ValueError("speedup_target must be positive.")
        if self.repeats < 1:
            raise ValueError("Comparison-suite repeats must be at least 1.")
        if self.openhcs_execution_port is not None and not (
            1 <= self.openhcs_execution_port <= 65535
        ):
            raise ValueError("openhcs_execution_port must be between 1 and 65535.")

    @property
    def expected_observation_count(self) -> int:
        """Derive the declared amount of case/repetition work for this run."""

        return len(self.case_names) * self.repeats


@dataclass(frozen=True, slots=True, kw_only=True)
class ComparisonSuiteRunReceipt(ComparisonSuiteRunDeclaration):
    """Typed, round-trippable provenance and lifecycle record for one run."""

    schema_version: str
    status: ComparisonSuiteRunStatus
    completed_observation_count: int
    updated_at_epoch_seconds: float
    finished_at_epoch_seconds: float | None
    python: str
    platform: str
    processor: str

    def __post_init__(self) -> None:
        ComparisonSuiteRunDeclaration.__post_init__(self)
        if self.schema_version != COMPARISON_SUITE_RUN_RECEIPT_SCHEMA_VERSION:
            raise ValueError(
                f"Unsupported comparison-suite receipt schema: {self.schema_version!r}."
            )
        if not 0 <= self.completed_observation_count <= self.expected_observation_count:
            raise ValueError(
                "Comparison-suite receipt completed observation count is outside "
                "its declared work range."
            )
        if (
            self.status is ComparisonSuiteRunStatus.RUNNING
            and self.finished_at_epoch_seconds is not None
        ):
            raise ValueError("A running comparison-suite receipt cannot be finished.")
        if (
            self.status is not ComparisonSuiteRunStatus.RUNNING
            and self.finished_at_epoch_seconds is None
        ):
            raise ValueError("A terminal comparison-suite receipt must be finished.")

    @classmethod
    def from_declaration(
        cls,
        declaration: ComparisonSuiteRunDeclaration,
        *,
        status: ComparisonSuiteRunStatus,
        completed_observation_count: int,
        updated_at_epoch_seconds: float,
    ) -> Self:
        """Create a lifecycle checkpoint by deriving all shared declaration fields."""

        declaration_values = {
            declared_field.name: getattr(declaration, declared_field.name)
            for declared_field in fields(ComparisonSuiteRunDeclaration)
        }
        return cls(
            **declaration_values,
            schema_version=COMPARISON_SUITE_RUN_RECEIPT_SCHEMA_VERSION,
            status=status,
            completed_observation_count=completed_observation_count,
            updated_at_epoch_seconds=updated_at_epoch_seconds,
            finished_at_epoch_seconds=(
                updated_at_epoch_seconds
                if status is not ComparisonSuiteRunStatus.RUNNING
                else None
            ),
            python=sys.version,
            platform=platform.platform(),
            processor=platform.processor(),
        )

    @classmethod
    def read(cls, path: Path) -> Self:
        """Parse and validate one receipt through its declared dataclass fields."""

        payload = json.loads(path.read_text(encoding="utf-8"))
        if not isinstance(payload, Mapping):
            raise TypeError(f"Comparison-suite receipt must be an object: {path}")
        return dataclass_from_mapping(cls, payload)

    def write(self, path: Path) -> None:
        """Atomically serialize this receipt through OpenHCS JSON projection."""

        contents = self._json_contents()
        path.parent.mkdir(parents=True, exist_ok=True)
        pending_path = path.with_name(f".{path.name}.pending")
        pending_path.write_text(contents, encoding="utf-8")
        pending_path.replace(path)

    def write_new(self, path: Path) -> None:
        """Exclusively claim one run directory with its first typed receipt."""

        path.parent.mkdir(parents=True, exist_ok=True)
        pending_path: Path | None = None
        try:
            with tempfile.NamedTemporaryFile(
                mode="w",
                encoding="utf-8",
                dir=path.parent,
                prefix=f".{path.name}.",
                suffix=".pending",
                delete=False,
            ) as pending:
                pending_path = Path(pending.name)
                pending.write(self._json_contents())
                pending.flush()
                os.fsync(pending.fileno())
            os.link(pending_path, path)
        finally:
            if pending_path is not None:
                pending_path.unlink(missing_ok=True)

    def _json_contents(self) -> str:
        payload = to_jsonable(self)
        if not isinstance(payload, Mapping):
            raise TypeError("Comparison-suite receipt projection must be an object.")
        return json.dumps(payload, indent=2, sort_keys=True)
