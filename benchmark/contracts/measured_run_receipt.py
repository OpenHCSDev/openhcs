"""Completed evidence for measuring one ordinary OpenHCS pipeline execution."""

from __future__ import annotations

import json
import re
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import Self

from python_introspect import dataclass_from_mapping

from benchmark.timing import PhaseTimingRecord
from openhcs.serialization.json import to_jsonable

MEASURED_PIPELINE_RUN_RECEIPT_SCHEMA_VERSION = "openhcs.benchmark.measured-pipeline.v1"
_SHA256_HEX = re.compile(r"[0-9a-f]{64}\Z")


@dataclass(frozen=True, slots=True)
class MeasuredEndpointProvenance:
    """Endpoint identity observed by the ordinary client during one run."""

    client_python_executable: str
    client_openhcs_file: str
    client_openhcs_version: str
    endpoint_application_identifier: str | None
    endpoint_openhcs_version: str
    endpoint_pid: int | None
    endpoint_create_time_epoch_seconds: float | None
    endpoint_log_file_path: str | None
    endpoint_port: int

    def as_payload(self) -> dict[str, object]:
        payload = to_jsonable(self)
        if not isinstance(payload, dict):
            raise TypeError("Endpoint provenance must project to a JSON object.")
        return payload


@dataclass(frozen=True, slots=True)
class MeasuredPipelineRunReceipt:
    """Success receipt; runtime job status remains with the execution service."""

    schema_version: str
    run_id: str
    pipeline_name: str
    plate_id: str
    execution_plate_id: str | None
    selected_pipeline_path: str | None
    execution_id: str
    pipeline_source_sha256: str
    global_config_source_sha256: str
    observation_export_path: Path
    results_summary_path: Path
    output_roots: tuple[Path, ...]
    phase_timings: tuple[PhaseTimingRecord, ...]
    endpoint_provenance: MeasuredEndpointProvenance
    completed_at_epoch_seconds: float
    compile_artifact_id: str | None = None

    def __post_init__(self) -> None:
        if self.schema_version != MEASURED_PIPELINE_RUN_RECEIPT_SCHEMA_VERSION:
            raise ValueError(
                f"Unsupported measured pipeline receipt schema: {self.schema_version!r}."
            )
        if not self.run_id or not self.execution_id or not self.plate_id:
            raise ValueError(
                "Measured run, execution, and plate identities are required."
            )
        for digest in (
            self.pipeline_source_sha256,
            self.global_config_source_sha256,
        ):
            if _SHA256_HEX.fullmatch(digest) is None:
                raise ValueError(
                    "Measured pipeline source digests must be SHA-256 hex."
                )
        if self.completed_at_epoch_seconds <= 0:
            raise ValueError("Completion time must be a positive epoch timestamp.")
        if self.compile_artifact_id == "":
            raise ValueError("Compile artifact id cannot be empty when declared.")

    @classmethod
    def read(cls, path: Path) -> Self:
        payload = json.loads(Path(path).read_text(encoding="utf-8"))
        if not isinstance(payload, Mapping):
            raise TypeError(f"Measured pipeline receipt must be an object: {path}")
        timing_payloads = payload.get("phase_timings")
        if not isinstance(timing_payloads, list) or not all(
            isinstance(record, Mapping) for record in timing_payloads
        ):
            raise TypeError(
                "Measured pipeline phase timings must be a list of objects."
            )
        return dataclass_from_mapping(
            cls,
            {
                **payload,
                "phase_timings": tuple(
                    PhaseTimingRecord.from_payload(record) for record in timing_payloads
                ),
            },
        )

    def write(self, path: Path) -> None:
        """Atomically retain a completed receipt after observation validation."""

        payload = to_jsonable(self)
        if not isinstance(payload, dict):
            raise TypeError("Measured pipeline receipt must project to a JSON object.")
        payload["phase_timings"] = [
            record.as_payload() for record in self.phase_timings
        ]
        target = Path(path)
        target.parent.mkdir(parents=True, exist_ok=True)
        pending = target.with_name(f".{target.name}.pending")
        pending.write_text(
            json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8"
        )
        pending.replace(target)
