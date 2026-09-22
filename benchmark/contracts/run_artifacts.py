"""Declaration-owned comparison-run artifact identities."""

from __future__ import annotations

from enum import Enum
from pathlib import Path
from typing import Self


class ComparisonRunArtifact(Enum):
    """Stable structured artifacts emitted by a comparison suite run."""

    SUITE_METADATA = "suite_metadata.json"
    OBSERVATIONS_JSONL = "observations.jsonl"
    OBSERVATIONS_CSV = "observations.csv"
    PHASE_TIMING_CSV = "phase_timing.csv"
    SUMMARY_CSV = "summary.csv"
    MODULE_COVERAGE_SUMMARY = "module_coverage_summary.json"
    MODULE_COVERAGE_CPPIPE_MODULES = "module_coverage_cppipe_modules.csv"
    MODULE_COVERAGE_CPPIPE_SETTINGS = "module_coverage_cppipe_settings.csv"
    MODULE_COVERAGE_ABSORBED_MODULES = "module_coverage_absorbed_modules.csv"

    @classmethod
    def from_path(cls, path: Path) -> Self | None:
        """Return the declared identity for a direct run artifact, if any."""

        return next((artifact for artifact in cls if artifact.value == path.name), None)

    def path_in(self, output_dir: Path) -> Path:
        """Project this declared artifact identity into one run directory."""

        return output_dir / self.value


class MeasuredPipelineRunArtifact(Enum):
    """Evidence owned by a single measured ordinary pipeline execution."""

    RUNTIME_OBSERVATION = ("runtime_execution_server_observation.pkl", False)
    RESULTS_SUMMARY = ("zmq_results_summary.json", True)
    RECEIPT = ("measured_pipeline_receipt.json", True)
    PIPELINE_SOURCE = ("submitted_pipeline.py", True)
    GLOBAL_CONFIG_SOURCE = ("submitted_global_config.py", True)

    def __new__(cls, filename: str, finalizer_output: bool) -> Self:
        member = object.__new__(cls)
        member._value_ = filename
        member.finalizer_output = finalizer_output
        return member

    def path_in(self, output_dir: Path) -> Path:
        return output_dir / self.value


class StructuredArtifactFormat(Enum):
    """Closed structured-file format axis used by run inspection."""

    CSV = ("csv", ".csv", "text/csv")
    JSON = ("json", ".json", "application/json")
    JSON_LINES = ("jsonl", ".jsonl", "application/x-ndjson")

    def __new__(cls, value: str, suffix: str, mime_type: str) -> Self:
        member = object.__new__(cls)
        member._value_ = value
        member.suffix = suffix
        member.mime_type = mime_type
        return member

    @classmethod
    def from_path(cls, path: Path) -> Self | None:
        """Select the declared structured format for a path."""

        return next((format_ for format_ in cls if format_.suffix == path.suffix), None)
