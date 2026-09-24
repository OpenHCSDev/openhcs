"""Read-only benchmark run-inspection control surface."""

from __future__ import annotations

import hashlib
import json
import os
from collections import defaultdict
from collections.abc import Mapping
from dataclasses import fields
from pathlib import Path
from statistics import median

from benchmark.contracts.control import (
    BenchmarkCaseCatalog,
    BenchmarkCaseSummary,
    BenchmarkRunInspection,
    BenchmarkRunInspectionRequest,
    BenchmarkRunReport,
    BenchmarkStructuredArtifact,
    MeasuredPipelineRunInspection,
    MeasuredPipelineRunReport,
    MeasuredSourceEvidence,
)
from benchmark.contracts.measured_run_receipt import MeasuredPipelineRunReceipt
from benchmark.contracts.run_artifacts import (
    ComparisonRunArtifact,
    MeasuredPipelineRunArtifact,
    StructuredArtifactFormat,
)
from benchmark.contracts.run_receipt import ComparisonSuiteRunReceipt
from benchmark.file_digest import sha256_file

BENCHMARK_CONTROL_SCHEMA_VERSION = "openhcs.benchmark.control.v1"
MEASURED_PIPELINE_INSPECTION_SCHEMA_VERSION = "openhcs.benchmark.measured-inspection.v3"
MAX_MEASURED_RECEIPT_BYTES = 1_000_000
MAX_COMPARISON_RECEIPT_BYTES = 1_000_000
MAX_SOURCE_SNAPSHOT_BYTES = 2_000_000
MAX_REPORT_OBSERVATION_FILE_BYTES = 20_000_000
MAX_REPORT_OBSERVATIONS = 2_048
MAX_REPORT_CASES = 128
MAX_REPORT_WARNINGS = 32
MAX_REPORT_WARNING_CHARS = 256
BENCHMARK_CASE_CATALOG_SCHEMA_VERSION = "openhcs.benchmark.case-catalog.v1"


def discover_benchmark_cases(
    manifest_path: Path,
    *,
    requested_names: tuple[str, ...] = (),
) -> BenchmarkCaseCatalog:
    """Project one manifest's work without acquiring data or launching jobs."""

    from benchmark.cellprofiler_comparison import (
        load_comparison_cases,
        select_comparison_cases,
    )

    path = Path(manifest_path).resolve()
    if not path.is_file():
        raise ValueError(f"Benchmark manifest must be a file: {path}")
    cases = select_comparison_cases(
        load_comparison_cases(path, materialize_roots=False),
        requested_names,
    )
    summaries = tuple(
        BenchmarkCaseSummary(
            name=case.name,
            dataset_id=case.resolved_dataset_id,
            dataset_path=str(case.dataset_path.resolve()),
            cppipe_path=str(case.cppipe_path.resolve()),
            dataset_present=case.dataset_path.exists(),
            cppipe_present=case.cppipe_path.is_file(),
            microscope_type=case.microscope_type,
        )
        for case in cases
    )
    warnings = tuple(
        f"Case {case.name!r} has an unavailable dataset or .cppipe source."
        for case in summaries
        if not case.dataset_present or not case.cppipe_present
    )
    return BenchmarkCaseCatalog(
        schema_version=BENCHMARK_CASE_CATALOG_SCHEMA_VERSION,
        manifest_path=str(path),
        cases=summaries,
        warnings=warnings,
    )


def _contained_file(root: Path, candidate: Path) -> Path | None:
    """Resolve a receipt path without allowing it to escape the selected run."""

    try:
        resolved = candidate.resolve(strict=False)
        return (
            resolved if resolved.is_relative_to(root) and resolved.is_file() else None
        )
    except (OSError, RuntimeError):
        return None


def _verify_retained_digest(
    file: Path | None,
    expected: str | None,
    label: str,
    warnings: list[str],
) -> bool:
    """Verify a receipt-declared artifact without promoting a legacy receipt."""

    if file is None:
        return False
    if expected is None:
        warnings.append(
            f"Archived receipt has no {label} digest; integrity is unverified."
        )
        return False
    try:
        verified = sha256_file(file) == expected
    except OSError as exc:
        warnings.append(f"Declared {label} could not be hashed: {exc}")
        return False
    if not verified:
        warnings.append(f"Declared {label} digest differs.")
    return verified


def inspect_measured_pipeline_run(output_dir: Path) -> MeasuredPipelineRunInspection:
    """Verify retained receipt/source/job evidence, not the pipeline's output files."""

    root = Path(output_dir).resolve()
    if not root.is_dir():
        raise ValueError(f"Measured pipeline output path must be a directory: {root}")
    warnings: list[str] = []
    receipt_path = MeasuredPipelineRunArtifact.RECEIPT.path_in(root)
    retained_receipt = _contained_file(root, receipt_path)
    receipt: MeasuredPipelineRunReceipt | None = None
    if retained_receipt is None:
        warnings.append("Measured pipeline success receipt is absent.")
    elif retained_receipt.stat().st_size > MAX_MEASURED_RECEIPT_BYTES:
        warnings.append("Measured pipeline receipt exceeds the inspection size limit.")
    else:
        try:
            receipt = MeasuredPipelineRunReceipt.read(retained_receipt)
        except (TypeError, ValueError, KeyError, AttributeError, OSError) as exc:
            warnings.append(f"Measured pipeline receipt is invalid: {exc}")

    unreceipted_artifacts = (
        tuple(
            artifact
            for artifact in MeasuredPipelineRunArtifact
            if artifact.finalizer_output
            and artifact is not MeasuredPipelineRunArtifact.RECEIPT
            and _contained_file(root, artifact.path_in(root)) is not None
        )
        if receipt is None
        else ()
    )
    if unreceipted_artifacts:
        names = ", ".join(artifact.value for artifact in unreceipted_artifacts)
        warnings.append(
            f"Finaliser artifacts exist without a valid success receipt: {names}."
        )

    source_evidence: list[MeasuredSourceEvidence] = []
    observation_present = False
    results_summary_present = False
    observation_integrity_verified = False
    results_summary_integrity_verified = False
    if receipt is not None:
        for artifact, expected in (
            (
                MeasuredPipelineRunArtifact.PIPELINE_SOURCE,
                receipt.pipeline_source_sha256,
            ),
            (
                MeasuredPipelineRunArtifact.GLOBAL_CONFIG_SOURCE,
                receipt.global_config_source_sha256,
            ),
        ):
            path = artifact.path_in(root)
            source_file = _contained_file(root, path)
            actual = None
            if source_file is None:
                warnings.append(
                    f"Declared source snapshot is absent or escapes the run: {path.name}"
                )
            elif source_file.stat().st_size > MAX_SOURCE_SNAPSHOT_BYTES:
                warnings.append(
                    f"Declared source snapshot exceeds the inspection size limit: {path.name}"
                )
            else:
                actual = hashlib.sha256(source_file.read_bytes()).hexdigest()
                if actual != expected:
                    warnings.append(
                        f"Declared source snapshot digest differs: {path.name}"
                    )
            source_evidence.append(
                MeasuredSourceEvidence(
                    artifact=artifact,
                    path=str(path),
                    expected_sha256=expected,
                    actual_sha256=actual,
                    valid=actual == expected,
                )
            )
        observation_file = _contained_file(root, receipt.observation_export_path)
        summary_file = _contained_file(root, receipt.results_summary_path)
        observation_present = observation_file is not None
        results_summary_present = summary_file is not None
        if not observation_present:
            warnings.append(
                "Declared runtime observation is absent or escapes the run."
            )
        if not results_summary_present:
            warnings.append("Declared execution summary is absent or escapes the run.")
        observation_integrity_verified = _verify_retained_digest(
            observation_file,
            receipt.observation_export_sha256,
            "runtime observation",
            warnings,
        )
        results_summary_integrity_verified = _verify_retained_digest(
            summary_file,
            receipt.results_summary_sha256,
            "execution summary",
            warnings,
        )

    return MeasuredPipelineRunInspection(
        schema_version=MEASURED_PIPELINE_INSPECTION_SCHEMA_VERSION,
        output_dir=str(root),
        receipt=receipt,
        unreceipted_artifacts=unreceipted_artifacts,
        source_evidence=tuple(source_evidence),
        observation_present=observation_present,
        results_summary_present=results_summary_present,
        observation_integrity_verified=observation_integrity_verified,
        results_summary_integrity_verified=results_summary_integrity_verified,
        retained_evidence_valid=(
            receipt is not None
            and all(item.valid for item in source_evidence)
            and observation_integrity_verified
            and results_summary_integrity_verified
            and not warnings
        ),
        warnings=tuple(warnings),
    )


def report_measured_pipeline_run(
    inspection: MeasuredPipelineRunInspection,
) -> MeasuredPipelineRunReport:
    """Render the bounded inspection as a report, without a second data loader."""

    receipt = inspection.receipt
    lines = ["# Measured OpenHCS pipeline run", ""]
    if receipt is None:
        lines.append("No valid completed-run receipt is available.")
    else:
        lines.extend(
            (
                "- Retained source, observation, and summary evidence: "
                + (
                    "verified"
                    if inspection.retained_evidence_valid
                    else "unverified or invalid"
                ),
                f"- Run: `{receipt.run_id}`",
                f"- Pipeline: `{receipt.pipeline_name}`",
                f"- Execution: `{receipt.execution_id}`",
                f"- Plate: `{receipt.plate_id}`",
                f"- Compile artifact: `{receipt.compile_artifact_id or 'none; server job may include compilation'}`",
                f"- Output roots: {len(receipt.output_roots)}",
                "- Output files: not inspected; use output/equivalence evidence for output claims",
                f"- Runtime observation scope: `{receipt.observation_export_scope.value}`",
                f"- Execution axes: {receipt.observed_axis_count if receipt.observed_axis_count is not None else 'not recorded'}"
                + (
                    f" / {receipt.expected_axis_count} expected"
                    if receipt.expected_axis_count is not None
                    else ""
                ),
                f"- Runtime observation retained: {inspection.observation_present}",
                f"- Runtime observation digest verified: {inspection.observation_integrity_verified}",
                f"- Execution summary digest verified: {inspection.results_summary_integrity_verified}",
                f"- Source snapshots verified: {sum(item.valid for item in inspection.source_evidence)}/{len(inspection.source_evidence)}",
                "",
                "## Measured phases",
                "",
            )
        )
        lines.extend(
            f"- {record.phase.name}: {record.seconds:.6f} s"
            for record in receipt.phase_timings
        )
    if inspection.warnings:
        lines.extend(("", "## Evidence warnings", ""))
        lines.extend(f"- {warning}" for warning in inspection.warnings)
    return MeasuredPipelineRunReport(
        schema_version=inspection.schema_version,
        output_dir=inspection.output_dir,
        markdown="\n".join(lines) + "\n",
        warnings=inspection.warnings,
    )


def inspect_benchmark_run(
    request: BenchmarkRunInspectionRequest,
) -> BenchmarkRunInspection:
    """Inspect one comparison-run directory without executing benchmark code."""

    resolved_output_dir = Path(request.output_dir).resolve()
    if not resolved_output_dir.is_dir():
        raise ValueError(
            f"Benchmark output path must be a directory: {resolved_output_dir}"
        )
    metadata_path = ComparisonRunArtifact.SUITE_METADATA.path_in(resolved_output_dir)
    observation_path = ComparisonRunArtifact.OBSERVATIONS_JSONL.path_in(
        resolved_output_dir
    )
    warnings: list[str] = []

    receipt: ComparisonSuiteRunReceipt | None = None
    retained_metadata = _contained_file(resolved_output_dir, metadata_path)
    if retained_metadata is not None:
        if retained_metadata.stat().st_size > MAX_COMPARISON_RECEIPT_BYTES:
            warnings.append("suite_metadata.json exceeds the inspection size limit.")
        else:
            try:
                receipt = ComparisonSuiteRunReceipt.read(retained_metadata)
            except (TypeError, ValueError) as error:
                warnings.append(
                    "suite_metadata.json is not a current typed run receipt; lifecycle "
                    f"and rerun claims are unavailable: {error}"
                )
    else:
        warnings.append(
            "suite_metadata.json is absent or escapes the run; lifecycle and "
            "rerun data are unavailable."
        )

    retained_observations = _contained_file(resolved_output_dir, observation_path)
    completed_observation_count = _observation_count(retained_observations)
    if observation_path.exists() and retained_observations is None:
        warnings.append("observations.jsonl escapes the run; progress is unavailable.")
    recorded_count = (
        receipt.completed_observation_count if receipt is not None else None
    )
    if recorded_count is not None and recorded_count != completed_observation_count:
        warnings.append(
            "suite_metadata.json observation count differs from observations.jsonl; "
            "the append-only observation artifact is reported as progress authority."
        )

    expected_observation_count = (
        receipt.expected_observation_count if receipt is not None else None
    )
    structured_artifacts, next_artifact_offset = _structured_artifacts(
        resolved_output_dir,
        warnings,
        offset=request.artifact_offset,
        limit=request.artifact_limit,
    )
    return BenchmarkRunInspection(
        schema_version=BENCHMARK_CONTROL_SCHEMA_VERSION,
        output_dir=str(resolved_output_dir),
        suite_id=receipt.suite_id if receipt is not None else None,
        recorded_status=receipt.status if receipt is not None else None,
        completed_observation_count=completed_observation_count,
        expected_observation_count=expected_observation_count,
        progress_fraction=(
            completed_observation_count / expected_observation_count
            if expected_observation_count
            else None
        ),
        manifest_path=(
            str(receipt.manifest_path)
            if receipt is not None and receipt.manifest_path is not None
            else None
        ),
        case_names=receipt.case_names if receipt is not None else (),
        repeats=receipt.repeats if receipt is not None else None,
        rerun_command=receipt.rerun_command if receipt is not None else (),
        rerun_working_directory=(
            str(receipt.rerun_working_directory)
            if receipt is not None and receipt.rerun_working_directory is not None
            else None
        ),
        structured_artifacts=structured_artifacts,
        next_artifact_offset=next_artifact_offset,
        warnings=tuple(warnings),
    )


def report_benchmark_run(
    inspection: BenchmarkRunInspection,
) -> BenchmarkRunReport:
    """Summarize typed comparison observations under the inspected run receipt.

    This report does not infer an observed speedup from unmatched timing scopes.
    It reads only the declared JSONL artifact and caps both input and output.
    """

    from python_introspect import dataclass_from_mapping

    from benchmark.cellprofiler_comparison import CellProfilerComparisonObservation

    root = Path(inspection.output_dir).resolve()
    warnings = [
        warning[:MAX_REPORT_WARNING_CHARS]
        for warning in inspection.warnings[:MAX_REPORT_WARNINGS]
    ]

    def warn(message: str) -> None:
        if len(warnings) < MAX_REPORT_WARNINGS:
            warnings.append(message[:MAX_REPORT_WARNING_CHARS])
        elif warnings[-1] != "Additional evidence warnings omitted.":
            warnings[-1] = "Additional evidence warnings omitted."

    lines = [
        "# CellProfiler–OpenHCS comparison run",
        "",
        f"- Suite: {inspection.suite_id or 'unavailable'}",
        f"- Recorded status: {inspection.recorded_status.value if inspection.recorded_status else 'unavailable'}",
        f"- Observations: {inspection.completed_observation_count} / {inspection.expected_observation_count if inspection.expected_observation_count is not None else 'unknown'}",
        "",
    ]
    observation_path = _contained_file(
        root,
        ComparisonRunArtifact.OBSERVATIONS_JSONL.path_in(root),
    )
    observations_by_case: dict[str, list[CellProfilerComparisonObservation]] = (
        defaultdict(list)
    )
    if inspection.suite_id is None:
        warn("A typed suite receipt is required for observation reporting.")
    elif observation_path is None:
        warn("Declared observations.jsonl is absent or escapes the run.")
    elif observation_path.stat().st_size > MAX_REPORT_OBSERVATION_FILE_BYTES:
        warn("Declared observations.jsonl exceeds the report size limit.")
    else:
        declared_fields = frozenset(
            field.name for field in fields(CellProfilerComparisonObservation)
        )
        seen: set[tuple[str, int]] = set()
        with observation_path.open("r", encoding="utf-8") as handle:
            for line_number, line in enumerate(handle, start=1):
                if not line.strip():
                    continue
                if len(seen) >= MAX_REPORT_OBSERVATIONS:
                    warn("Observation report limit reached; case results are partial.")
                    break
                try:
                    payload = json.loads(line)
                    if not isinstance(payload, Mapping):
                        raise TypeError("observation must be a JSON object")
                    observation = dataclass_from_mapping(
                        CellProfilerComparisonObservation,
                        {
                            key: value
                            for key, value in payload.items()
                            if key in declared_fields
                        },
                    )
                except (TypeError, ValueError, KeyError, AttributeError) as exc:
                    warn(
                        f"Observation line {line_number} is invalid "
                        f"({type(exc).__name__})."
                    )
                    continue
                if observation.suite_id != inspection.suite_id:
                    warn(f"Observation line {line_number} has another suite identity.")
                    continue
                if observation.case_name not in inspection.case_names or not (
                    1 <= observation.repetition <= (inspection.repeats or 0)
                ):
                    warn(f"Observation line {line_number} is outside declared work.")
                    continue
                key = (observation.case_name, observation.repetition)
                if key in seen:
                    warn(f"Observation line {line_number} repeats declared work.")
                    continue
                seen.add(key)
                observations_by_case[observation.case_name].append(observation)

    if observations_by_case:
        lines.extend(
            (
                "## Recorded case outcomes",
                "",
                "| Case | Observed repeats | Both executions succeeded | Equivalent results | Native median (s) | OpenHCS median (s) |",
                "| --- | ---: | ---: | ---: | ---: | ---: |",
            )
        )
        for case_name in inspection.case_names[:MAX_REPORT_CASES]:
            case_observations = observations_by_case.get(case_name, ())
            if not case_observations:
                continue
            displayed_case_name = case_name.replace("|", "\\|").replace("\n", " ")
            native_times = tuple(
                item.native_cellprofiler.execution_seconds
                for item in case_observations
                if item.native_cellprofiler.success
                and item.native_cellprofiler.execution_seconds is not None
            )
            openhcs_times = tuple(
                item.openhcs.execution_seconds
                for item in case_observations
                if item.openhcs.success and item.openhcs.execution_seconds is not None
            )
            native_median = f"{median(native_times):.3f}" if native_times else "—"
            openhcs_median = f"{median(openhcs_times):.3f}" if openhcs_times else "—"
            lines.append(
                f"| {displayed_case_name} "
                f"| {len(case_observations)} "
                f"| {sum(item.native_cellprofiler.success and item.openhcs.success for item in case_observations)} "
                f"| {sum(item.equivalent for item in case_observations)} "
                f"| {native_median} | {openhcs_median} |"
            )
        if len(inspection.case_names) > MAX_REPORT_CASES:
            warn("Case table is truncated at the report case limit.")
        lines.extend(
            (
                "",
                "Recorded execution intervals are not, by themselves, a matched-concurrency performance claim.",
            )
        )
    else:
        lines.append("No validated comparison observations are available.")
    if warnings:
        lines.extend(("", "## Evidence warnings", ""))
        lines.extend(f"- {warning}" for warning in warnings)
    return BenchmarkRunReport(
        schema_version=inspection.schema_version,
        output_dir=inspection.output_dir,
        markdown="\n".join(lines) + "\n",
        warnings=tuple(warnings),
    )


def _observation_count(path: Path | None) -> int:
    if path is None:
        return 0
    with path.open("r", encoding="utf-8") as handle:
        return sum(1 for line in handle if line.strip())


def _structured_artifacts(
    output_dir: Path,
    warnings: list[str],
    *,
    offset: int,
    limit: int,
) -> tuple[tuple[BenchmarkStructuredArtifact, ...], int | None]:
    artifacts: list[BenchmarkStructuredArtifact] = []
    eligible_count = 0
    escaped_reported = False
    for directory, subdirectories, filenames in os.walk(output_dir, followlinks=False):
        subdirectories[:] = sorted(subdirectories)
        for filename in sorted(filenames):
            path = Path(directory) / filename
            format_ = StructuredArtifactFormat.from_path(path)
            if format_ is None:
                continue
            contained = _contained_file(output_dir, path)
            if contained is None:
                if not escaped_reported:
                    warnings.append("Structured artifact escapes the run.")
                    escaped_reported = True
                continue
            if eligible_count < offset:
                eligible_count += 1
                continue
            if len(artifacts) == limit:
                return tuple(artifacts), eligible_count
            declared_identity = (
                ComparisonRunArtifact.from_path(path)
                if path.parent == output_dir
                else None
            )
            artifacts.append(
                BenchmarkStructuredArtifact(
                    path=str(path),
                    relative_path=str(path.relative_to(output_dir)),
                    format=format_,
                    mime_type=format_.mime_type,
                    size_bytes=contained.stat().st_size,
                    declared_identity=declared_identity,
                )
            )
            eligible_count += 1
    return tuple(artifacts), None
