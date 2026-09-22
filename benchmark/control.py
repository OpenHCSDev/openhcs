"""Read-only benchmark run-inspection control surface."""

from __future__ import annotations

import hashlib
from pathlib import Path

from benchmark.contracts.control import (
    BenchmarkCaseCatalog,
    BenchmarkCaseSummary,
    BenchmarkRunInspection,
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

BENCHMARK_CONTROL_SCHEMA_VERSION = "openhcs.benchmark.control.v1"
MEASURED_PIPELINE_INSPECTION_SCHEMA_VERSION = "openhcs.benchmark.measured-inspection.v1"
MAX_MEASURED_RECEIPT_BYTES = 1_000_000
MAX_SOURCE_SNAPSHOT_BYTES = 2_000_000
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


def inspect_measured_pipeline_run(output_dir: Path) -> MeasuredPipelineRunInspection:
    """Inspect one completed pipeline run without loading its pickle observation."""

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

    source_evidence: list[MeasuredSourceEvidence] = []
    observation_present = False
    results_summary_present = False
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
        observation_present = (
            _contained_file(root, receipt.observation_export_path) is not None
        )
        results_summary_present = (
            _contained_file(root, receipt.results_summary_path) is not None
        )
        if not observation_present:
            warnings.append(
                "Declared runtime observation is absent or escapes the run."
            )
        if not results_summary_present:
            warnings.append("Declared execution summary is absent or escapes the run.")

    return MeasuredPipelineRunInspection(
        schema_version=MEASURED_PIPELINE_INSPECTION_SCHEMA_VERSION,
        output_dir=str(root),
        receipt=receipt,
        source_evidence=tuple(source_evidence),
        observation_present=observation_present,
        results_summary_present=results_summary_present,
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
                f"- Run: `{receipt.run_id}`",
                f"- Pipeline: `{receipt.pipeline_name}`",
                f"- Execution: `{receipt.execution_id}`",
                f"- Plate: `{receipt.plate_id}`",
                f"- Output roots: {len(receipt.output_roots)}",
                f"- Runtime observation retained: {inspection.observation_present}",
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


def inspect_benchmark_run(output_dir: Path) -> BenchmarkRunInspection:
    """Inspect one comparison-run directory without executing benchmark code."""

    resolved_output_dir = Path(output_dir).resolve()
    metadata_path = ComparisonRunArtifact.SUITE_METADATA.path_in(resolved_output_dir)
    observation_path = ComparisonRunArtifact.OBSERVATIONS_JSONL.path_in(
        resolved_output_dir
    )
    warnings: list[str] = []

    receipt: ComparisonSuiteRunReceipt | None = None
    if metadata_path.is_file():
        try:
            receipt = ComparisonSuiteRunReceipt.read(metadata_path)
        except (TypeError, ValueError) as error:
            warnings.append(
                "suite_metadata.json is not a current typed run receipt; lifecycle "
                f"and rerun claims are unavailable: {error}"
            )
    else:
        warnings.append(
            "suite_metadata.json is absent; lifecycle and rerun data are unavailable."
        )

    completed_observation_count = _observation_count(observation_path)
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
        rerun_command=receipt.rerun_command if receipt is not None else (),
        rerun_working_directory=(
            str(receipt.rerun_working_directory)
            if receipt is not None and receipt.rerun_working_directory is not None
            else None
        ),
        structured_artifacts=_structured_artifacts(resolved_output_dir),
        warnings=tuple(warnings),
    )


def _observation_count(path: Path) -> int:
    if not path.is_file():
        return 0
    return sum(
        1 for line in path.read_text(encoding="utf-8").splitlines() if line.strip()
    )


def _structured_artifacts(
    output_dir: Path,
) -> tuple[BenchmarkStructuredArtifact, ...]:
    artifacts = []
    for path in sorted(output_dir.rglob("*")):
        if not path.is_file():
            continue
        format_ = StructuredArtifactFormat.from_path(path)
        if format_ is None:
            continue
        declared_identity = (
            ComparisonRunArtifact.from_path(path) if path.parent == output_dir else None
        )
        artifacts.append(
            BenchmarkStructuredArtifact(
                path=str(path),
                relative_path=str(path.relative_to(output_dir)),
                format=format_,
                mime_type=format_.mime_type,
                size_bytes=path.stat().st_size,
                declared_identity=declared_identity,
            )
        )
    return tuple(artifacts)
