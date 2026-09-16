"""Read-only benchmark run-inspection control surface."""

from __future__ import annotations

from pathlib import Path

from benchmark.contracts.control import (
    BenchmarkRunInspection,
    BenchmarkStructuredArtifact,
)
from benchmark.contracts.run_artifacts import (
    ComparisonRunArtifact,
    StructuredArtifactFormat,
)
from benchmark.contracts.run_receipt import ComparisonSuiteRunReceipt

BENCHMARK_CONTROL_SCHEMA_VERSION = "openhcs.benchmark.control.v1"


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
