"""Native reuse preserves original partitions, clocks and physical custody."""

import json
from dataclasses import asdict
from pathlib import Path

import pytest

from benchmark.matched_cellprofiler_batch import (
    _concurrent_timing,
    _native_reference_inventory,
    _native_shard_requests,
    _require_native_reference_unchanged,
    _validate_native_shard_reports,
)
from benchmark.native_batch_contracts import (
    NativeBatchEnvironment,
    NativeBatchObservation,
    NativeBatchReport,
    NativeBatchRequest,
)


@pytest.fixture
def native_runs(tmp_path: Path):
    environment = NativeBatchEnvironment(
        "native-python",
        "3.9",
        "4.2",
        "4.2",
        "1.24",
        "1.9",
        str(tmp_path / "scratch"),
        tmp_path.stat().st_dev,
        "machine",
        "host",
        "Linux",
        "cpu-sha",
        (4, 5),
    )

    def report_for(request, index):
        observations = []
        for repetition in (-1, 0):
            run_root = Path(request.output_root) / str(repetition)
            counts = tuple(
                (directory, 1) for directory in request.assignment_output_subdirectories
            )
            for directory, _ in counts:
                output = run_root / directory / "output.txt"
                output.parent.mkdir(parents=True)
                output.write_text("declared output")
            invocation = 10.0 + 30 * (repetition + 1) + index * 0.1
            started, completed = invocation + 0.1, invocation + 2.0
            observations.append(
                NativeBatchObservation(
                    repetition,
                    str(run_root),
                    len(counts),
                    completed - invocation,
                    started - invocation,
                    completed - started,
                    invocation,
                    started,
                    completed,
                    counts,
                )
            )
        return NativeBatchReport(1.0, environment, request, tuple(observations))

    request = NativeBatchRequest(
        "pipeline.cppipe",
        "inputs",
        str(tmp_path / "native"),
        None,
        1,
        report_path=str(tmp_path / "native_report.json"),
        assignment_output_subdirectories=("W001", "W002"),
    )
    whole = report_for(request, 0)
    Path(request.report_path).write_text(json.dumps(asdict(whole)))
    reports = []
    for index, shard_request in enumerate(_native_shard_requests(whole, 2)):
        report = report_for(shard_request, index)
        payload = json.loads(json.dumps(asdict(report)))
        reports.append(payload)
        Path(shard_request.report_path).write_text(json.dumps(payload))
        Path(shard_request.report_path).with_name(f"request_{index}.json").write_text(
            json.dumps(asdict(shard_request))
        )
        barrier = Path(shard_request.start_barrier_root)
        barrier.mkdir(exist_ok=True)
        (barrier / f"repetition_0_job_{index}.ready").touch()
    (tmp_path / "native_shards/reports.json").write_text(json.dumps(reports))
    return whole, tuple(reports)


def test_original_partitions_and_simultaneous_clocks_are_admitted(native_runs):
    whole, reports = native_runs
    files = _validate_native_shard_reports(whole, reports, 2)
    assert len(files) == 6
    assert _concurrent_timing(reports, 0)[
        "pipeline_execution_makespan_seconds"
    ] == pytest.approx(2.0)


@pytest.mark.parametrize(
    "field,value",
    [
        ("start_barrier_job_index", 1),
        ("first_image_set", 2),
        ("expected_image_sets", 2),
        ("assignment_output_subdirectories", ["W002"]),
    ],
)
def test_shard_request_cannot_change_partition_or_barrier(native_runs, field, value):
    whole, reports = native_runs
    reports[0]["request"][field] = value
    with pytest.raises(RuntimeError):
        _validate_native_shard_reports(whole, reports, 2)


def test_original_request_and_worker_report_must_agree(native_runs):
    whole, reports = native_runs
    report_path = Path(reports[0]["request"]["report_path"])
    request_path = report_path.with_name("request_0.json")
    payload = json.loads(request_path.read_text())
    payload["last_image_set"] = 2
    request_path.write_text(json.dumps(payload))
    with pytest.raises(RuntimeError, match="original partition/request/report"):
        _validate_native_shard_reports(whole, reports, 2)


def test_missing_barrier_member_rejects_reuse(native_runs):
    whole, reports = native_runs
    root = Path(reports[0]["request"]["start_barrier_root"])
    (root / "repetition_0_job_1.ready").unlink()
    with pytest.raises(RuntimeError, match="barrier membership"):
        _validate_native_shard_reports(whole, reports, 2)


def test_nonadditive_clocks_reject_reuse(native_runs):
    whole, reports = native_runs
    reports[0]["observations"][0]["invocation_seconds"] += 0.5
    with pytest.raises(RuntimeError, match="duration disagrees"):
        _validate_native_shard_reports(whole, reports, 2)


def test_affinity_is_a_physical_environment_guard(native_runs):
    whole, reports = native_runs
    reports[0]["environment"]["cpu_affinity"] = [3]
    Path(reports[0]["request"]["report_path"]).write_text(json.dumps(reports[0]))
    with pytest.raises(RuntimeError, match="declared environment"):
        _validate_native_shard_reports(whole, reports, 2)


@pytest.mark.parametrize("change", ["add-output", "change-report", "add-marker"])
def test_shard_custody_is_rechecked_after_candidate_execution(native_runs, change):
    whole, reports = native_runs
    files = _validate_native_shard_reports(whole, reports, 2)
    files |= frozenset(
        (
            Path(whole.request.report_path),
            Path(whole.request.output_root).parent / "native_shards/reports.json",
        )
    )
    files |= frozenset(
        path
        for payload in (asdict(whole), *reports)
        for row in payload["observations"]
        for path in Path(row["output_root"]).rglob("*")
        if path.is_file()
    )
    provenance = {
        "native_job_count": 2,
        "native_reference_report_path": whole.request.report_path,
        "native_reference_file_inventory": _native_reference_inventory(files),
    }
    if change == "add-output":
        (
            Path(reports[0]["observations"][0]["output_root"]) / "unexpected.txt"
        ).write_text("extra")
    elif change == "change-report":
        Path(reports[0]["request"]["report_path"]).write_text("{}")
    else:
        (Path(reports[0]["request"]["start_barrier_root"]) / "unexpected.ready").touch()
    with pytest.raises(RuntimeError, match="reference files changed"):
        _require_native_reference_unchanged(provenance)
