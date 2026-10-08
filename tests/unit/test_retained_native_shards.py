"""Native reuse preserves original partitions, clocks and physical custody."""

import json
from dataclasses import asdict, replace
from pathlib import Path

import pytest

import benchmark.matched_cellprofiler_batch as matched_batch
from benchmark.adapters.cellprofiler import NativeCellProfilerSelectedSourceUniverse
from benchmark.matched_cellprofiler_batch import (
    _concurrent_timing,
    _native_reference_inventory,
    _native_shard_requests,
    _require_native_reference_unchanged,
    _reuse_native_projection_source,
    _validate_native_shard_reports,
)
from benchmark.native_execution_projection import RepeatedSourceNativeBatchReport
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
    "change",
    ("relocated", "changed-bytes", "changed-size", "changed-name", "retained-mutated"),
)
def test_retained_source_reuse_preserves_content_identity_across_staging(
    native_runs, tmp_path: Path, monkeypatch: pytest.MonkeyPatch, change: str
):
    whole, _ = native_runs
    original = tmp_path / "original-input" / "metadata.csv"
    current = tmp_path / "current-input" / "metadata.csv"
    for source in (original, current):
        source.parent.mkdir()
        source.write_bytes(b"Image,Well\nimage.tif,A01\n")
    pipeline = tmp_path / "pipeline.cppipe"
    pipeline.write_text("unchanged effective pipeline")
    worker = tmp_path / "native_worker.py"
    worker.write_text("native worker source")
    worker.with_name("native_batch_contracts.py").write_text("native contract source")
    whole = replace(
        whole,
        request=replace(
            whole.request, pipeline_path=str(pipeline), input_dir=str(original.parent)
        ),
    )
    report = json.loads(json.dumps(asdict(whole)))
    Path(whole.request.report_path).write_text(json.dumps(report))
    (tmp_path / "native_request.json").write_text(json.dumps(asdict(whole.request)))
    origin = {
        "case": "selected-metadata",
        "wells": ["W001", "W002"],
        "selected_source_wells": ["A01"],
        "assignment_scope": "independent repeated source assignments",
        "cppipe_sha256": matched_batch.sha256_file(pipeline),
        "native_worker_sha256": matched_batch.sha256_file(worker),
        "native_contract_sha256": matched_batch.sha256_file(
            worker.with_name("native_batch_contracts.py")
        ),
        "native_job_count": 1,
        "thread_environment": {"OMP_NUM_THREADS": "1"},
        "native_image_set_count": 2,
        "source_commit": "retained-source",
        "native_input_inventory": json.loads(
            json.dumps(
                matched_batch._source_input_inventory(
                    NativeCellProfilerSelectedSourceUniverse((original,))
                )
            )
        ),
    }
    (tmp_path / "pilot_provenance.json").write_text(json.dumps(origin))
    if change == "changed-bytes":
        current.write_bytes(current.read_bytes().replace(b"A01", b"A02"))
    elif change == "changed-size":
        current.write_bytes(current.read_bytes() + b"extra")
    elif change == "changed-name":
        current = current.rename(current.with_name("other.csv"))
    elif change == "retained-mutated":
        original.write_bytes(original.read_bytes().replace(b"A01", b"A02"))
    provenance = {
        **origin,
        "native_input_inventory": matched_batch._source_input_inventory(
            NativeCellProfilerSelectedSourceUniverse((current,))
        ),
    }
    monkeypatch.setattr(
        matched_batch, "_probe_native_environment", lambda *_: whole.environment
    )

    def reuse():
        return matched_batch._reuse_native_report(
            tmp_path,
            native_payload=asdict(
                replace(whole.request, input_dir=str(current.parent))
            ),
            native_python=Path("native-python"),
            native_worker=worker,
            provenance=provenance,
        )

    if change != "relocated":
        with pytest.raises(RuntimeError, match="source images or metadata differ"):
            reuse()
        return
    assert reuse() == report
    assert origin["native_input_inventory"][0]["source_path"] == str(original)
    assert provenance["native_input_inventory"][0]["source_path"] == str(current)
    assert provenance["native_reference_report_sha256"] == matched_batch.sha256_file(
        tmp_path / "native_report.json"
    )


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


def test_projection_view_preserves_genuine_clocks_and_maps_every_target(native_runs):
    whole, _ = native_runs
    payload = asdict(whole)
    view = RepeatedSourceNativeBatchReport.from_payload(payload)
    assert asdict(view) == payload
    assert view.comparison_directories(5) == ("W001", "W002", "W001", "W002", "W001")
    declaration = view.projection_inputs(
        5,
        source_report_path=Path(whole.request.report_path),
        source_report_sha256="sha",
    )
    assert declaration["status"] == "model_pending"
    assert declaration["source_assignment_count"] == 2
    assert declaration["target_assignment_count"] == 5
    assert tuple(
        row["repetition"] for row in declaration["observed_reference_inputs"]
    ) == (-1, 0)
    assert whole.observations == view.observations
    assert "projected_execution_seconds" not in declaration


def test_projection_validation_derives_actual_source_cardinality_only(native_runs):
    whole, _ = native_runs
    view = RepeatedSourceNativeBatchReport.from_payload(asdict(whole))
    target = replace(
        whole.request,
        expected_image_sets=6,
        assignment_output_subdirectories=("W001", "W002", "W003"),
        output_root="new-candidate-reference",
    )
    admitted = view.validation_request(target, 3)
    assert admitted == replace(
        target,
        expected_image_sets=4,
        assignment_output_subdirectories=whole.request.assignment_output_subdirectories,
    )
    with pytest.raises(RuntimeError, match="equal assignments"):
        view.validation_request(replace(target, expected_image_sets=5), 3)


@pytest.mark.parametrize(
    "change", ("missing-observation", "unequal-domain", "bad-clock")
)
def test_projection_cannot_admit_incomplete_or_changed_native_evidence(
    native_runs, change
):
    whole, _ = native_runs
    payload = json.loads(json.dumps(asdict(whole)))
    if change == "missing-observation":
        payload["observations"].pop()
    elif change == "unequal-domain":
        payload["observations"][0]["assignment_image_set_counts"][0][1] = 2
        payload["observations"][0]["image_set_count"] = 3
    else:
        payload["observations"][0]["pipeline_execution_seconds"] += 1
    view = RepeatedSourceNativeBatchReport.from_payload(payload)
    with pytest.raises(RuntimeError):
        view.comparison_directories(3)


def test_fresh_projection_counts_actual_first_execution_and_preparation_once(
    native_runs,
):
    whole, _ = native_runs
    view = RepeatedSourceNativeBatchReport.from_payload(asdict(whole))
    declaration = view.projected_fresh_batch(
        5,
        source_report_path=Path(whole.request.report_path),
        source_report_sha256="sha",
    )
    first, warm = whole.observations
    expected = (
        first.pipeline_execution_seconds + 3 * warm.pipeline_execution_seconds / 2
    )
    assert declaration["projected_fresh_batch_execution_seconds"] == expected
    assert (
        declaration["projected_fresh_batch_prepared_invocation_seconds"]
        == expected + first.pre_pipeline_seconds
    )
    assert declaration["source_fresh_observation_count"] == 1
    assert declaration["source_warm_repetitions"] == (0,)
    assert declaration["target_native_observation_count"] == 0
    assert declaration["status"] == "projected"
    assert asdict(view) == asdict(whole)


def test_projection_reuse_preserves_strict_guard_fields(native_runs, monkeypatch):
    whole, _ = native_runs
    target = replace(
        whole.request,
        assignment_output_subdirectories=("W001", "W002", "W003"),
    )
    provenance = {
        "selected_source_wells": ("source-1",),
        "assignment_scope": "independent repeated source assignments",
        "native_job_count": 1,
        "wells": ("W001", "W002", "W003"),
        "thread_environment": {"OMP_NUM_THREADS": "unexpected-value"},
        "native_input_inventory": ("unchanged-input-authority",),
    }

    def reject_changed_environment(reference_case, **kwargs):
        planned = NativeBatchRequest(**kwargs["native_payload"])
        assert planned.assignment_output_subdirectories == ("W001", "W002")
        assert kwargs["provenance"] == {**provenance, "wells": ("W001", "W002")}
        raise RuntimeError("Retained native reference differs in thread_environment.")

    monkeypatch.setattr(
        "benchmark.matched_cellprofiler_batch._reuse_native_report",
        reject_changed_environment,
    )
    with pytest.raises(RuntimeError, match="thread_environment"):
        _reuse_native_projection_source(
            Path(whole.request.report_path).parent,
            native_payload=asdict(target),
            native_python=Path("native-python"),
            native_worker=Path("native-worker"),
            provenance=provenance,
        )
    assert provenance["wells"] == ("W001", "W002", "W003")
