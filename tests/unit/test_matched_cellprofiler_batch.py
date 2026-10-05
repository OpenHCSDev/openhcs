"""The matched pilot preserves interpreter and output evidence identities."""

import hashlib
import json
from dataclasses import replace
from pathlib import Path
from subprocess import CompletedProcess

import pytest
from objectstate.context_manager import config_context
from objectstate.global_config import GlobalContextValues

import benchmark.matched_cellprofiler_batch as matched_batch
from benchmark.matched_cellprofiler_batch import (
    _candidate_pipeline_config,
    _global_config,
    _invoke_native_worker,
    _native_python_executable,
    _output_inventory,
    _parser,
    _select_genuine_wells,
    _source_input_inventory,
    _worker_axis_evidence,
)
from openhcs.core.config import (
    GlobalPipelineConfig,
    MultiprocessingStartMethod,
    PipelineConfig,
)
from openhcs.core.progress.types import ProgressEvent
from openhcs.core.runtime_exports import RuntimeExportObservation
from openhcs.core.runtime_equivalence import (
    RuntimeMeasurementSnapshot,
    RuntimeOutputSnapshot,
    RuntimeTableSnapshot,
    runtime_measurement_equivalence,
)


@pytest.fixture(autouse=True)
def restore_benchmark_global_context():
    """Restore both saved and live projections changed by config rebuilding."""
    previous = GlobalContextValues.capture(GlobalPipelineConfig)
    yield
    previous.apply()


@pytest.mark.parametrize("extra", (None, "Experiment.csv", "plate_Experiment.csv"))
def test_matched_inventory_accepts_csv_and_only_engine_receipt_asymmetry(
    tmp_path: Path,
    extra: str | None,
) -> None:
    roots = (tmp_path / "native", tmp_path / "candidate")
    for root in roots:
        root.mkdir()
        (root / "plate_Image.csv").write_text("ImageNumber,Count_Cells\n1,2\n")
    if extra is not None:
        (roots[0] / extra).write_text("Key,Value\nCellProfiler_Version,4.2.8.1\n")
    exports = tuple(RuntimeExportObservation.from_output_root(root) for root in roots)
    snapshots = tuple(
        RuntimeOutputSnapshot.from_export_observation(item) for item in exports
    )

    matched_batch._require_compared_output_inventory(
        reference_files=frozenset(roots[0].iterdir()),
        candidate_files=frozenset(roots[1].iterdir()),
        reference_exports=exports[0],
        candidate_exports=exports[1],
        reference_snapshot=snapshots[0],
        candidate_snapshot=snapshots[1],
    )


@pytest.mark.parametrize(
    "contents, message",
    (
        ({"unexpected.txt": "data"}, "without a value comparison"),
        ({"Empty.csv": ""}, "without a value comparison"),
        (
            {"Cells.csv": "ImageNumber,ObjectNumber,AreaShape_Area\n1,1,5\n"},
            "counts differ",
        ),
        ({"Experiment.csv": "ImageNumber,Count_Cells\n1,2\n"}, "counts differ"),
        ({"Receipt.csv": "Key,Value\nVersion,1\n"}, "counts differ"),
    ),
)
def test_matched_inventory_rejects_uncompared_and_extra_scientific_files(
    tmp_path: Path,
    contents: dict[str, str],
    message: str,
) -> None:
    roots = (tmp_path / "native", tmp_path / "candidate")
    for root in roots:
        root.mkdir()
        (root / "Image.csv").write_text("ImageNumber,Count_Cells\n1,2\n")
    for name, text in contents.items():
        (roots[1] / name).write_text(text)
    exports = tuple(RuntimeExportObservation.from_output_root(root) for root in roots)
    snapshots = tuple(
        RuntimeOutputSnapshot.from_export_observation(item) for item in exports
    )
    with pytest.raises(RuntimeError, match=message):
        matched_batch._require_compared_output_inventory(
            reference_files=frozenset(roots[0].iterdir()),
            candidate_files=frozenset(roots[1].iterdir()),
            reference_exports=exports[0],
            candidate_exports=exports[1],
            reference_snapshot=snapshots[0],
            candidate_snapshot=snapshots[1],
        )


@pytest.mark.parametrize(
    "path, header, expected",
    (
        ("Experiment.csv", ("Key", "Value"), True),
        ("Experiment.csv", ("Value", "Key"), True),
        ("Receipt.csv", ("Key", "Value"), False),
        ("Experiment.csv", ("ImageNumber", "Count_Cells"), False),
        ("Experiment.csv", ("Key", "Value", "Measurement"), False),
    ),
)
def test_engine_metadata_classification_preserves_scientific_tables(
    path: str,
    header: tuple[str, ...],
    expected: bool,
) -> None:
    assert RuntimeTableSnapshot(Path(path), header, ()).participates_in_comparison is (
        not expected
    )


@pytest.mark.parametrize(
    "candidate, equivalent",
    (
        (
            "ImageNumber,ObjectNumber,AreaShape_Area,Metadata_Plate\n1,1,5.0000001,plate\n",
            True,
        ),
        (
            "ImageNumber,ObjectNumber,AreaShape_Area,Metadata_Plate\n1,1,6,plate\n",
            False,
        ),
        ("ImageNumber,ObjectNumber,Metadata_Plate\n1,1,plate\n", False),
        (
            "ImageNumber,ObjectNumber,AreaShape_Area,Image_Metadata_Plate\n1,1,5,plate\n",
            False,
        ),
    ),
)
def test_matched_csv_scientific_comparison_rejects_value_and_schema_changes(
    tmp_path: Path,
    candidate: str,
    equivalent: bool,
) -> None:
    roots = (tmp_path / "native", tmp_path / "candidate")
    for root in roots:
        root.mkdir()
    (roots[0] / "Cells.csv").write_text(
        "ImageNumber,ObjectNumber,AreaShape_Area,Metadata_Plate\n1,1,5,plate\n"
    )
    (roots[1] / "Cells.csv").write_text(candidate)
    policy = matched_batch._strict_cellprofiler_runtime_equivalence_policy()
    measurements = tuple(
        RuntimeMeasurementSnapshot.from_output_snapshot(
            RuntimeOutputSnapshot.from_output_root(root),
            policy=policy,
        )
        for root in roots
    )
    report = runtime_measurement_equivalence(*measurements, policy=policy)
    assert report.is_equivalent is equivalent


@pytest.mark.parametrize(
    "candidate_text",
    (
        "ImageNumber,ObjectNumber,AreaShape_Area\n1,1,5\n1,2,5\n",
        "ImageNumber,ObjectNumber,AreaShape_Area\n",
    ),
)
def test_matched_inventory_rejects_csv_row_duplication_or_loss(
    tmp_path: Path,
    candidate_text: str,
) -> None:
    roots = (tmp_path / "native", tmp_path / "candidate")
    for root in roots:
        root.mkdir()
    (roots[0] / "Cells.csv").write_text(
        "ImageNumber,ObjectNumber,AreaShape_Area\n1,1,5\n"
    )
    (roots[1] / "Cells.csv").write_text(candidate_text)
    exports = tuple(RuntimeExportObservation.from_output_root(root) for root in roots)
    snapshots = tuple(
        RuntimeOutputSnapshot.from_export_observation(item) for item in exports
    )
    with pytest.raises(RuntimeError, match="CSV table row counts differ"):
        matched_batch._require_compared_output_inventory(
            reference_files=frozenset(roots[0].iterdir()),
            candidate_files=frozenset(roots[1].iterdir()),
            reference_exports=exports[0],
            candidate_exports=exports[1],
            reference_snapshot=snapshots[0],
            candidate_snapshot=snapshots[1],
        )


def test_matched_inventory_rejects_metadata_only_outputs(tmp_path: Path) -> None:
    (tmp_path / "Experiment.csv").write_text("Key,Value\nVersion,1\n")
    exports = RuntimeExportObservation.from_output_root(tmp_path)
    snapshot = RuntimeOutputSnapshot.from_export_observation(exports)
    with pytest.raises(RuntimeError, match="no compared scientific output"):
        matched_batch._require_compared_output_inventory(
            reference_files=frozenset(tmp_path.iterdir()),
            candidate_files=frozenset(tmp_path.iterdir()),
            reference_exports=exports,
            candidate_exports=exports,
            reference_snapshot=snapshot,
            candidate_snapshot=snapshot,
        )


@pytest.mark.parametrize("renamed", (False, True))
def test_matched_inventory_accepts_only_declared_workspace_managed_paths(
    tmp_path: Path,
    renamed: bool,
) -> None:
    roots = (tmp_path / "native", tmp_path / "candidate")
    for root in roots:
        root.mkdir()
        (root / "Image.csv").write_text("ImageNumber,Count_Cells\n1,2\n")
    config = (
        replace(matched_batch.METADATA_CONFIG, METADATA_FILENAME="renamed.json")
        if renamed
        else matched_batch.METADATA_CONFIG
    )
    managed_files = frozenset(config.managed_paths(roots[1]))
    for path in managed_files:
        path.write_text("{}")

    def validate() -> None:
        exports = tuple(
            RuntimeExportObservation.from_output_root(root) for root in roots
        )
        snapshots = tuple(
            RuntimeOutputSnapshot.from_export_observation(item) for item in exports
        )
        matched_batch._require_compared_output_inventory(
            reference_files=frozenset(roots[0].rglob("*")),
            candidate_files=frozenset(
                path for path in roots[1].rglob("*") if path.is_file()
            ),
            reference_exports=exports[0],
            candidate_exports=exports[1],
            reference_snapshot=snapshots[0],
            candidate_snapshot=snapshots[1],
            candidate_managed_files=managed_files,
        )

    validate()
    nested = roots[1] / "unowned"
    nested.mkdir()
    (nested / config.METADATA_FILENAME).write_text("{}")
    with pytest.raises(RuntimeError, match="without a value comparison"):
        validate()


def test_pilot_parser_requires_one_sampling_declaration() -> None:
    parser = _parser()
    common = (
        "--manifest",
        "manifest.json",
        "--case",
        "advanced",
        "--output-dir",
        "output",
        "--native-python",
        "native-python",
    )

    with pytest.raises(SystemExit):
        parser.parse_args(common)
    assert parser.parse_args((*common, "--well-count", "8")).well_count == 8
    assert parser.parse_args(
        (*common, "--well", "A01", "--well", "B12")
    ).requested_wells == ["A01", "B12"]
    with pytest.raises(SystemExit):
        parser.parse_args((*common, "--well-count", "2", "--well", "A01"))


def test_pilot_sampling_resolves_only_genuine_declared_wells() -> None:
    available = {"A01", "A12", "B01", "B12"}

    assert _select_genuine_wells(available, well_count=2, requested_wells=()) == (
        "A01",
        "A12",
    )
    assert _select_genuine_wells(
        available, well_count=None, requested_wells=("B12", "A01")
    ) == ("B12", "A01")
    with pytest.raises(ValueError, match="unique"):
        _select_genuine_wells(
            available, well_count=None, requested_wells=("A01", "A01")
        )
    with pytest.raises(ValueError, match="absent"):
        _select_genuine_wells(available, well_count=None, requested_wells=("C01",))
    with pytest.raises(ValueError, match="lacks a declared well"):
        _select_genuine_wells({"A01", None}, well_count=1, requested_wells=())


def test_native_python_keeps_virtual_environment_symlink(tmp_path: Path) -> None:
    base = tmp_path / "base-python"
    base.touch()
    venv_python = tmp_path / "venv-python"
    venv_python.symlink_to(base)

    selected = _native_python_executable(Path("venv-python"), tmp_path)

    assert selected == venv_python
    assert selected != selected.resolve()


@pytest.mark.parametrize(
    ("timeout_seconds", "assignments", "expected_timeout"),
    ((None, (), None), (1800, (), 3600), (1800, ("W001", "W002"), 7200)),
)
def test_native_worker_receives_an_owned_temporary_root(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    timeout_seconds: float | None,
    assignments: tuple[str, ...],
    expected_timeout: float | None,
) -> None:
    invocation: dict[str, object] = {}

    def fake_run(command: tuple[str, ...], **kwargs: object) -> CompletedProcess[str]:
        invocation.update(kwargs)
        request = json.loads(Path(command[-1]).read_text())
        Path(request["report_path"]).write_text("{}")
        kwargs["stdout"].write("native stdout is diagnostic text\n")
        kwargs["stderr"].write("native stderr evidence\n")
        return CompletedProcess(command, 0)

    monkeypatch.setattr(matched_batch.subprocess, "run", fake_run)
    evidence_prefix = tmp_path / "native"
    request_path = tmp_path / "request.json"
    request_path.write_text(
        json.dumps({"assignment_output_subdirectories": assignments})
    )

    assert (
        _invoke_native_worker(
            native_python=Path("native-python"),
            worker_script=Path("worker.py"),
            request_path=request_path,
            evidence_prefix=evidence_prefix,
            project_root=tmp_path,
            repetitions=1,
            timeout_seconds=timeout_seconds,
        )
        == {}
    )
    temporary_root = tmp_path / "native_tmp"
    assert temporary_root.is_dir()
    assert "capture_output" not in invocation
    assert invocation["timeout"] == expected_timeout
    assert json.loads(request_path.read_text())["report_path"] == str(
        tmp_path / "native_report.json"
    )
    assert (
        tmp_path / "native_stdout.log"
    ).read_text() == "native stdout is diagnostic text\n"
    assert (tmp_path / "native_stderr.log").read_text() == "native stderr evidence\n"
    native_environment = invocation["env"]
    assert isinstance(native_environment, dict)
    assert native_environment["TMPDIR"] == str(temporary_root)
    assert native_environment["TMP"] == str(temporary_root)
    assert native_environment["TEMP"] == str(temporary_root)


def test_output_inventory_retains_relative_paths_and_content_digests(
    tmp_path: Path,
) -> None:
    images = tmp_path / "images"
    images.mkdir()
    output = images / "overlay.tiff"
    output.write_bytes(b"pixel evidence")

    inventory = _output_inventory(tmp_path, frozenset({output}))

    assert inventory == (
        {
            "path": "images/overlay.tiff",
            "sha256": hashlib.sha256(b"pixel evidence").hexdigest(),
        },
    )


def test_source_input_inventory_hashes_symlink_target(tmp_path: Path) -> None:
    source = tmp_path / "source.tif"
    source.write_bytes(b"microscopy pixels")
    staged = tmp_path / "staged"
    staged.mkdir()
    (staged / "source.tif").symlink_to(source)

    inventory = _source_input_inventory(staged)

    assert inventory == (
        {
            "path": "source.tif",
            "source_path": str(source),
            "size_bytes": len(b"microscopy pixels"),
            "sha256": hashlib.sha256(b"microscopy pixels").hexdigest(),
        },
    )


def test_pilot_inventories_stream_files_without_read_bytes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    source = tmp_path / "image.tif"
    source.write_bytes(b"microscopy pixels")
    staged = tmp_path / "staged"
    staged.mkdir()
    (staged / "image.tif").symlink_to(source)

    def reject_read_bytes(_path: Path) -> bytes:
        raise AssertionError("Pilot inventory must stream source and output files")

    monkeypatch.setattr(Path, "read_bytes", reject_read_bytes)
    expected = hashlib.sha256(b"microscopy pixels").hexdigest()

    assert _source_input_inventory(staged)[0]["sha256"] == expected
    assert _output_inventory(tmp_path, frozenset({source}))[0]["sha256"] == expected


def test_candidate_worker_count_uses_ordinary_global_config(tmp_path: Path) -> None:
    config = _global_config(
        tmp_path,
        ("A01", "A12"),
        worker_count=2,
        start_method=MultiprocessingStartMethod.FORK,
    )

    assert config.num_workers == 2
    assert config.multiprocessing_start_method is MultiprocessingStartMethod.FORK
    assert config.materialize_runtime_artifacts is False


def test_candidate_pipeline_inherits_benchmark_worker_count(tmp_path: Path) -> None:
    global_config = _global_config(
        tmp_path,
        ("A01", "A12"),
        worker_count=2,
        start_method=MultiprocessingStartMethod.FORK,
    )

    with config_context(global_config):
        imported = PipelineConfig(
            num_workers=1,
            use_threading=True,
            multiprocessing_start_method=MultiprocessingStartMethod.SPAWN,
        )
        candidate = _candidate_pipeline_config(
            imported, global_config, tmp_path, ("A01", "A12")
        )

        assert candidate.num_workers == 2
        assert candidate.use_threading is False
        assert candidate.multiprocessing_start_method is MultiprocessingStartMethod.FORK


def _axis_event(axis_id: str, phase: str, pid: int, timestamp: float) -> ProgressEvent:
    return ProgressEvent.from_dict(
        {
            "execution_id": "job-1",
            "plate_id": "plate-1",
            "axis_id": axis_id,
            "step_name": "pipeline",
            "phase": phase,
            "status": "started" if phase == "axis_started" else "success",
            "percent": 0.0 if phase == "axis_started" else 100.0,
            "completed": 0 if phase == "axis_started" else 1,
            "total": 1,
            "timestamp": timestamp,
            "pid": pid,
        }
    )


def test_worker_axis_evidence_proves_distinct_overlapping_processes() -> None:
    events = (
        _axis_event("A01", "axis_started", 11, 1.0),
        _axis_event("A12", "axis_started", 22, 1.2),
        _axis_event("A12", "axis_completed", 22, 2.8),
        _axis_event("A01", "axis_completed", 11, 3.0),
    )

    evidence = _worker_axis_evidence(
        events, execution_id="job-1", expected_axes=2, expected_workers=2
    )

    assert evidence["worker_process_ids"] == (11, 22)
    assert evidence["worker_interval_overlap_seconds"] == pytest.approx(1.6)


def test_worker_axis_evidence_rejects_one_process_for_two_workers() -> None:
    events = (
        _axis_event("A01", "axis_started", 11, 1.0),
        _axis_event("A12", "axis_started", 11, 1.2),
        _axis_event("A12", "axis_completed", 11, 2.8),
        _axis_event("A01", "axis_completed", 11, 3.0),
    )

    with pytest.raises(RuntimeError, match="expected 2"):
        _worker_axis_evidence(
            events, execution_id="job-1", expected_axes=2, expected_workers=2
        )
