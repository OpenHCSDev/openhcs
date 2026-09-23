from __future__ import annotations

import csv
import json
from pathlib import Path
from types import SimpleNamespace

import pytest
from polystore.virtual_workspace import SourcePixelRef

from benchmark.cellprofiler_benchmark_cli import create_benchmark_argument_parser
from benchmark.reports.cppipe_figures import LINEAR_AXIS_BREAK_POLICY
from benchmark.timing import BenchmarkPhase
from benchmark.well_throughput_scaling import (
    LEGACY_DIRECT_EXECUTION_ROUTE,
    ORDINARY_ZMQ_OUTCOMES_EXECUTION_ROUTE,
    ModuleAbstractionCoverageKind,
    ModuleAbstractionCoverageTable,
    NativeCellProfilerExecutionBaseline,
    PresentationAxisBand,
    PresentationAxisBandPolicy,
    WellThroughputBenchmarkPlan,
    WellThroughputMode,
    WellThroughputObservationKey,
    WellThroughputPresentationReport,
    WellThroughputPresentationSources,
    WellThroughputPreset,
    WellThroughputResult,
    WellThroughputStatus,
    _replicate_source_binding_workspace_wells,
    generate_well_throughput_figures,
    native_execution_baselines_from_summary_csv,
    read_well_throughput_csv,
    run_case_well_throughput,
    run_well_throughput_suite,
    well_throughput_plan_from_manifest,
    well_throughput_start_method_from_manifest,
    write_well_throughput_csv,
)
from openhcs.constants.constants import AllComponents
from openhcs.core.config import (
    MultiprocessingStartMethod,
    PipelineConfig,
    WellFilterConfig,
)
from openhcs.core.orchestrator.execution_result import ExecutionResult
from openhcs.core.source_projection import (
    OpenHCSPlaneAddress,
    SourcePlaneProjection,
    SourceProjectionMetadataSerializer,
)
from openhcs.core.virtual_workspace_metadata import (
    FIELDS,
    VirtualWorkspaceMapping,
    VirtualWorkspaceSourceProjectionEntries,
)
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser
from openhcs.runtime.zmq_execution_observation import ZMQRuntimeExecutionOutcomeExport
from openhcs.runtime.zmq_execution_signature import ZMQRuntimeObservationExportScope


def test_well_throughput_presets_are_paired_modes() -> None:
    plan = WellThroughputBenchmarkPlan.from_presets(
        (
            WellThroughputPreset.WELL_1_THREAD_1,
            WellThroughputPreset.WELLS_8_WORKERS_2,
            WellThroughputPreset.WELLS_12_WORKERS_3,
            WellThroughputPreset.WELLS_16_WORKERS_4,
        )
    )

    assert tuple((mode.well_count, mode.worker_count) for mode in plan.modes) == (
        (1, 1),
        (8, 2),
        (12, 3),
        (16, 4),
    )
    assert tuple(mode.name for mode in plan.modes) == (
        "1w_1t",
        "8w_2c",
        "12w_3c",
        "16w_4c",
    )


def test_well_throughput_axis_plan_preserves_legacy_cross_product() -> None:
    plan = WellThroughputBenchmarkPlan.from_axes(
        well_counts=(12, 8),
        worker_counts=(3, 2),
    )

    assert tuple((mode.well_count, mode.worker_count) for mode in plan.modes) == (
        (8, 2),
        (8, 3),
        (12, 2),
        (12, 3),
    )


def test_native_execution_baselines_from_summary_csv(tmp_path: Path) -> None:
    path = tmp_path / "summary.csv"
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=("case_name", "median_native_execution_seconds"),
        )
        writer.writeheader()
        writer.writerow(
            {
                "case_name": "Example",
                "median_native_execution_seconds": "2.5",
            }
        )

    baselines = native_execution_baselines_from_summary_csv(path)

    assert baselines == {"Example": NativeCellProfilerExecutionBaseline("Example", 2.5)}
    assert baselines["Example"].projected_execution_seconds(12) == 30.0


def test_well_throughput_plan_from_manifest_reads_declared_modes(
    tmp_path: Path,
) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        """
        {
          "path_roots": {},
          "cases": [],
          "well_throughput_modes": ["1w_1t", "8w_2c", "12w_3c", "16w_4c"]
        }
        """,
        encoding="utf-8",
    )

    plan = well_throughput_plan_from_manifest(manifest_path)

    assert plan is not None
    assert tuple(mode.name for mode in plan.modes) == (
        "1w_1t",
        "8w_2c",
        "12w_3c",
        "16w_4c",
    )


def test_paper_manifest_declares_paired_sweep_modes_and_start_method() -> None:
    manifest_path = Path("benchmark/manifests/official30_portable_axis1.json")

    plan = well_throughput_plan_from_manifest(manifest_path)

    assert plan is not None
    assert tuple((mode.well_count, mode.worker_count) for mode in plan.modes) == (
        (1, 1),
        (8, 2),
        (12, 3),
        (16, 4),
    )
    assert well_throughput_start_method_from_manifest(manifest_path) is (
        MultiprocessingStartMethod.FORK
    )


def test_sweep_runner_uses_manifest_modes_and_worker_start_method(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    from benchmark import well_throughput_scaling

    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        '{"cases": [], "well_throughput_modes": ["8w_2c", "12w_3c"], '
        '"well_throughput_start_method": "spawn"}',
        encoding="utf-8",
    )
    case = SimpleNamespace(
        name="Example",
        dataset_path=tmp_path / "dataset",
        cppipe_path=tmp_path / "pipeline.cppipe",
        well_filter_config=WellFilterConfig(well_filter=1),
    )
    monkeypatch.setattr(
        well_throughput_scaling,
        "load_comparison_cases",
        lambda _manifest_path: (case,),
    )
    submitted: list[tuple[str, MultiprocessingStartMethod, WellFilterConfig]] = []

    def fake_run_case_well_throughput(**kwargs):
        mode = kwargs["mode"]
        submitted.append(
            (mode.name, kwargs["start_method"], kwargs["source_well_filter"])
        )
        return WellThroughputResult(
            case_name="Example",
            mode_name=mode.name,
            worker_count=mode.worker_count,
            well_count=mode.well_count,
            compile_seconds=1.0,
            prepare_seconds=0.0,
            execute_seconds=2.0,
            total_seconds=3.0,
            wells_per_second=mode.well_count / 2.0,
            successful_wells=mode.well_count,
            execution_route=ORDINARY_ZMQ_OUTCOMES_EXECUTION_ROUTE,
        )

    monkeypatch.setattr(
        well_throughput_scaling,
        "run_case_well_throughput",
        fake_run_case_well_throughput,
    )

    rows = run_well_throughput_suite(
        manifest_path,
        output_root=tmp_path / "outputs",
        well_counts=(),
        worker_counts=(),
    )

    assert submitted == [
        ("8w_2c", MultiprocessingStartMethod.SPAWN, case.well_filter_config),
        ("12w_3c", MultiprocessingStartMethod.SPAWN, case.well_filter_config),
    ]
    assert tuple(row.mode_name for row in rows) == ("8w_2c", "12w_3c")


def test_sweep_cli_plan_resolves_paper_manifest_without_acquiring_data(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    output_dir = tmp_path / "unused"
    args = create_benchmark_argument_parser().parse_args(
        (
            "run-well-throughput",
            "--manifest",
            "benchmark/manifests/official30_portable_axis1.json",
            "--output-dir",
            str(output_dir),
            "--plan-only",
        )
    )

    assert args.cli_command.run(args) == 0
    payload = json.loads(capsys.readouterr().out)
    assert tuple(
        (mode["well_count"], mode["worker_count"]) for mode in payload["modes"]
    ) == ((1, 1), (8, 2), (12, 3), (16, 4))
    assert payload["start_method"] == "fork"
    assert not output_dir.exists()


def test_sweep_cli_refuses_to_mix_existing_output_without_resume(
    tmp_path: Path,
) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "cases": [
                    {
                        "name": "Example",
                        "dataset_path": str(tmp_path / "dataset"),
                        "cppipe_path": str(tmp_path / "pipeline.cppipe"),
                    }
                ],
                "well_throughput_modes": ["8w_2c"],
            }
        ),
        encoding="utf-8",
    )
    output_dir = tmp_path / "outputs"
    output_dir.mkdir()
    sentinel = output_dir / "keep.txt"
    sentinel.write_text("keep", encoding="utf-8")
    args = create_benchmark_argument_parser().parse_args(
        (
            "run-well-throughput",
            "--manifest",
            str(manifest_path),
            "--output-dir",
            str(output_dir),
        )
    )

    with pytest.raises(FileExistsError, match="must be empty"):
        args.cli_command.run(args)
    assert sentinel.read_text(encoding="utf-8") == "keep"


def test_sweep_cli_reports_recorded_failure_with_nonzero_exit(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    import benchmark.cellprofiler_benchmark_cli as cli
    import benchmark.well_throughput_scaling as throughput

    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "cases": [
                    {
                        "name": "Example",
                        "dataset_path": str(tmp_path / "dataset"),
                        "cppipe_path": str(tmp_path / "pipeline.cppipe"),
                    }
                ],
                "well_throughput_modes": ["8w_2c"],
            }
        ),
        encoding="utf-8",
    )
    monkeypatch.setattr(cli, "configure_headless_cpu_benchmark_runtime", lambda _: None)
    monkeypatch.setattr(
        throughput,
        "run_well_throughput_suite",
        lambda *_args, **_kwargs: (
            WellThroughputResult.failed(
                case_name="Example",
                mode=WellThroughputMode("8w_2c", 8, 2),
                compile_seconds=0.0,
                prepare_seconds=0.0,
                execute_seconds=0.0,
                total_seconds=1.0,
                peak_memory_mb=None,
                native_execution_baseline=None,
                error_message="compile failed",
                execution_route=ORDINARY_ZMQ_OUTCOMES_EXECUTION_ROUTE,
            ),
        ),
    )
    args = create_benchmark_argument_parser().parse_args(
        (
            "run-well-throughput",
            "--manifest",
            str(manifest_path),
            "--output-dir",
            str(tmp_path / "outputs"),
        )
    )

    assert args.cli_command.run(args) == 1


def test_repeated_wells_keep_all_declared_projection_fields_coherent(
    tmp_path: Path,
) -> None:
    parser = SourceSchemaFilenameParser()
    original = SourcePlaneProjection(
        address=OpenHCSPlaneAddress.from_values("A01", 1, 1, 1, 1),
        ref=SourcePixelRef("disk", "/source/blue.tif"),
        source_alias="Blue",
        source_metadata={"Well": "A01", "site": "1", "channel": "1"},
    )
    serializer = SourceProjectionMetadataSerializer(parser=parser)
    original_path = serializer.virtual_path(original, execution_anchor=True)
    main = {
        **serializer.projection_fields(((original, original_path),)),
        FIELDS.IMAGE_FILES: [original_path],
        FIELDS.WELLS: {"A01": None},
    }
    metadata_path = tmp_path / "openhcs_metadata.json"
    metadata_path.write_text(
        json.dumps({FIELDS.SUBDIRECTORIES: {FIELDS.DEFAULT_SUBDIRECTORY: main}}),
        encoding="utf-8",
    )

    wells = _replicate_source_binding_workspace_wells(metadata_path, ("W001", "W002"))

    assert wells == ("W001", "W002")
    updated = json.loads(metadata_path.read_text(encoding="utf-8"))[
        FIELDS.SUBDIRECTORIES
    ][FIELDS.DEFAULT_SUBDIRECTORY]
    mapping = VirtualWorkspaceMapping.from_subdirectory(updated).entries
    projections = VirtualWorkspaceSourceProjectionEntries.from_subdirectory(
        updated
    ).entries
    assert set(mapping) == set(projections) == set(updated[FIELDS.IMAGE_FILES])
    assert len(projections) == 2
    assert {
        projection.address.value_for(AllComponents.WELL)
        for projection in projections.values()
    } == {
        "W001",
        "W002",
    }
    assert all(projection.ref == original.ref for projection in projections.values())
    assert set(updated[FIELDS.SOURCE_METADATA]) == set(projections)


@pytest.mark.parametrize(
    ("source_filter", "expected_source_well"),
    ((1, "A01"), ("B01", "B01")),
)
def test_repeated_wells_use_manifest_source_well_scope(
    tmp_path: Path,
    source_filter: int | str,
    expected_source_well: str,
) -> None:
    parser = SourceSchemaFilenameParser()
    serializer = SourceProjectionMetadataSerializer(parser=parser)
    sources = tuple(
        SourcePlaneProjection(
            address=OpenHCSPlaneAddress.from_values(well, 1, 1, 1, 1),
            ref=SourcePixelRef("disk", f"/source/{well}.tif"),
            source_metadata={"Well": well},
        )
        for well in ("A01", "B01")
    )
    entries = tuple(
        (source, serializer.virtual_path(source, execution_anchor=True))
        for source in sources
    )
    main = {
        **serializer.projection_fields(entries),
        FIELDS.IMAGE_FILES: [path for _source, path in entries],
        FIELDS.WELLS: {"A01": None, "B01": None},
    }
    metadata_path = tmp_path / "openhcs_metadata.json"
    metadata_path.write_text(
        json.dumps({FIELDS.SUBDIRECTORIES: {FIELDS.DEFAULT_SUBDIRECTORY: main}}),
        encoding="utf-8",
    )

    target_wells = _replicate_source_binding_workspace_wells(
        metadata_path,
        ("W001", "W002"),
        source_well_filter=WellFilterConfig(well_filter=source_filter),
    )

    assert target_wells == ("W001", "W002")
    updated = json.loads(metadata_path.read_text(encoding="utf-8"))[
        FIELDS.SUBDIRECTORIES
    ][FIELDS.DEFAULT_SUBDIRECTORY]
    projections = VirtualWorkspaceSourceProjectionEntries.from_subdirectory(
        updated
    ).entries
    assert len(projections) == 2
    assert {projection.ref for projection in projections.values()} == {
        SourcePixelRef("disk", f"/source/{expected_source_well}.tif")
    }


def test_requested_well_throughput_axes_override_manifest_modes(
    tmp_path: Path,
) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        """
        {
          "path_roots": {},
          "cases": [],
          "well_throughput_modes": ["1w_1t", "8w_2c", "12w_3c"]
        }
        """,
        encoding="utf-8",
    )

    plan = WellThroughputBenchmarkPlan.from_requested_modes(
        well_counts=(2,),
        worker_counts=(1,),
        manifest_path=manifest_path,
    )

    assert tuple(
        (mode.name, mode.well_count, mode.worker_count) for mode in plan.modes
    ) == (
        ("2w_1c", 2, 1),
    )


def test_requested_well_throughput_presets_override_axis_modes(
    tmp_path: Path,
) -> None:
    plan = WellThroughputBenchmarkPlan.from_requested_modes(
        presets=(WellThroughputPreset.WELL_1_THREAD_1,),
        well_counts=(2,),
        worker_counts=(1,),
        manifest_path=tmp_path / "missing.json",
    )

    assert tuple(mode.name for mode in plan.modes) == ("1w_1t",)


def test_well_throughput_csv_round_trip_preserves_resume_identity(
    tmp_path: Path,
) -> None:
    path = tmp_path / "well_throughput.csv"
    row = WellThroughputResult(
        case_name="Example",
        mode_name="12w_3c",
        worker_count=3,
        well_count=12,
        compile_seconds=1.0,
        prepare_seconds=0.0,
        execute_seconds=2.0,
        total_seconds=3.0,
        wells_per_second=6.0,
        successful_wells=12,
        native_single_sample_execution_seconds=10.0,
        projected_native_execution_seconds=120.0,
        projected_execution_speedup=60.0,
        peak_memory_mb=512.0,
    )

    write_well_throughput_csv(path, (row,))

    restored = read_well_throughput_csv(path)
    assert restored == (row,)
    assert WellThroughputObservationKey(
        restored[0].case_name,
        restored[0].mode_name,
    ) == WellThroughputObservationKey("Example", "12w_3c")


def test_well_throughput_csv_reads_legacy_rows_without_status(
    tmp_path: Path,
) -> None:
    path = tmp_path / "well_throughput.csv"
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=(
                "case_name",
                "mode_name",
                "worker_count",
                "well_count",
                "compile_seconds",
                "prepare_seconds",
                "execute_seconds",
                "total_seconds",
                "wells_per_second",
                "successful_wells",
                "native_single_sample_execution_seconds",
                "projected_native_execution_seconds",
                "projected_execution_speedup",
                "peak_memory_mb",
            ),
        )
        writer.writeheader()
        writer.writerow(
            {
                "case_name": "Example",
                "mode_name": "8w_2c",
                "worker_count": "2",
                "well_count": "8",
                "compile_seconds": "1.0",
                "prepare_seconds": "0.0",
                "execute_seconds": "2.0",
                "total_seconds": "3.0",
                "wells_per_second": "4.0",
                "successful_wells": "8",
                "native_single_sample_execution_seconds": "",
                "projected_native_execution_seconds": "",
                "projected_execution_speedup": "",
                "peak_memory_mb": "",
            }
        )

    (row,) = read_well_throughput_csv(path)

    assert row.status is WellThroughputStatus.SUCCESS
    assert row.memory_limit_mb is None
    assert row.error_message is None
    assert row.execution_route == LEGACY_DIRECT_EXECUTION_ROUTE


def test_memory_limited_result_records_guardrail() -> None:
    baseline = NativeCellProfilerExecutionBaseline("Example", 2.0)
    result = WellThroughputResult.memory_limited(
        case_name="Example",
        mode=WellThroughputMode("16w_4c", 16, 4),
        compile_seconds=1.0,
        prepare_seconds=0.0,
        execute_seconds=0.0,
        total_seconds=3.0,
        peak_memory_mb=2048.0,
        memory_limit_mb=1024.0,
        native_execution_baseline=baseline,
        error_message="worker terminated",
    )

    assert result.status is WellThroughputStatus.MEMORY_LIMIT_EXCEEDED
    assert not result.is_successful()
    assert result.successful_wells == 0
    assert result.projected_native_execution_seconds == 32.0
    assert result.projected_execution_speedup is None
    assert result.memory_limit_mb == 1024.0


def test_failed_result_records_error_without_speedup() -> None:
    baseline = NativeCellProfilerExecutionBaseline("Example", 2.0)
    result = WellThroughputResult.failed(
        case_name="Example",
        mode=WellThroughputMode("8w_2c", 8, 2),
        compile_seconds=1.0,
        prepare_seconds=0.0,
        execute_seconds=0.0,
        total_seconds=3.0,
        peak_memory_mb=1024.0,
        native_execution_baseline=baseline,
        error_message="shape mismatch",
    )

    assert result.status is WellThroughputStatus.ERROR
    assert not result.is_successful()
    assert result.successful_wells == 0
    assert result.projected_native_execution_seconds == 16.0
    assert result.projected_execution_speedup is None
    assert result.error_message == "shape mismatch"


def test_rerun_missing_memory_filters_completed_rows(
    monkeypatch, tmp_path: Path
) -> None:
    from benchmark import well_throughput_scaling

    case = type(
        "Case",
        (),
        {
            "name": "Example",
            "dataset_path": tmp_path / "dataset",
            "cppipe_path": tmp_path / "pipeline.cppipe",
            "well_filter_config": None,
        },
    )()
    completed = WellThroughputResult(
        case_name="Example",
        mode_name="8w_2c",
        worker_count=2,
        well_count=8,
        compile_seconds=1.0,
        prepare_seconds=0.0,
        execute_seconds=2.0,
        total_seconds=3.0,
        wells_per_second=4.0,
        successful_wells=8,
        peak_memory_mb=128.0,
        execution_route=ORDINARY_ZMQ_OUTCOMES_EXECUTION_ROUTE,
    )
    missing_memory = WellThroughputResult(
        case_name="Example",
        mode_name="12w_3c",
        worker_count=3,
        well_count=12,
        compile_seconds=1.0,
        prepare_seconds=0.0,
        execute_seconds=2.0,
        total_seconds=3.0,
        wells_per_second=6.0,
        successful_wells=12,
        peak_memory_mb=None,
        execution_route=ORDINARY_ZMQ_OUTCOMES_EXECUTION_ROUTE,
    )
    rerun = WellThroughputResult(
        case_name="Example",
        mode_name="12w_3c",
        worker_count=3,
        well_count=12,
        compile_seconds=1.0,
        prepare_seconds=0.0,
        execute_seconds=1.5,
        total_seconds=2.0,
        wells_per_second=8.0,
        successful_wells=12,
        peak_memory_mb=256.0,
        execution_route=ORDINARY_ZMQ_OUTCOMES_EXECUTION_ROUTE,
    )

    monkeypatch.setattr(
        well_throughput_scaling,
        "load_comparison_cases",
        lambda _manifest_path: (case,),
    )
    calls: list[tuple[str, str]] = []

    def fake_run_case_well_throughput(**kwargs):
        calls.append((kwargs["case_name"], kwargs["mode"].name))
        return rerun

    monkeypatch.setattr(
        well_throughput_scaling,
        "run_case_well_throughput",
        fake_run_case_well_throughput,
    )

    rows = run_well_throughput_suite(
        tmp_path / "manifest.json",
        output_root=tmp_path / "out",
        well_counts=(),
        worker_counts=(),
        plan=WellThroughputBenchmarkPlan(
            (
                WellThroughputMode("8w_2c", 8, 2),
                WellThroughputMode("12w_3c", 12, 3),
            )
        ),
        existing_results=(completed, missing_memory),
        rerun_missing_memory=True,
        start_method=MultiprocessingStartMethod.FORK,
    )

    assert calls == [("Example", "12w_3c")]
    assert rows == (completed, rerun)


def test_run_suite_reruns_existing_error_rows(monkeypatch, tmp_path: Path) -> None:
    from benchmark import well_throughput_scaling

    case = type(
        "Case",
        (),
        {
            "name": "Example",
            "dataset_path": tmp_path / "dataset",
            "cppipe_path": tmp_path / "pipeline.cppipe",
            "well_filter_config": None,
        },
    )()
    existing_error = WellThroughputResult(
        case_name="Example",
        mode_name="1w_1t",
        worker_count=1,
        well_count=1,
        compile_seconds=0.0,
        prepare_seconds=0.0,
        execute_seconds=0.0,
        total_seconds=0.0,
        wells_per_second=0.0,
        successful_wells=0,
        status=WellThroughputStatus.ERROR,
        error_message="old failure",
        execution_route=ORDINARY_ZMQ_OUTCOMES_EXECUTION_ROUTE,
    )
    rerun = WellThroughputResult(
        case_name="Example",
        mode_name="1w_1t",
        worker_count=1,
        well_count=1,
        compile_seconds=1.0,
        prepare_seconds=0.0,
        execute_seconds=2.0,
        total_seconds=3.0,
        wells_per_second=1.0,
        successful_wells=1,
        peak_memory_mb=128.0,
        execution_route=ORDINARY_ZMQ_OUTCOMES_EXECUTION_ROUTE,
    )
    monkeypatch.setattr(
        well_throughput_scaling,
        "load_comparison_cases",
        lambda _manifest_path: (case,),
    )
    monkeypatch.setattr(
        well_throughput_scaling,
        "run_case_well_throughput",
        lambda **_kwargs: rerun,
    )

    rows = run_well_throughput_suite(
        tmp_path / "manifest.json",
        output_root=tmp_path / "out",
        well_counts=(),
        worker_counts=(),
        plan=WellThroughputBenchmarkPlan((WellThroughputMode("1w_1t", 1, 1),)),
        existing_results=(existing_error,),
        start_method=MultiprocessingStartMethod.FORK,
    )

    assert rows == (rerun,)


def test_legacy_rows_cannot_be_resumed_or_plotted_with_ordinary_rows(
    tmp_path: Path,
) -> None:
    legacy = WellThroughputResult(
        case_name="Example",
        mode_name="1w_1t",
        worker_count=1,
        well_count=1,
        compile_seconds=1.0,
        prepare_seconds=0.0,
        execute_seconds=2.0,
        total_seconds=3.0,
        wells_per_second=0.5,
        successful_wells=1,
    )
    ordinary = WellThroughputResult(
        case_name="Example",
        mode_name="1w_1t",
        worker_count=1,
        well_count=1,
        compile_seconds=1.0,
        prepare_seconds=0.0,
        execute_seconds=1.0,
        total_seconds=2.0,
        wells_per_second=1.0,
        successful_wells=1,
        execution_route=ORDINARY_ZMQ_OUTCOMES_EXECUTION_ROUTE,
    )
    with pytest.raises(ValueError, match="Cannot resume legacy well-throughput rows"):
        run_well_throughput_suite(
            tmp_path / "manifest.json",
            output_root=tmp_path / "out",
            well_counts=(),
            worker_counts=(),
            plan=WellThroughputBenchmarkPlan((WellThroughputMode("1w_1t", 1, 1),)),
            existing_results=(legacy,),
        )
    assert not (tmp_path / "out").exists()

    csv_path = tmp_path / "mixed.csv"
    write_well_throughput_csv(csv_path, (legacy, ordinary))
    with pytest.raises(ValueError, match="cannot pool different execution routes"):
        generate_well_throughput_figures(csv_path, tmp_path / "figures")


def test_well_throughput_case_submits_one_ordinary_outcome_run(
    monkeypatch, tmp_path: Path
) -> None:
    from benchmark import well_throughput_scaling

    monkeypatch.setattr(
        well_throughput_scaling,
        "prepare_cellprofiler_input_workspace",
        lambda _request: SimpleNamespace(
            pipeline_import_error=None,
            pipeline_steps=[],
            pipeline_config=PipelineConfig(),
            materialization=SimpleNamespace(metadata_path=tmp_path / "metadata.json"),
            execution_plate_path=tmp_path / "plate",
        ),
    )
    monkeypatch.setattr(
        well_throughput_scaling,
        "_replicate_source_binding_workspace_wells",
        lambda _path, well_ids, *, source_well_filter: well_ids,
    )
    submissions = []

    def fake_execute(
        *,
        submission,
        phase_timing,
        timing_observer,
        expected_axis_count,
        execution_port,
        require_owned_server,
    ):
        submissions.append(submission)
        assert expected_axis_count == 1
        assert execution_port == 18088
        assert require_owned_server is True
        assert timing_observer.on_event is not None
        phase_timing.record(BenchmarkPhase.COMPILE_OPENHCS, seconds=1.25)
        phase_timing.record(BenchmarkPhase.EXECUTE_OPENHCS, seconds=2.5)
        phase_timing.record(BenchmarkPhase.SERVER_COMPILATION_JOB, seconds=1.5)
        phase_timing.record(BenchmarkPhase.SERVER_PIPELINE_JOB, seconds=2.75)
        return (
            SimpleNamespace(
                observation_export=ZMQRuntimeExecutionOutcomeExport.from_execution(
                    execution_results={"W001": ExecutionResult.success("W001")},
                    output_roots=(tmp_path / "output",),
                )
            ),
            "source",
        )

    monkeypatch.setattr(
        well_throughput_scaling,
        "execute_measured_openhcs_pipeline",
        fake_execute,
    )

    result = run_case_well_throughput(
        case_name="Example",
        dataset_path=tmp_path / "input",
        cppipe_path=tmp_path / "pipeline.cppipe",
        output_root=tmp_path / "case",
        mode=WellThroughputMode("1w_1t", 1, 1),
        execution_port=18088,
    )

    assert result.is_successful()
    assert result.successful_wells == 1
    assert result.compile_seconds == 1.5
    assert result.execute_seconds == 2.75
    assert result.execution_route == ORDINARY_ZMQ_OUTCOMES_EXECUTION_ROUTE
    assert len(submissions) == 1
    assert submissions[0].plate_id == str(tmp_path / "input")
    assert submissions[0].execution_plate_id == str(tmp_path / "plate")
    assert submissions[0].pipeline_document.pipeline_steps == []
    pipeline_config = submissions[0].pipeline_document.pipeline_config
    assert pipeline_config.path_planning_config.well_filter == 0
    assert pipeline_config.materialize_runtime_artifacts is False
    assert submissions[0].global_pipeline_config.materialize_runtime_artifacts is False
    assert submissions[0].config_params["runtime_observation_export_scope"] == (
        ZMQRuntimeObservationExportScope.OUTCOMES.value
    )


def test_run_suite_passes_memory_limit_to_case_runner(
    monkeypatch, tmp_path: Path
) -> None:
    from benchmark import well_throughput_scaling

    case = type(
        "Case",
        (),
        {
            "name": "Example",
            "dataset_path": tmp_path / "dataset",
            "cppipe_path": tmp_path / "pipeline.cppipe",
            "well_filter_config": None,
        },
    )()
    monkeypatch.setattr(
        well_throughput_scaling,
        "load_comparison_cases",
        lambda _manifest_path: (case,),
    )
    observed_limits: list[float | None] = []

    def fake_run_case_well_throughput(**kwargs):
        observed_limits.append(kwargs["max_memory_mb"])
        return WellThroughputResult(
            case_name="Example",
            mode_name=kwargs["mode"].name,
            worker_count=kwargs["mode"].worker_count,
            well_count=kwargs["mode"].well_count,
            compile_seconds=1.0,
            prepare_seconds=0.0,
            execute_seconds=2.0,
            total_seconds=3.0,
            wells_per_second=4.0,
            successful_wells=kwargs["mode"].well_count,
            peak_memory_mb=128.0,
        )

    monkeypatch.setattr(
        well_throughput_scaling,
        "run_case_well_throughput",
        fake_run_case_well_throughput,
    )

    run_well_throughput_suite(
        tmp_path / "manifest.json",
        output_root=tmp_path / "out",
        well_counts=(),
        worker_counts=(),
        plan=WellThroughputBenchmarkPlan((WellThroughputMode("8w_2c", 8, 2),)),
        max_memory_mb=4096.0,
        start_method=MultiprocessingStartMethod.FORK,
    )

    assert observed_limits == [4096.0]


def test_generate_well_throughput_figures_writes_linear_log_and_points(
    tmp_path: Path,
) -> None:
    csv_path = tmp_path / "well_throughput.csv"
    rows = (
        WellThroughputResult(
            case_name="CaseB",
            mode_name="16w_4c",
            worker_count=4,
            well_count=16,
            compile_seconds=0.1,
            prepare_seconds=0.0,
            execute_seconds=1.0,
            total_seconds=1.1,
            wells_per_second=16.0,
            successful_wells=16,
            projected_execution_speedup=500.0,
            peak_memory_mb=4096.0,
        ),
        WellThroughputResult(
            case_name="CaseA",
            mode_name="1w_1t",
            worker_count=1,
            well_count=1,
            compile_seconds=0.1,
            prepare_seconds=0.0,
            execute_seconds=1.0,
            total_seconds=1.1,
            wells_per_second=1.0,
            successful_wells=1,
            projected_execution_speedup=4.0,
            peak_memory_mb=512.0,
        ),
    )
    write_well_throughput_csv(csv_path, rows)

    outputs = generate_well_throughput_figures(
        csv_path,
        tmp_path / "figures",
        output_formats=("png",),
    )

    assert {output.name for output in outputs} == {
        "well_throughput_speedup.png",
        "well_throughput_speedup_log.png",
        "well_throughput_speedup_summary_statistics.csv",
        "well_throughput_speedup_summary_statistics.md",
        "well_throughput_speedup_cumulative_distribution.csv",
        "well_throughput_speedup_cumulative_distribution.png",
        "well_throughput_speedup_cumulative_distribution_log.png",
        "well_throughput_average_speedup_points.csv",
        "well_throughput_average_speedup_points.png",
        "well_throughput_average_speedup_points_log.png",
        "well_throughput_peak_memory.png",
        "well_throughput_peak_memory_log.png",
    }
    assert all(output.exists() for output in outputs)
    summary_rows = tuple(
        csv.DictReader(
            (
                tmp_path / "figures" / "well_throughput_speedup_summary_statistics.csv"
            ).open(encoding="utf-8", newline="")
        )
    )
    assert tuple(row["label"] for row in summary_rows) == ("1w_1t", "16w_4c")


def test_linear_axis_break_policy_handles_single_extreme_outlier() -> None:
    assert LINEAR_AXIS_BREAK_POLICY.range_for((4.0, 500.0)) is not None


def test_linear_axis_break_policy_prefers_earliest_dominant_outlier_cluster() -> None:
    low_cluster = (
        5.5,
        6.2,
        8.7,
        11.5,
        16.9,
        22.5,
        36.3,
        70.2,
        96.4,
        109.4,
    )
    high_cluster = (725.0, 1477.0, 2044.0, 2277.0)

    low_top, high_bottom, _high_top = LINEAR_AXIS_BREAK_POLICY.range_for(
        (*low_cluster, *high_cluster)
    )

    assert low_top < 130.0
    assert 130.0 < high_bottom < 200.0


def test_presentation_axis_band_policy_keeps_normal_mid_and_outlier_bars_readable() -> (
    None
):
    bands = PresentationAxisBandPolicy().bands_for(
        (
            5.5,
            6.2,
            8.7,
            11.5,
            16.9,
            22.5,
            36.3,
            70.2,
            96.4,
            109.4,
            725.0,
            1477.0,
            2044.0,
            2277.0,
        )
    )

    assert len(bands) == 3
    assert bands[0].contains(36.3)
    assert not bands[0].contains(70.2)
    assert bands[1].contains(70.2)
    assert bands[1].contains(109.4)
    assert not bands[1].contains(725.0)
    assert bands[2].contains(725.0)
    assert bands[2].contains(2277.0)


def test_presentation_axis_band_rejects_invalid_range() -> None:
    try:
        PresentationAxisBand(10.0, 10.0)
    except ValueError as exc:
        assert "upper bound" in str(exc)
    else:
        raise AssertionError("Expected invalid presentation axis band to fail.")


def test_well_throughput_presentation_report_uses_existing_figure_pack(
    tmp_path: Path,
) -> None:
    summary_csv = tmp_path / "summary.csv"
    with summary_csv.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=(
                "case_name",
                "assay_category",
                "module_category",
                "median_speedup",
                "min_parity_accuracy",
            ),
        )
        writer.writeheader()
        writer.writerow(
            {
                "case_name": "CaseA",
                "assay_category": "A",
                "module_category": "M",
                "median_speedup": "5.0",
                "min_parity_accuracy": "1.0",
            }
        )
        writer.writerow(
            {
                "case_name": "CaseB",
                "assay_category": "A",
                "module_category": "M",
                "median_speedup": "8.0",
                "min_parity_accuracy": "1.0",
            }
        )

    def result(
        case_name: str,
        mode_name: str,
        wells: int,
        workers: int,
        speedup: float,
    ) -> WellThroughputResult:
        return WellThroughputResult(
            case_name=case_name,
            mode_name=mode_name,
            worker_count=workers,
            well_count=wells,
            compile_seconds=0.1,
            prepare_seconds=0.0,
            execute_seconds=1.0,
            total_seconds=1.1,
            wells_per_second=float(wells),
            successful_wells=wells,
            projected_execution_speedup=speedup,
            peak_memory_mb=512.0 * workers,
        )

    core_csv = tmp_path / "core.csv"
    core_rows = []
    for case_index, case_name in enumerate(("CaseA", "CaseB"), start=1):
        core_rows.extend(
            (
                result(case_name, "1w_1t", 1, 1, 4.0 + case_index),
                result(case_name, "8w_2c", 8, 2, 8.0 + case_index),
                result(case_name, "12w_3c", 12, 3, 12.0 + case_index),
                result(case_name, "16w_4c", 16, 4, 16.0 + case_index),
            )
        )
    write_well_throughput_csv(core_csv, tuple(core_rows))

    wells_per_core_csv = tmp_path / "wells_per_core.csv"
    wpc_rows = []
    for case_index, case_name in enumerate(("CaseA", "CaseB"), start=1):
        for workers in (2, 3, 4):
            for wells_per_core in (2, 3):
                wells = workers * wells_per_core
                wpc_rows.append(
                    result(
                        case_name,
                        f"{wells}w_{workers}c",
                        wells,
                        workers,
                        float(wells + case_index),
                    )
                )
    write_well_throughput_csv(wells_per_core_csv, tuple(wpc_rows))

    outputs = WellThroughputPresentationReport(
        sources=WellThroughputPresentationSources(
            single_process_summary_csv=summary_csv,
            core_scaling_csv=core_csv,
            wells_per_core_csv=wells_per_core_csv,
        ),
        output_dir=tmp_path / "figures",
        output_formats=("png",),
    ).generate()

    output_names = {path.name for path in outputs}
    assert "01_parity_by_pipeline.png" in output_names
    assert "02_core_scaling_by_pipeline_plus_average_speedup.png" in output_names
    assert "02_core_scaling_by_pipeline_plus_average_speedup_log.png" in output_names
    assert "03_core_scaling_average_with_pipeline_points_speedup.png" in output_names
    assert "04_core_scaling_by_pipeline_plus_average_ram.png" in output_names
    assert "05_speedup_summary_by_core_and_wells_per_core.png" in output_names
    assert "05_speedup_summary_by_core_and_wells_per_core_log.png" in output_names
    assert all(path.exists() for path in outputs)

    summary_rows = tuple(
        csv.DictReader(
            (
                tmp_path
                / "figures"
                / "05_speedup_by_core_and_wells_per_core_summary.csv"
            ).open(encoding="utf-8", newline="")
        )
    )
    assert len(summary_rows) == 9
    assert summary_rows[0]["worker_count"] == "2"
    assert summary_rows[0]["wells_per_core"] == "2"


def test_module_abstraction_coverage_table_maps_existing_family_coverage(
    tmp_path: Path,
) -> None:
    coverage_csv = tmp_path / "module_coverage_semantic_families.csv"
    with coverage_csv.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=(
                "module_name",
                "semantic_family",
                "family_coverage",
                "corpus_coverage",
                "category",
                "dimensionality",
                "respects_masks",
                "family_supported_modules",
                "family_absorbed_modules",
            ),
        )
        writer.writeheader()
        writer.writerow(
            {
                "module_name": "MeasureObjectSizeShape",
                "semantic_family": "measure_objects",
                "family_coverage": "direct_supported",
                "corpus_coverage": "supported_corpus",
                "category": "measurement",
                "dimensionality": "TWO_D",
                "respects_masks": "True",
                "family_supported_modules": "MeasureObjectSizeShape",
                "family_absorbed_modules": "MeasureObjectSizeShape;MeasureObjectIntensity",
            }
        )
        writer.writerow(
            {
                "module_name": "MeasureObjectIntensity",
                "semantic_family": "measure_objects",
                "family_coverage": "semantic_family_supported",
                "corpus_coverage": "not_in_corpus",
                "category": "measurement",
                "dimensionality": "TWO_D",
                "respects_masks": "True",
                "family_supported_modules": "MeasureObjectSizeShape",
                "family_absorbed_modules": "MeasureObjectSizeShape;MeasureObjectIntensity",
            }
        )
        writer.writerow(
            {
                "module_name": "UncoveredModule",
                "semantic_family": "uncovered",
                "family_coverage": "not_supported",
                "corpus_coverage": "not_in_corpus",
                "category": "",
                "dimensionality": "",
                "respects_masks": "False",
                "family_supported_modules": "",
                "family_absorbed_modules": "UncoveredModule",
            }
        )

    table = ModuleAbstractionCoverageTable.from_semantic_family_csv(coverage_csv)
    grouped_rows = table.grouped_rows()

    assert tuple(
        row.module_name for row in grouped_rows[ModuleAbstractionCoverageKind.EXPLICIT]
    ) == ("MeasureObjectSizeShape",)
    assert tuple(
        row.module_name
        for row in grouped_rows[ModuleAbstractionCoverageKind.SHARED_ABSTRACTION]
    ) == ("MeasureObjectIntensity",)
    assert tuple(
        row.module_name for row in grouped_rows[ModuleAbstractionCoverageKind.UNCOVERED]
    ) == ("UncoveredModule",)
