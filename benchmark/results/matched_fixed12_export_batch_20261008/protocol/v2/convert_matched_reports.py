"""Qualify first-use CP references against three actual OpenHCS observations.

V1 remains an immutable steady-state conversion. Native repetition -1 includes
internal initialization in execution; it is one observation, never three. Future
assignment references are declared projections over unchanged retained reports.
"""

import argparse
import csv
import hashlib
import json
import math
import statistics
from collections import Counter
from pathlib import Path

from benchmark.matched_cellprofiler_batch import _worker_axis_evidence
from benchmark.native_batch_contracts import NativeBatchReport, NativeBatchRequest
from benchmark.native_execution_projection import RepeatedSourceNativeBatchReport
from benchmark.reports.cppipe_figures import SPEEDUP_TARGET
from benchmark.timing import PhaseTimingRecord, additive_phase_total_seconds
from openhcs.core.progress.types import ProgressEvent
from openhcs.core.source_projection import OpenHCSPlaneAddress


def load(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def median(values):
    require(
        all(math.isfinite(value) and value > 0 for value in values), "Invalid duration"
    )
    return statistics.median(values)


def argument(command, name):
    argv = command["argv"]
    return argv[argv.index(name) + 1]


def qualify_native(case_dir, provenance, native, repetitions, command, scaling):
    """Preserve the physical native domain and admit a separate headline view."""
    serial = NativeBatchReport.from_payload(native)
    serial.require_complete(repetitions)
    require(
        serial.request == NativeBatchRequest(**load(case_dir / "native_request.json")),
        "Native request/report differ",
    )
    require(
        provenance["native_job_count"] == int(argument(command, "--native-jobs")) == 1,
        "First-use headline requires serial native CP",
    )
    require(
        not (case_dir / "native_shards" / "reports.json").exists(),
        "Serial reference cannot borrow native shard clocks",
    )
    require(
        all(
            row.image_set_count == provenance["native_image_set_count"]
            for row in serial.observations
        ),
        "Native acquired domain differs",
    )
    report_path = case_dir / "report.json"
    report = load(report_path)
    require(
        report["native"] == native
        and report["candidate"] == load(case_dir / "candidate_report.json"),
        "Final report differs from original engine reports",
    )
    require(
        all(report[key] == value for key, value in provenance.items()),
        "Final report/provenance differ",
    )
    projected = "--candidate-only" in command["argv"]
    projection = report.get("native_execution_projection")
    target_count = len(provenance["wells"])
    if scaling:
        require(
            target_count == int(argument(command, "--repeat-assignments")),
            "Command assignment count differs",
        )
        require(
            provenance["candidate_worker_count"]
            == int(argument(command, "--openhcs-workers")),
            "Command worker count differs",
        )
        require(
            1 <= provenance["candidate_worker_count"] <= target_count,
            "Workers exceed assignment domain",
        )
        require(
            len(set(provenance["wells"])) == target_count,
            "Duplicate candidate assignment",
        )
        require(
            provenance["assignment_scope"] == "independent repeated source assignments"
            and len(provenance["selected_source_wells"]) == 1,
            "Expected one explicitly repeated genuine source",
        )
        view = RepeatedSourceNativeBatchReport.from_payload(native)
        source_directories = view.assignment_directories
        expected_directories = tuple(
            OpenHCSPlaneAddress.component_token(well) for well in provenance["wells"]
        )
        require(
            serial.request.first_image_set == 1
            and serial.request.last_image_set is None
            and serial.request.start_barrier_root is None,
            "Native reference has a different partition/barrier scope",
        )
        comparison_directories = view.comparison_directories(target_count)
        if not projected:
            require(
                source_directories == expected_directories,
                "Actual native assignment roles differ",
            )
    else:
        require(
            not projected and target_count == provenance["candidate_worker_count"] == 1,
            "Singlewell requires actual one-worker engines",
        )
        source_directories = serial.request.assignment_output_subdirectories or ("",)
        comparison_directories = source_directories
    require(
        len(comparison_directories) == target_count,
        "Comparison domain does not cover candidate assignments",
    )
    fresh = serial.observations[0]
    if projected:
        require(
            scaling
            and provenance["native_capture_status"] == "retained_projection_source",
            "Projected reference lacks declared retained source",
        )
        require(
            argument(command, "--native-execution-model")
            == "retained-first-batch-plus-warm-assignments-v1",
            "Unsupported first-use projection law",
        )
        require(
            provenance["production_source_root"]
            == argument(command, "--production-source-root"),
            "Production source role differs",
        )
        require(
            provenance["benchmark_harness"]["file_sha256"],
            "Independent harness dependency seal absent",
        )
        source_path = Path(provenance["native_reference_report_path"])
        source_sha = sha(source_path)
        require(
            source_sha == provenance["native_reference_report_sha256"]
            and load(source_path) == native,
            "Original retained native report changed",
        )
        expected = view.projected_fresh_batch(
            target_count,
            source_report_path=source_path,
            source_report_sha256=source_sha,
        )
        require(
            projection == json.loads(json.dumps(expected)),
            "Producer projection disagrees with original observed inputs",
        )
        headline = {
            "kind": "projected_first_batch",
            "execution_seconds": projection["projected_fresh_batch_execution_seconds"],
            "prepared_invocation_seconds": projection[
                "projected_fresh_batch_prepared_invocation_seconds"
            ],
            "source_report_path": str(source_path),
            "source_report_sha256": source_sha,
            "source_fresh_repetition": -1,
            "source_fresh_observation_count": 1,
            "target_native_observation_count": 0,
        }
    else:
        require(projection is None, "Actual mode must not carry a projection")
        source_path = Path(
            provenance.get(
                "native_reference_report_path", case_dir / "native_report.json"
            )
        )
        require(
            load(source_path) == native,
            "Actual native report differs from retained original",
        )
        headline = {
            "kind": "measured_first_batch",
            "execution_seconds": fresh.pipeline_execution_seconds,
            "prepared_invocation_seconds": fresh.invocation_seconds,
            "source_report_path": str(source_path),
            "source_report_sha256": sha(source_path),
            "source_fresh_repetition": -1,
            "source_fresh_observation_count": 1,
            "target_native_observation_count": 1,
        }
    median([headline["execution_seconds"], headline["prepared_invocation_seconds"]])
    return headline, projection, source_directories, comparison_directories


def qualify_candidate(
    c,
    provenance,
    native_row,
    source_directories,
    comparison_directories,
    *,
    scaling,
    projected,
):
    """One admission path for warmup and all three actual candidate repetitions."""
    axes = len(provenance["wells"])
    require(c["axis_count"] == axes, "Candidate axis domain differs")
    for key in (
        "database_differences",
        "csv_differences",
        "image_differences",
        "unexpected_output_files",
        "missing_declared_output_files",
    ):
        require(c[key] == [], f"Candidate science failed: {key}")
    require(
        c["declared_output_file_count"] is not None
        and c["declared_output_file_count"] > 0
        and c["native_output_file_count"] > 0,
        "Vacuous output comparison",
    )
    require(
        c["native_image_count"] == c["candidate_image_count"],
        "Compared scientific image domains differ",
    )
    if projected:
        source_count = len(source_directories)
        require(
            c["native_physical_image_count"] * axes
            == c["candidate_physical_image_count"] * source_count,
            "Physical source/target image domain is not uniformly repeated",
        )
        expected_mapping = [
            {"candidate_assignment": well, "observed_reference_directory": directory}
            for well, directory in zip(
                provenance["wells"], comparison_directories, strict=True
            )
        ]
        require(
            c["native_assignment_correspondence"] == expected_mapping,
            "Candidate/native assignment correspondence differs",
        )
        require(
            native_row["image_set_count"] == provenance["native_image_set_count"],
            "Physical native image sets differ",
        )
        require(
            c["native_image_count"] >= c["native_physical_image_count"],
            "Comparison coverage omits source images",
        )
    else:
        require(
            c["native_physical_image_count"] == c["candidate_physical_image_count"],
            "Physical image inventory differs",
        )
    for engine in ("native", "candidate"):
        inventory = c[f"{engine}_output_inventory"]
        require(
            len(inventory) == c[f"{engine}_output_file_count"]
            and len({item["path"] for item in inventory}) == len(inventory),
            "Incomplete or duplicate output inventory",
        )
        require(
            all(
                len(item["sha256"]) == 64
                and all(char in "0123456789abcdef" for char in item["sha256"])
                for item in inventory
            ),
            "Missing scientific output hashes",
        )
    receipt_path = Path(c["receipt_path"])
    receipt = load(receipt_path)
    require(
        receipt["execution_id"] == c["execution_id"]
        and receipt["compile_artifact_id"] == c["compile_artifact_id"],
        "Receipt identity mismatch",
    )
    require(receipt["pipeline_name"] == provenance["case"], "Recipe identity mismatch")
    require(
        receipt["expected_axis_count"] == receipt["observed_axis_count"] == axes,
        "Receipt axis mismatch",
    )
    require(
        c["observation_scope"] == receipt["observation_export_scope"] == "outcomes",
        "Must retain ordinary OUTCOMES",
    )
    progress_path = receipt_path.parent / "well_throughput_progress_events.csv"
    with progress_path.open(newline="") as handle:
        progress = tuple(csv.DictReader(handle))
    require(
        progress
        and all(
            row["case_name"] == provenance["case"]
            and int(row["worker_count"]) == provenance["candidate_worker_count"]
            and int(row["well_count"]) == axes
            for row in progress
        ),
        "Worker progress mode differs",
    )
    events = tuple(
        ProgressEvent.from_dict(
            {
                **row,
                "execution_id": c["execution_id"],
                "plate_id": receipt["execution_plate_id"],
                "timestamp": float(row["timestamp"]),
                "pid": int(row["pid"]),
                "percent": float(row["percent"]),
                "completed": int(row["completed"]),
                "total": int(row["total"]),
            }
        )
        for row in progress
        if row["phase"] in ("axis_started", "axis_completed")
    )
    evidence = _worker_axis_evidence(
        events,
        execution_id=c["execution_id"],
        expected_axes=axes,
        expected_workers=provenance["candidate_worker_count"],
    )
    require(
        tuple(evidence["worker_process_ids"]) == tuple(c["worker_process_ids"])
        and math.isclose(
            evidence["worker_interval_overlap_seconds"],
            c["worker_interval_overlap_seconds"],
            rel_tol=0.0,
            abs_tol=1e-9,
        ),
        "Worker concurrency differs from saved progress",
    )
    require(
        {
            (event.axis_id, event.phase.value, event.timestamp, event.pid)
            for event in events
        }
        == {
            (event["axis_id"], event["phase"], event["timestamp"], event["pid"])
            for event in c["axis_events"]
        },
        "Axis report differs from original progress",
    )
    if scaling:
        require(
            c["assignment_scope"] == provenance["assignment_scope"]
            and tuple(c["compared_assignments"]) == tuple(provenance["wells"]),
            "SCI does not cover exact candidate assignments",
        )
        require(
            {event["axis_id"] for event in c["axis_events"]}
            == set(provenance["wells"]),
            "Axes differ from assignment identities",
        )
    records = tuple(
        PhaseTimingRecord.from_payload(payload) for payload in receipt["phase_timings"]
    )
    require(
        all(not record.cached for record in records),
        "Cached duration cannot enter summary",
    )
    require(
        all(
            math.isfinite(record.seconds)
            and record.seconds >= 0
            and record.pipeline_name == provenance["case"]
            and record.tool == "OpenHCS"
            for record in records
        ),
        "Invalid phase duration or recipe/tool identity",
    )
    require(
        tuple(
            record.phase.name
            for record in records
            if record.phase.name in ("SUBMIT_OPENHCS", "WAIT_OPENHCS")
        )
        == ("SUBMIT_OPENHCS", "WAIT_OPENHCS", "SUBMIT_OPENHCS", "WAIT_OPENHCS"),
        "Compile/execute client phases are not sequential submit/wait pairs",
    )
    require(
        math.isfinite(c["server_job_seconds"]) and c["server_job_seconds"] > 0,
        "Invalid full server execution duration",
    )
    phases = PhaseTimingRecord.seconds_by_phase(records)
    phase_counts = Counter(record.phase.name for record in records)
    require(
        phase_counts["SUBMIT_OPENHCS"] == phase_counts["WAIT_OPENHCS"] == 2,
        "Require disjoint compile+execute client phases",
    )
    total = additive_phase_total_seconds(
        {
            name: seconds
            for name, seconds in phases.items()
            if name in ("SUBMIT_OPENHCS", "WAIT_OPENHCS")
        }
    )
    require(
        math.isclose(
            phases["SERVER_PIPELINE_JOB"],
            c["server_job_seconds"],
            rel_tol=0.0,
            abs_tol=1e-9,
        ),
        "Server duration differs",
    )
    require(
        math.isclose(
            c["server_job_completed_at_epoch_seconds"]
            - c["server_job_started_at_epoch_seconds"],
            c["server_job_seconds"],
            rel_tol=0.0,
            abs_tol=1e-9,
        ),
        "Server clock differs",
    )
    return (
        phases,
        total,
        receipt,
        {str(progress_path): sha(progress_path), str(receipt_path): sha(receipt_path)},
    )


def convert(case_dir, source_commit, repetitions, *, scaling=False, command=None):
    require(
        command is not None
        and repetitions == int(argument(command, "--repetitions")) == 3,
        "Require three command-declared actual OH repetitions",
    )
    require(command["source_freeze_head"] == source_commit, "Command source differs")
    provenance_path = case_dir / "pilot_provenance.json"
    native_path = case_dir / "native_report.json"
    candidate_path = case_dir / "candidate_report.json"
    provenance = load(provenance_path)
    require(
        provenance["source_commit"] == source_commit
        and provenance["source_dirty"] is False,
        "Production source mismatch/dirty",
    )
    require(
        provenance["manifest_sha256"] == sha(Path(argument(command, "--manifest"))),
        "Command manifest differs",
    )
    if "--case" in command["argv"]:
        require(
            provenance["case"] == argument(command, "--case"), "Command recipe differs"
        )
    require(
        provenance["native_input_inventory"]
        and provenance["native_input_inventory"]
        == provenance["native_input_inventory_after"],
        "Input custody mismatch",
    )
    require(
        scaling == ("--repeat-assignments" in command["argv"]),
        "Scaling command mode differs",
    )
    native, candidate = load(native_path), load(candidate_path)
    headline, projection, source_directories, comparison_directories = qualify_native(
        case_dir, provenance, native, repetitions, command, scaling
    )
    require(
        tuple(row["repetition"] for row in candidate) == tuple(range(-1, repetitions)),
        "Incomplete/reordered candidate observations",
    )
    native_rows = {row["repetition"]: row for row in native["observations"]}
    rows, receipts, environments = [], [], []
    raw_inputs = {
        str(path): sha(path)
        for path in (
            provenance_path,
            native_path,
            candidate_path,
            case_dir / "native_request.json",
            case_dir / "report.json",
        )
    }
    for c in candidate:
        rep = c["repetition"]
        n = native_rows[rep]
        phases, total, receipt, inputs = qualify_candidate(
            c,
            provenance,
            n,
            source_directories,
            comparison_directories,
            scaling=scaling,
            projected=projection is not None,
        )
        raw_inputs.update(inputs)
        receipts.append(
            {
                "path": c["receipt_path"],
                "sha256": inputs[c["receipt_path"]],
                "execution_id": c["execution_id"],
                "repetition": rep,
            }
        )
        environments.append(receipt["server_environment"])
        if rep >= 0:
            rows.append(
                {
                    "repetition": rep,
                    "native_execution_seconds": n["pipeline_execution_seconds"],
                    "native_total_seconds": n["invocation_seconds"],
                    "openhcs_execution_seconds": c["server_job_seconds"],
                    "openhcs_total_seconds": total,
                    "openhcs_compile_seconds": phases["SERVER_COMPILATION_JOB"],
                    "openhcs_axis_only_seconds": phases["EXECUTE_OPENHCS"],
                    "openhcs_first_axis_to_completion_seconds": c[
                        "first_axis_through_server_completion_seconds"
                    ],
                }
            )
    require(
        all(env == environments[0] for env in environments),
        "Mixed server environment across all four observations",
    )
    execution = {
        "case_name": provenance["case"],
        "assay_category": "",
        "module_category": "",
        "n": repetitions,
        "equivalent_count": repetitions,
        "native_observation_count": headline["target_native_observation_count"],
        "native_reference_kind": headline["kind"],
        "median_native_execution_seconds": headline["execution_seconds"],
        "median_openhcs_execution_seconds": median(
            [row["openhcs_execution_seconds"] for row in rows]
        ),
        "median_native_total_phase_seconds": headline["prepared_invocation_seconds"],
        "median_openhcs_total_phase_seconds": median(
            [row["openhcs_total_seconds"] for row in rows]
        ),
        "median_native_peak_memory_mb": "",
        "median_openhcs_peak_memory_mb": "",
        "min_parity_accuracy": 1.0,
        "speedup_target": SPEEDUP_TARGET,
    }
    execution["median_speedup"] = (
        execution["median_native_execution_seconds"]
        / execution["median_openhcs_execution_seconds"]
    )
    execution["median_total_phase_speedup"] = (
        execution["median_native_total_phase_seconds"]
        / execution["median_openhcs_total_phase_seconds"]
    )
    execution["meets_execution_speedup_target"] = (
        execution["median_speedup"] >= SPEEDUP_TARGET
    )
    execution["meets_total_phase_speedup_target"] = (
        execution["median_total_phase_speedup"] >= SPEEDUP_TARGET
    )
    total = {
        **execution,
        "median_native_execution_seconds": execution[
            "median_native_total_phase_seconds"
        ],
        "median_openhcs_execution_seconds": execution[
            "median_openhcs_total_phase_seconds"
        ],
        "median_speedup": execution["median_total_phase_speedup"],
    }
    metadata = {
        "case": provenance["case"],
        "source_commit": source_commit,
        "rows": rows,
        "receipts": receipts,
        "raw_inputs": raw_inputs,
        "server_environment": environments[0],
        "native_environment": native["environment"],
        "thread_environment": provenance["thread_environment"],
        "native_headline_reference": headline,
        "native_execution_projection": projection,
        "native_observations": native["observations"],
    }
    metadata["mode"] = {
        key: provenance[key]
        for key in (
            "wells",
            "selected_source_wells",
            "assignment_scope",
            "native_job_count",
            "candidate_worker_count",
            "candidate_worker_start_method",
        )
    }
    metadata["assignment_comparison"] = {
        "native_source_assignment_count": len(source_directories),
        "candidate_assignment_count": len(provenance["wells"]),
        "observed_reference_directories": comparison_directories,
        "candidate_rows": [
            {
                "repetition": row["repetition"],
                "native_assignment_correspondence": row.get(
                    "native_assignment_correspondence"
                ),
                "native_physical_image_count": row["native_physical_image_count"],
                "candidate_physical_image_count": row["candidate_physical_image_count"],
                "native_image_count": row["native_image_count"],
                "candidate_image_count": row["candidate_image_count"],
            }
            for row in candidate
        ],
    }
    if "benchmark_harness" in provenance:
        metadata["benchmark_harness"] = provenance["benchmark_harness"]
    return execution, total, metadata


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--suite-dir", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--scaling", action="store_true")
    args = parser.parse_args()
    command = load(args.suite_dir / "command.json")
    terminal_path = args.suite_dir / "terminal.json"
    terminal = load(terminal_path)
    source_commit = command["source_freeze_head"]
    require(
        terminal["returncode"] == 0
        and terminal["source_head_before"]
        == terminal["source_head_after"]
        == source_commit
        and not terminal["source_status_after"].strip(),
        "Suite failed or production source changed",
    )
    require(
        "--all-cases" in command["argv"],
        "First-use headline requires the complete 30-case suite",
    )
    repetitions = int(argument(command, "--repetitions"))
    manifest_path = Path(argument(command, "--manifest"))
    cases = load(manifest_path)["cases"]
    require(
        len(cases) == 30 and len({case["name"] for case in cases}) == 30,
        "Require all 30 declared cases",
    )
    output_root = Path(argument(command, "--output-dir"))
    converted = [
        convert(
            output_root / case["name"],
            source_commit,
            repetitions,
            scaling=args.scaling,
            command=command,
        )
        for case in cases
    ]
    require(
        [metadata["case"] for _, _, metadata in converted]
        == [case["name"] for case in cases],
        "Case reports differ from manifest",
    )
    first = converted[0][2]
    require(
        all(
            metadata["server_environment"] == first["server_environment"]
            and {
                key: value
                for key, value in metadata["native_environment"].items()
                if key != "temporary_root"
            }
            == {
                key: value
                for key, value in first["native_environment"].items()
                if key != "temporary_root"
            }
            and metadata["thread_environment"] == first["thread_environment"]
            for _, _, metadata in converted
        ),
        "Mixed environment across case matrix",
    )
    require(not args.output_dir.exists(), "Fresh first-use namespace required")
    args.output_dir.mkdir(parents=True)
    for name, index in (
        ("first_use_execution_summary.csv", 0),
        ("first_use_total_summary.csv", 1),
    ):
        rows = [item[index] for item in converted]
        with (args.output_dir / name).open("w", newline="") as handle:
            writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
            writer.writeheader()
            writer.writerows(rows)
    custody = {
        "status": "PASS",
        "source_head": source_commit,
        "suite_terminal": {"path": str(terminal_path), "sha256": sha(terminal_path)},
        "manifest": {"path": str(manifest_path), "sha256": sha(manifest_path)},
        "converter_sha256": sha(Path(__file__)),
        "execution_clock": "CP first fresh pipeline call including internal initialization or explicitly declared projection / OH actual full SERVER_PIPELINE_JOB",
        "total_clock": "CP actual first prepared invocation or projected execution plus actual first preparation once / OH disjoint compile+execute SUBMIT+WAIT, excluding startup and SCI",
        "speedup_definition": "CP one fresh-batch reference divided by median of three measured OH repetitions; n/equivalent_count refer to OH only; legacy median_native columns hold the explicit first-use reference",
        "memory": "Not measured; absent",
        "cases": [metadata for _, _, metadata in converted],
    }
    (args.output_dir / "summary_custody.json").write_text(
        json.dumps(custody, indent=2) + "\n"
    )
    print(
        json.dumps(
            {
                "status": "PASS",
                "cases": len(converted),
                "output_dir": str(args.output_dir),
            }
        )
    )


if __name__ == "__main__":
    main()
