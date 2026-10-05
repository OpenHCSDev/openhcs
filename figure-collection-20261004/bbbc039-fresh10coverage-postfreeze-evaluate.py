"""Coordinator-only recovery of one frozen full200 reference score.

Receipt orchestration only: unchanged installed benchmark reference loading and
instance matching own all image decoding and scoring. No pipeline is executed.
Print the complete result for the caller to preserve with apply_patch.
"""
from __future__ import annotations

import ast
import csv
import hashlib
import json
import resource
import sys
import time
from collections import Counter
from dataclasses import asdict
from datetime import datetime, timezone
from pathlib import Path


def digest(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def totals(rows):
    # Same receipt summation as the existing612 driver, not a matching scorer.
    tp = sum(row["true_positive_count"] for row in rows)
    fp = sum(row["false_positive_count"] for row in rows)
    fn = sum(row["false_negative_count"] for row in rows)
    return {
        "fields": len(rows), "reference_objects": tp + fn,
        "predicted_objects": tp + fp, "true_positives": tp,
        "false_positives": fp, "false_negatives": fn,
        "precision": tp / (tp + fp) if tp + fp else 0.0,
        "recall": tp / (tp + fn) if tp + fn else 0.0,
        "micro_f1": 2 * tp / (2 * tp + fp + fn) if 2 * tp + fp + fn else 0.0,
        "macro_f1": sum(row["f1"] for row in rows) / len(rows),
        "mean_panoptic_quality": sum(row["panoptic_quality"] for row in rows) / len(rows),
        "tp_weighted_mean_matched_iou": (
            sum(row["mean_matched_iou"] * row["true_positive_count"] for row in rows) / tp
            if tp else 0.0
        ),
        "split_reference_count": sum(row["split_reference_count"] for row in rows),
        "merged_prediction_count": sum(row["merged_prediction_count"] for row in rows),
        "signed_count_error": fp - fn,
    }


def primary_step(path):
    tree = ast.parse(path.read_text())
    steps = next(node.value for node in tree.body if isinstance(node, ast.Assign)
                 and any(isinstance(target, ast.Name) and target.id == "pipeline_steps"
                         for target in node.targets))
    return ast.dump(steps.elts[0], include_attributes=False)


started = time.monotonic()
author, old_path, trusted = map(Path, sys.argv[1:])
manifest_path = author / "manifest.json"
freeze_path = author / "freeze.json"
completion_path = author / "completion.json"
first_path = author / "attempts/FIRST/pipeline.py"
final_path = author / "pipeline.py"
custody_path = author.parents[2] / "OWNER-BBBC039-TERMINAL.rst"
manifest = json.loads(manifest_path.read_text())
freeze = json.loads(freeze_path.read_text())
completion = json.loads(completion_path.read_text())
custody = custody_path.read_text()
assert "Original author 63369: turn.completed" in custody
assert completion["client_eof_actual"]["exit_code"] == 2
assert all(not record["process_present"] and record["exact_identity_exited"]
           for record in completion["owned_process_observation"]["processes"])
native = completion["owned_native_close"]["results"][0]["payloads"][0]["outcome"]
viewer = completion["owned_viewer_close"]["results"][0]["payloads"][0]
assert native["succeeded"] and native["process_exited"] and native["acknowledged"]
assert viewer["succeeded"] and viewer["process_exited"] and viewer["acknowledged"]
job = completion["native_job"]["results"][0]["payloads"][0]
assert job["status"] == "complete" and not job["errors"]
assert manifest["coverage"]["expected"] == manifest["coverage"]["labels"] == 200
assert manifest["coverage"]["native_object_rows"] == 21371
assert primary_step(first_path) == primary_step(final_path)
assert digest(final_path) == "0824f47839bfe4a5ac05592d8e57f4c548c68517ea46f7ea7765d0921b9f6b1a"

closed = {}
for line in custody.splitlines():
    if len(line) > 66 and line[64:66] == "  " and line[66:].startswith("/"):
        expected, path = line.split("  ", 1)
        assert len(expected) == 64 and digest(path) == expected
        closed[path] = expected
assert len(closed) == 6
journal_path = next(Path(path) for path in closed if path.endswith(".jsonl"))
with journal_path.open("rb") as stream:
    offset = max(0, journal_path.stat().st_size - 65536)
    stream.seek(offset)
    if offset:
        stream.readline()
    events = [json.loads(line) for line in stream if line.strip()]
terminal = [event for event in events if event["type"] == "event_msg"
            and event["payload"]["type"] == "task_complete"][-1]
assert terminal["timestamp"] == "2026-10-05T13:12:31.614Z"

named = manifest["retained_artifacts"] + manifest["qa_bitmaps"] + [
    manifest["source_inventory"], manifest["final_pipeline"]
]
assert len(named) == len({record["path"] for record in named}) == 2742
assert sum(record["bytes"] for record in named) == 2487862194


def verify_records(records):
    for record in records:
        path = Path(record["path"])
        assert path.stat().st_size == record["bytes"], path
        assert digest(path) == record["sha256"], path


verify_records(named)
verify_records(freeze["files"])
inventory_path = Path(manifest["source_inventory"]["path"])
inventory = json.loads(inventory_path.read_text())
assert len(inventory) == 200


def verify_raw_sources():
    for record in inventory:
        assert digest(record["original_path"]) == record["original_sha256"]
        assert digest(record["staged_path"]) == record["staged_sha256"]
        assert record["original_sha256"] == record["staged_sha256"]


verify_raw_sources()
predictions = {(row["source"]["source_set_id"], row["source"]["channel"],
                row["source"]["partition"]): row for row in manifest["fields"]}
assert len(predictions) == len(manifest["fields"]) == 200
assert sum(row["object_count"] for row in predictions.values()) == 21371
inventory_keys = {(row["source_set_id"], row["channel"], row["partition"])
                  for row in inventory}
assert predictions.keys() == inventory_keys
print("PUBLIC_FREEZE_PASS:2742 named files/2487862194 bytes; original author+client closed; private evaluation now admitted.", flush=True)

# Private comparison begins only after the original frozen terminal is verified.
old = json.loads(old_path.read_text())
old_metrics = {(row["source_set_id"], row["channel"], row["partition"]): row
               for row in old["instance_metrics"]}
with (trusted / "reference_manifest.csv").open(newline="") as stream:
    reference_rows = list(csv.DictReader(stream))
references = {(row["source_set_id"], row["channel"], row["partition"]): row
              for row in reference_rows}
assert predictions.keys() == references.keys() == old_metrics.keys()
assert len(reference_rows) == len(references) == len(old_metrics) == 200
assert old["match_iou"] == .5
reference_hashes = {}
for key, row in references.items():
    assert row["reference_kind"] == "instance_masks"
    path = trusted / row["relative_path"]
    sha = digest(path)
    assert old["protected_sha256_before_after"][str(path)] == sha, path
    reference_hashes[str(path)] = sha

from benchmark.contracts.validation import ValidationEvidenceKind
from benchmark.validation.references import ValidationReferenceStrategy
from benchmark.validation.scoring import _load_label_array, instance_segmentation_metrics
import benchmark.validation.references as references_module
import benchmark.validation.scoring as scoring_module

assert digest(scoring_module.__file__) == old["protected_sha256_before_after"][old["scoring_owner"]]
assert digest(references_module.__file__) == old["protected_sha256_before_after"][old["reference_owner"]]
protected = [manifest_path, freeze_path, completion_path, final_path, first_path,
             custody_path, journal_path, inventory_path, old_path, Path(__file__),
             trusted / "reference_manifest.csv", Path(scoring_module.__file__),
             Path(references_module.__file__)]
before = {str(path): digest(path) for path in protected}
decoder = ValidationReferenceStrategy.for_evidence(ValidationEvidenceKind.INSTANCE_MASKS)
metrics = []
for index, (key, row) in enumerate(sorted(predictions.items()), 1):
    prediction_path = Path(row["instance_labels"]["path"])
    reference_path = trusted / references[key]["relative_path"]
    predicted = _load_label_array(prediction_path)
    reference = decoder.load(reference_path)
    assert predicted.shape == reference.shape == (520, 696), key
    metric = instance_segmentation_metrics(predicted, reference,
        source_set_id=key[0], channel=key[1], match_iou=.5)
    previous = old_metrics[key]
    assert metric.predicted_count == row["object_count"]
    assert metric.reference_count == previous["reference_count"]
    delta_keys = ("true_positive_count", "false_positive_count", "false_negative_count",
                  "predicted_count", "f1", "precision", "recall")
    metrics.append({
        **asdict(metric), "partition": key[2], "shape_yx": [520, 696],
        "prediction_path": str(prediction_path),
        "prediction_sha256_before_after": row["instance_labels"]["sha256"],
        "reference_path": str(reference_path),
        "reference_sha256_before_after": reference_hashes[str(reference_path)],
        "reference_sha256_matches612": True,
        "previous612": {name: previous[name] for name in delta_keys},
        "delta_vs612": {name: asdict(metric)[name] - previous[name] for name in delta_keys},
    })
    del predicted, reference
    if index % 50 == 0:
        print(f"SCORED:{index}/200 sequentially", flush=True)

verify_records(named)
verify_records(freeze["files"])
verify_raw_sources()
assert all(digest(path) == expected for path, expected in before.items())
assert all(digest(path) == expected for path, expected in closed.items())
assert all(digest(path) == expected for path, expected in reference_hashes.items())
summary = totals(metrics)
previous_summary = totals(list(old_metrics.values()))
assert summary["predicted_objects"] == 21371
assert all(abs(previous_summary[key] - old["summary"][key]) < 1e-12
           for key in previous_summary)
distribution = {
    "f1_at_least_0_90": sum(row["f1"] >= .9 for row in metrics),
    "f1_at_least_0_85": sum(row["f1"] >= .85 for row in metrics),
    "f1_below_0_80": sum(row["f1"] < .8 for row in metrics),
    "below_0_80_by_partition": dict(Counter(row["partition"] for row in metrics if row["f1"] < .8)),
    "worst_fields": sorted(metrics, key=lambda row: (row["f1"], row["source_set_id"]))[:12],
    "improved_vs612": sum(row["delta_vs612"]["f1"] > 1e-12 for row in metrics),
    "regressed_vs612": sum(row["delta_vs612"]["f1"] < -1e-12 for row in metrics),
    "unchanged_vs612": sum(abs(row["delta_vs612"]["f1"]) <= 1e-12 for row in metrics),
    "largest_regressions_vs612": sorted(metrics, key=lambda row: row["delta_vs612"]["f1"])[:8],
}
result = {
    "status": "PASS", "evaluated_at_utc": datetime.now(timezone.utc).isoformat(),
    "scope": "Coordinator-only postfreeze full200 reference agreement; same200 keys and reference hashes as published612.",
    "recovery": {"original_parent_handle": "87956", "original_exit": 0,
                 "reason": "Original stdout truncated before summary and not persisted; one read-only recovery, not pipeline replay."},
    "author_root": str(author), "author_terminal_at": terminal["timestamp"],
    "original_author_exit_code": 0, "original_public_client_exit_code": 2,
    "original_native_execution_id": job["server_execution_id"],
    "custody_path": str(custody_path), "closed_journals_before_after": closed,
    "final_pipeline_sha256": before[str(final_path)],
    "first_primary_step_equals_final": True,
    "original_freeze_path": str(freeze_path), "original_freeze_sha256": before[str(freeze_path)],
    "unchanged_named_files_before_after": len(named),
    "unchanged_named_bytes_before_after": sum(row["bytes"] for row in named),
    "unchanged_science_freeze_files_before_after": len(freeze["files"]),
    "unchanged_original_and_staged_source_pairs": len(inventory),
    "unchanged_predictions_before_after": len(metrics),
    "unchanged_references_before_after": len(reference_hashes),
    "protected_sha256_before_after": before,
    "scoring_owner": str(scoring_module.__file__), "reference_owner": str(references_module.__file__),
    "scoring_source_matches612": True, "reference_decoder_source_matches612": True,
    "interpreter": sys.executable, "argv": sys.argv, "match_iou": .5,
    "summary": summary,
    "comparison612": {"report_path": str(old_path), "report_sha256": before[str(old_path)],
        "same200_previous_summary": previous_summary,
        "delta": {key: summary[key] - previous_summary[key] for key in summary}},
    "by_partition": {partition: totals([row for row in metrics if row["partition"] == partition])
                     for partition in sorted({key[2] for key in predictions})},
    "distribution": distribution, "instance_metrics": metrics,
    "elapsed_seconds": time.monotonic() - started,
    "process_high_water_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    "pipeline_execution": False, "author_feedback": False, "reference_pixels_exported": False,
    "limits": [
        "Published first/final primary scientific call is unchanged; technical repairs and six-field development preceded full200.",
        "Three unsuccessful development repairs remain frozen; this score is the actual selected full200 method, not their best-of score.",
        "Prepared instance-mask agreement is not manual biological truth, exhaustive census, unseen generalisation or skill-only causality.",
        "Split/merge counts use any positive overlap in the existing scorer; they are not independently adjudicated biological events.",
        "Original author/client exits and failed inputs are preserved independently of evaluator PASS.",
        "Distribution cutoffs describe the tail; they are not new admission thresholds.",
        "Process ru_maxrss is high-water accounting, not a measured current allocation peak attributable to scoring.",
    ],
}
print("RESULT_JSON_BEGIN", flush=True)
print(json.dumps(result, indent=2), flush=True)
print("RESULT_JSON_END", flush=True)
