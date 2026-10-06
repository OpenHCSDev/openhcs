import csv
import json
import shutil
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[4]))
from benchmark.reports.cppipe_figures import (
    MeasuredBatchSummarySource,
    SerialCellProfilerBatchSummarySource,
)
from paper.figures.build_slas_benchmark import build_measured

record = Path("benchmark/results/matched_lastconsumer_20261006")
out = Path("paper/figures/slas/matched_lastconsumer_20261006")
receipts = {}
for scope in ("execution", "total"):
    sources = tuple(
        f"16 assignments/{n} worker{suffix}={record}/data/16assignments-{n}worker{suffix}/{scope}_summary.csv"
        for n, suffix in ((1, ""), (4, "s"))
    )
    baseline = record / "data/16assignments-1worker" / f"{scope}_summary.csv"
    build_measured(sources, scope, out / f"primary-{scope}", native_baseline=baseline)
    build_measured(sources, scope, out / f"independent-cp-calibration-{scope}")
    candidate = SerialCellProfilerBatchSummarySource(
        "16 assignments/4 workers",
        record / "data/16assignments-4workers" / f"{scope}_summary.csv",
        MeasuredBatchSummarySource("one process", baseline),
    )
    with candidate.path.open() as f:
        row = next(csv.DictReader(f))
    native, oh = candidate.metric_rows(row["case_name"], row, category_row=row)
    assert oh.speedup == native.raw_seconds / oh.raw_seconds
    assert oh.speedup != float(row["median_speedup"])
    receipts[scope] = {
        "native_seconds": native.raw_seconds,
        "openhcs_seconds": oh.raw_seconds,
        "primary_speedup": oh.speedup,
        "original_calibration_speedup": float(row["median_speedup"]),
    }
source = SerialCellProfilerBatchSummarySource(
    "4 workers",
    record / "data/16assignments-4workers/execution_summary.csv",
    MeasuredBatchSummarySource(
        "one process", record / "data/16assignments-1worker/execution_summary.csv"
    ),
)
total = SerialCellProfilerBatchSummarySource(
    "4 workers",
    record / "data/16assignments-4workers/total_summary.csv",
    MeasuredBatchSummarySource(
        "one process", record / "data/16assignments-1worker/total_summary.csv"
    ),
)
claims = source.publication_values(total, record_name=record.name, frozen=True)
assert claims["execution_min"] == f"{receipts['execution']['primary_speedup']:.3f}"
assert claims["total_min"] == f"{receipts['total']['primary_speedup']:.3f}"
for field in ("source_head", "manifest", "assignments", "native_job_count"):
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp)
        shutil.copyfile(source.baseline.path, path / "execution_summary.csv")
        custody = source.baseline.qualified_custody()
        if field == "source_head":
            custody[field] = "wrong-source"
        elif field == "manifest":
            custody[field]["sha256"] = "wrong-declaration"
        elif field == "assignments":
            custody["cases"][0]["mode"]["wells"].pop()
        else:
            custody["cases"][0]["mode"][field] = 4
        (path / "summary_custody.json").write_text(json.dumps(custody))
        candidate = SerialCellProfilerBatchSummarySource(
            "4 workers",
            source.path,
            MeasuredBatchSummarySource("bad baseline", path / "execution_summary.csv"),
        )
        try:
            _ = candidate.baseline_table
        except ValueError as exc:
            receipts[field] = {"rejected": True, "reason": str(exc)}
        else:
            raise AssertionError(f"Accepted mismatched {field}")
cross = SerialCellProfilerBatchSummarySource("4 workers", total.path, source.baseline)
try:
    _ = cross.baseline_table
except ValueError as exc:
    receipts["cross_scope"] = {"rejected": True, "reason": str(exc)}
else:
    raise AssertionError("Accepted execution baseline for total")
receipts["claims"] = claims
receipts["rendered_provenance"] = [str(p) for p in out.glob("*/figure2_provenance.json")]
(record / "protocol/publication-qualification.json").write_text(
    json.dumps(receipts, indent=2) + "\n"
)
print(json.dumps(receipts, indent=2))
