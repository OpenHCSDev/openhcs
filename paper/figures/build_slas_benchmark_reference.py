"""Rebuild reference chart forms from the existing qualified sweep owners."""

from __future__ import annotations

import csv
import inspect
import json
import xml.etree.ElementTree as ET
from dataclasses import replace
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.lines import Line2D
from matplotlib.patches import Patch
from matplotlib.ticker import FixedLocator, FuncFormatter, NullFormatter

from build_slas_benchmark import ROOT, sha256, write_provenance
from build_slas_visual_story import FigureSheet, OUTPUT


class BenchmarkFigure(FigureSheet):
    """Publication distributions share points, summaries and typography."""

    scope_colors = ("#087e8b", "#c76828")
    summary_color = "#152536"
    mean_alpha = .20
    publication = OUTPUT / "benchmark-publication"

    @property
    def summary_handles(self):
        return (
            Patch(facecolor=self.summary_color, alpha=self.mean_alpha, label="Mean bars"),
            Line2D([], [], color=self.summary_color, lw=2.1, label="Median lines"),
        )

    def qualified_claims(self):
        claims = json.loads(self.retained(self.publication / "benchmark_claims.json").read_text())
        if claims["status"] != "qualified-first-use-sweep":
            raise ValueError("Publication figures require the qualified sweep")
        return claims

    def __init__(self, stem: str, height: float, *,
                 reference_label: str = "CellProfiler",
                 limits: tuple[float, float] = (.8, 800)) -> None:
        super().__init__(stem, "", height)
        self.reference_label = reference_label
        self.limits = limits
        self.source(Path(__file__))

    def retained(self, path, record_name="figure2_provenance.json"):
        record_path = path.parent / record_name
        record = json.loads(record_path.read_text())
        if sha256(path) != record["output_sha256"][path.name]:
            raise ValueError(f"Figure source differs from its retained output: {path}")
        self.source(record_path)
        self.source(path)
        return path

    def distributions(self, axis, groups, labels):
        from benchmark.reports.cppipe_figures import SpeedupDistributionSeries, SpeedupSummaryStatistics

        self.source(Path(inspect.getfile(SpeedupSummaryStatistics)))
        number_of_workflows = len(groups[0][0])
        summary_bars = {}
        for group_index, pair in enumerate(groups):
            for scope_index, numbers in enumerate(pair):
                # Fixed workflow offsets reveal the distribution without adding data.
                offset = (scope_index - (len(pair) - 1) / 2) * .44
                jitter = np.linspace(-.14, .14, number_of_workflows)
                if len(numbers) != number_of_workflows or not np.all(np.isfinite(numbers) & (numbers > 0)):
                    raise ValueError("Each distribution requires the same positive workflow values")
                axis.scatter(group_index + offset + jitter, numbers, s=33,
                             color=self.scope_colors[scope_index], alpha=.78,
                             edgecolors="white", linewidths=.35, zorder=3)
                summary = SpeedupSummaryStatistics.from_series(
                    SpeedupDistributionSeries(labels[group_index], tuple(numbers)))
                half_bar_width = .40 / len(pair)
                bar = axis.bar(group_index + offset, summary.mean - 1, bottom=1,
                               width=2 * half_bar_width, color=self.scope_colors[scope_index], alpha=self.mean_alpha,
                               edgecolor=self.scope_colors[scope_index], linewidth=.8, zorder=1)[0]
                summary_bars[bar] = summary
                axis.plot([group_index + offset - half_bar_width, group_index + offset + half_bar_width],
                          [summary.median] * 2, color=self.summary_color, lw=2.1, zorder=4)
        for row_index, (label, values) in enumerate((
            ("Min (×)", (summary.minimum for summary in summary_bars.values())),
            ("Mean (×)", (summary.mean for summary in summary_bars.values())),
            ("Median (×)", (summary.median for summary in summary_bars.values())),
            ("Max (×)", (summary.maximum for summary in summary_bars.values())),
        )):
            y_offset = -5 - row_index * self.plot_font_size * 1.35
            axis.annotate(label, (0, 0), xycoords="axes fraction",
                          xytext=(0, y_offset), textcoords="offset points",
                          ha="right", va="top", fontsize=self.plot_font_size,
                          color=self.summary_color, annotation_clip=False)
            for bar, value in zip(summary_bars, values):
                axis.annotate(f"{value:.1f}",
                              (bar.get_x() + bar.get_width() / 2, 0),
                              xycoords=axis.get_xaxis_transform(),
                              xytext=(0, y_offset), textcoords="offset points",
                              ha="center", va="top", fontsize=self.plot_font_size,
                              color=bar.get_facecolor()[:3], annotation_clip=False)
        axis.set_yscale("log")
        axis.set_ylim(*self.limits)
        axis.yaxis.set_major_locator(FixedLocator((1, 2, 4, 10, 100)))
        axis.yaxis.set_major_formatter(FuncFormatter(lambda v, _: f"{v:g}×"))
        axis.yaxis.set_minor_formatter(NullFormatter())
        axis.axhline(1, color="#a64343", ls="--", lw=1)
        axis.set_xticks(range(len(labels)), labels)
        axis.set_xlim(-.46, len(labels) - .54)
        axis.tick_params(axis="x", pad=77)
        axis.grid(axis="y", alpha=.2)
        axis.set_axisbelow(True)
        axis.spines[["top", "right"]].set_visible(False)
        axis.set_ylabel(f"Speedup over\n{self.reference_label}")


def submission_benchmark_schedule() -> None:
    """Replot the retained measured worker comparison through the shared sheet."""
    sheet = BenchmarkFigure("submission_benchmark_schedule", 5.6,
                            reference_label="one worker", limits=(.8, 5))
    claims = sheet.qualified_claims()
    path = sheet.retained(sheet.publication / "fixed12/execution/first_use_workflow_metrics.csv")
    with path.open(newline="") as stream:
        rows = tuple(csv.DictReader(stream))
    values = {(row["method"], row["pipeline_name"]): float(row["raw_seconds"]) for row in rows}
    if len(values) != len(rows):
        raise ValueError("Duplicate retained workflow times")
    names = sorted({name for method, name in values})
    if len(names) != int(claims["case_count"]):
        raise ValueError("Worker plot differs from the qualified workflow cohort")
    reference_mode = claims["mode_statistics"]["12assignments-1worker"]
    modes = sorted((mode for mode in claims["mode_statistics"].values()
                    if mode["assignment_count"] == reference_mode["assignment_count"]),
                   key=lambda mode: mode["openhcs_worker_count"])
    reference_label = reference_mode["scope_statistics"]["execution"]["label"]
    reference = np.array([values[reference_label, name] for name in names])
    groups = tuple((reference / np.array([
        values[mode["scope_statistics"]["execution"]["label"], name] for name in names]),)
        for mode in modes)
    axis = sheet.plot_axes((.12, .39, .83, .44))
    labels = [f"{mode['openhcs_worker_count']} worker{'s' if mode['openhcs_worker_count'] != 1 else ''}"
              for mode in modes]
    sheet.distributions(axis, groups, labels)
    sheet.text(3, 95, "Measured processing speedup with more workers", size=14, weight="bold")
    sheet.text(3, 88, "Same twelve samples · all thirty workflows · medians of three runs",
               size=sheet.plot_font_size, color="#59697b")
    sheet.figure.legend(handles=[
        Line2D([], [], marker="o", ls="", color=sheet.scope_colors[0], label="Workflows"),
        *sheet.summary_handles,
    ], loc="lower center", bbox_to_anchor=(.53, .025), ncol=3,
       frameon=False, fontsize=sheet.plot_font_size)
    sheet.display_transforms.append({
        "operation": "Replot retained fixed-workload speedups with shared publication typography and minimum, arithmetic mean, median and maximum annotations in × units",
        "analysis_rerun": False,
        "retained_speedups_plotted": len(names) * len(modes),
    })
    sheet.save()


def balanced_cp_projection(anchor, assignments: int, workers: int):
    """Apply the retained affine batch model to equal independent CP processes.

    This is an ideal parallel projection, not measured multicore performance.
    Each process pays initialization; only assignments are partitioned. Below
    eight assignments/process this extrapolates beyond the validation domain.
    """
    if workers < 1 or assignments < workers or assignments % workers:
        raise ValueError("CP projection requires equal positive process workloads")
    per_worker = assignments // workers
    execution = (anchor["observed_source_fresh_execution_seconds"]
                 + (per_worker - anchor["source_assignment_count"])
                 * anchor["derived_warm_assignment_execution_seconds"])
    total = execution + anchor["observed_source_fresh_pre_pipeline_seconds"]
    if not np.isfinite(execution) or execution <= 0 or total < execution:
        raise ValueError("Retained affine model cannot predict this workload")
    return execution, total


def submission_benchmark_summary() -> None:
    """Dense main-paper view of the existing sweep and retained evidence grades."""
    from benchmark.reports.cppipe_figures import SpeedupDistributionSeries, SpeedupSummaryStatistics
    from benchmark.native_execution_projection import RepeatedSourceNativeBatchReport

    sheet = BenchmarkFigure("submission_benchmark_summary", 10.2)
    publication = sheet.publication
    claims = sheet.qualified_claims()
    tables = {}
    for schedule in ("may", "fixed12"):
        for scope in ("execution", "total"):
            path = sheet.retained(publication / schedule / scope / "first_use_workflow_metrics.csv")
            with path.open(newline="") as stream:
                rows = tuple(csv.DictReader(stream))
            table = {(row["method"], row["pipeline_name"]): row for row in rows}
            if len(table) != len(rows):
                raise ValueError("Duplicate workflow rows in retained figure input")
            tables[schedule, scope] = table
    names = tuple(sorted({name for method, name in tables["may", "execution"]}))
    if len(names) != int(claims["case_count"]):
        raise ValueError("Expected the qualified workflow cohort")
    modes = claims["mode_statistics"]

    # Read actual anchor reports through their existing model owner. Never turn
    # these derived times into observations or change the qualified sweep.
    record = ROOT / "benchmark/results/matched_worker_sweep_20261008_latestproduction"
    source_path = record / "data/first_use/8assignments-2workers/summary_custody.json"
    source = json.loads(source_path.read_text())
    if source["status"] != "PASS":
        raise ValueError("The CP anchors must come from a qualified comparison")
    sheet.source(source_path)
    anchors = {}
    for case in source["cases"]:
        path = record / "reports/8assignments-2workers" / case["case"] / "native_report.json"
        digest = sha256(path)
        if digest != case["native_headline_reference"]["source_report_sha256"]:
            raise ValueError(f"Changed CP anchor: {path}")
        report = RepeatedSourceNativeBatchReport.from_payload(json.loads(path.read_text()))
        anchors[case["case"]] = report.projected_fresh_batch(
            8, source_report_path=path, source_report_sha256=digest)
        sheet.source(path)
    if set(anchors) != set(names):
        raise ValueError("CP projection must cover the exact measured workflow cohort")
    sheet.source(Path(inspect.getfile(RepeatedSourceNativeBatchReport)))
    sheet.source(record / "calibration/cold_first/cold-first-model-validation.json")

    def values(mode_name, scope, *, native=False):
        mode = modes[mode_name]
        label = mode["scope_statistics"][scope]["label"]
        if native:
            label = f"CP first batch ({label})"
        schedule = "fixed12" if mode["assignment_count"] == 12 else "may"
        return np.array([float(tables[schedule, scope][label, name]["raw_seconds"])
                         for name in names])

    def ratios(mode_name, scope):
        result = values(mode_name, scope, native=True) / values(mode_name, scope)
        summary = SpeedupSummaryStatistics.from_series(
            SpeedupDistributionSeries(mode_name, tuple(result)))
        expected = modes[mode_name]["scope_statistics"][scope]
        if not np.isclose(summary.median, expected["median"], rtol=1e-12):
            raise ValueError("Plotted ratios differ from the canonical claim")
        return result


    sheet.text(2, 96, "A  How modules were tested", size=14, weight="bold")
    coverage = sheet.retained(publication / "reference-layout/reference_module_coverage.csv",
                        "retained_coverage_provenance.json")
    with coverage.open(newline="") as stream:
        coverage_rows = tuple(csv.DictReader(stream))
    tiers = ("30-workflow corpus", "Module-specific behavior tested", "Shared-path behavior tested",
             "Declaration/import checks only", "No evidence")
    counts = [sum(row["tier"] == tier for row in coverage_rows) for tier in tiers]
    if sum(counts) != len(coverage_rows):
        raise ValueError("Unknown retained coverage grade")
    coverage_colors = ("#16877f", "#4682b4", "#e2a23b", "#969696", "#b2182b")
    pie = sheet.plot_axes((.015, .65, .20, .25))
    present = [i for i, count in enumerate(counts) if count]
    pie.pie([counts[i] for i in present], colors=[coverage_colors[i] for i in present],
            startangle=90, wedgeprops={"width": .34, "edgecolor": "white"})
    pie.text(0, .09, str(len(coverage_rows)), ha="center", va="center", fontsize=23, weight="bold")
    pie.text(0, -.22, "modules", ha="center", va="center", fontsize=sheet.plot_font_size)
    for i, label in enumerate(("In 30 workflows", "Individual tests", "Shared code only",
                                "Import checks only", "No tests")):
        y = 87 - i * 5.2
        if counts[i]:
            sheet.axis.plot(23, y, marker="s", color=coverage_colors[i], markersize=8)
        sheet.text(25, y, f"{label}: {counts[i]}", size=sheet.plot_font_size, va="center")
    sheet.text(3, 58, "Each module counted once. Shared-code tests\ndo not test the module's own algorithm.",
               size=sheet.plot_font_size, color="#59697b", va="top")

    sheet.text(54, 96, "B  One worker · measured times", size=14, weight="bold")
    single = tuple(ratios("singlewell", scope) for scope in ("execution", "total"))
    amortized = []
    for scope in ("execution", "total"):
        numbers = (values("8assignments-2workers", scope, native=True) / 8
                   / (values("12assignments-1worker", scope) / 12))
        summary = SpeedupSummaryStatistics.from_series(SpeedupDistributionSeries(scope, tuple(numbers)))
        if not np.isclose(summary.median, claims["amortized_statistics"][scope]["median"], rtol=1e-12):
            raise ValueError("Per-well ratios differ from the canonical amortized claim")
        amortized.append(numbers)
    axis = sheet.plot_axes((.60, .65, .37, .24))
    sheet.distributions(axis, (single, amortized), ("1 sample each", "Batched samples\nCP: 8; OpenHCS: 12"))

    sheet.text(2, 46, "C  Same cores and samples", size=14, weight="bold")
    sheet.text(2, 43.5, "OpenHCS measured · CellProfiler estimated, assuming ideal parallel execution",
               size=sheet.plot_font_size, color="#59697b")
    ordered = sorted(modes, key=lambda key: (modes[key]["openhcs_worker_count"], modes[key]["assignment_count"]))
    ordered = [key for key in ordered if key != "singlewell"]
    groups = []
    projected_rows = []
    for key in ordered:
        mode = modes[key]
        predicted = np.array([balanced_cp_projection(
            anchors[name], mode["assignment_count"], mode["openhcs_worker_count"])
            for name in names])
        groups.append(tuple(predicted[:, i] / values(key, scope)
                            for i, scope in enumerate(("execution", "total"))))
        for i, name in enumerate(names):
            for j, scope in enumerate(("execution", "total")):
                projected_rows.append({"workflow": name, "scope": scope,
                    "workers_each": mode["openhcs_worker_count"],
                    "wells_each": mode["assignment_count"],
                    "wells_per_worker": mode["assignment_count"] // mode["openhcs_worker_count"],
                    "cp_projected_seconds": predicted[i, j],
                    "openhcs_measured_seconds": values(key, scope)[i],
                    "speedup": groups[-1][j][i]})
    labels = [f"{modes[key]['openhcs_worker_count']} {'core' if modes[key]['openhcs_worker_count'] == 1 else 'cores'}\n"
              + f"{modes[key]['assignment_count']} samples\n"
              + f"({modes[key]['assignment_count'] // modes[key]['openhcs_worker_count']} per core)"
              for key in ordered]
    axis = sheet.plot_axes((.12, .23, .85, .18))
    sheet.distributions(axis, groups, labels)
    axis.set_xlabel("Same workload and core count for both applications", labelpad=7)
    sheet.figure.legend(handles=[
        Line2D([], [], marker="o", ls="", color=sheet.scope_colors[0], label="Processing"),
        Line2D([], [], marker="o", ls="", color=sheet.scope_colors[1], label="Setup + processing"),
        *sheet.summary_handles,
    ], loc="lower center", bbox_to_anchor=(.5, .907), ncol=4, frameon=False,
       fontsize=sheet.plot_font_size, borderpad=0, labelspacing=.2,
       title=f"{len(names)} workflows per distribution · OpenHCS medians of 3 runs",
       title_fontsize=sheet.plot_font_size)
    sheet.display_transforms.append({
        "operation": "Paired workflow dots, translucent bars from 1x to the arithmetic mean, median lines and minimum, arithmetic mean, median and maximum values below each distribution; summary row headers give × units; log axes",
        "bar_statistic": "arithmetic mean",
        "bar_baseline": 1.0,
        "reference_lines": {"equal_speed": 1, "speedup_guides": [2, 4, 10]},
        "workflow_count_per_distribution": len(names),
        "single_worker_batch_policy": claims["amortized_policy"],
        "native_policy": claims["native_policy"],
        "matched_core_projection": {
            "formula": "T_CP(N,C) = T_CP(8,first) + (N/C - 8) * median(T_CP(8,warm))/8",
            "total": "Add first-batch pre-pipeline overhead once per concurrent process",
            "assumptions": "Balanced independent one-thread processes; no contention or coordination overhead; external startup excluded",
            "validation_scope": "Serial batches at 8,12,16 samples on three workflows; does not validate parallel scaling or 3-6 samples per process",
            "target_native_observation_count": 0,
        },
        "analysis_rerun": False,
    })
    table_path = OUTPUT / "submission_benchmark_summary_projection.csv"
    with table_path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=tuple(projected_rows[0]))
        writer.writeheader()
        writer.writerows(projected_rows)
    sheet.source(table_path)
    sheet.save(dpi=450)


def build_reference_figures(
    publication_dir: Path, output_dir: Path, *, rebuild_coverage: bool = True,
) -> None:
    """Rebuild the supplied historical chart forms from admitted new sweep rows."""
    from benchmark.reports import cppipe_figures as figures

    publication_dir = publication_dir.resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    include = publication_dir / "benchmark_claims.json"
    claims = json.loads(include.read_text())
    if claims["status"] != "qualified-first-use-sweep":
        raise ValueError("Reference figures require the complete qualified sweep")
    inputs = [include, Path(__file__), Path(figures.__file__)]
    tables = {}
    observations = {}
    source_receipts = []
    for schedule in ("may", "fixed12"):
        directory = publication_dir / schedule / "execution"
        path = directory / "first_use_workflow_metrics.csv"
        receipt_path = directory / "figure2_provenance.json"
        receipt = json.loads(receipt_path.read_text())
        source_receipts.append(receipt)
        if receipt["output_sha256"][path.name] != sha256(path):
            raise ValueError(f"Sweep rows differ from admitted artwork source: {path}")
        inputs.extend((path, receipt_path))
        with path.open(newline="") as stream:
            admitted = tuple(r for r in csv.DictReader(stream)
                             if not r["method"].startswith("CP first batch"))
            for r in admitted:
                key = (r["method"], r["pipeline_name"])
                if key in observations and observations[key] != r:
                    raise ValueError(f"Shared sweep observation disagrees: {key}")
                observations[key] = r
            rows = tuple(figures.BenchmarkMetricRow(
                pipeline_name=r["pipeline_name"], method=r["method"],
                assay_category=r["assay_category"], module_category=r["module_category"],
                accuracy_fraction=float(r["accuracy_fraction"]) if r["accuracy_fraction"] else None,
                raw_seconds=float(r["raw_seconds"]) if r["raw_seconds"] else None,
                speedup=float(r["speedup"]) if r["speedup"] else None,
                peak_memory_mb=None,
            ) for r in admitted)
        tables[schedule] = rows
    rows = tables["may"]
    methods = tuple(dict.fromkeys(row.method for row in rows))
    names = tuple(sorted({row.pipeline_name for row in rows}))
    if len(names) != 30 or any(
        len(condition := tuple(r.pipeline_name for r in rows if r.method == m)) != 30
        or set(condition) != set(names) for m in methods
    ):
        raise ValueError("Each plotted worker condition must contain all thirty workflows")
    outputs = list(figures.FIGURE_STYLE.generate_average_point_figures(
        rows, methods=methods, output_dir=output_dir, output_formats=("png", "svg"),
        filename_stem="reference_core_summary", title="Execution speedup by worker count",
        ylabel="CP first-use reference / OpenHCS", value_key="speedup", target_line=1,
        log_variant=True,
    ))
    # Relabel the admitted observations; the shared painter owns dots and statistics.
    modes = sorted(claims["mode_statistics"].values(),
                   key=lambda m: (m["openhcs_worker_count"], m["assignment_count"]))
    if any(receipt["source_revision"] != source_receipts[0]["source_revision"]
           or receipt["source_sha256"] != source_receipts[0]["source_sha256"]
           for receipt in source_receipts[1:]):
        raise ValueError("Shared sweep observations require identical source provenance")
    combined = {(row.method, row.pipeline_name): row
                for schedule_rows in tables.values() for row in schedule_rows}
    all_methods = {row.method for row in combined.values()}
    if len(all_methods) != 7 or len(combined) != 210 or any(
        {row.pipeline_name for row in combined.values() if row.method == method} != set(names)
        for method in all_methods
    ):
        raise ValueError("Assignment panel requires seven configurations of thirty workflows")
    assignment_labels = {
        m["scope_statistics"]["execution"]["label"]:
        f"{m['openhcs_worker_count']}w × {m['assignment_count'] / m['openhcs_worker_count']:g}/worker\n"
        f"{m['assignment_count']} assignments\n"
        + ("CP measured" if m['native_reference_kind'] == 'measured_first_batch' else "CP projected")
        for m in modes
    }
    assignment_rows = tuple(replace(row, method=assignment_labels[row.method])
                            for row in combined.values())
    outputs.extend(figures.FIGURE_STYLE.generate_average_point_figures(
        assignment_rows, methods=tuple(assignment_labels.values()), output_dir=output_dir,
        output_formats=("png", "svg"), filename_stem="reference_assignments_summary",
        title="Execution speedup by assignments per worker (w = worker)",
        ylabel="CP first-use reference / OpenHCS", value_key="speedup",
        target_line=1, log_variant=True,
    ))
    table = output_dir / "reference_pipeline_metrics.csv"
    figures._write_metric_rows(table, tuple(combined.values()))
    outputs.append(table)
    if rebuild_coverage:
        coverage_inputs, coverage_outputs = build_module_test_coverage(output_dir)
    else:
        # Editorial regeneration must not replace an independently qualified grade.
        retained_path = output_dir / "retained_coverage_provenance.json"
        retained = json.loads(retained_path.read_text())
        coverage_outputs = tuple(output_dir / f"reference_module_coverage.{extension}"
                                 for extension in ("png", "svg", "csv"))
        for path in coverage_outputs:
            if sha256(path) != retained["output_sha256"][path.name]:
                raise ValueError(f"Retained module coverage differs from its record: {path}")
        coverage_inputs = (retained_path,)
    inputs.extend(coverage_inputs)
    outputs.extend(coverage_outputs)
    write_provenance(output_dir, tuple(inputs), tuple(outputs), {
        "source_revision": claims["source_revision"],
        "interpretation": "Old chart forms rebuilt from the new qualified sweep. CP1/8 measured; CP12/16 projected. Seven available configurations only. Agreement is export parity, not biological accuracy. No historical numbers or RAM are substituted.",
    })


def build_module_test_coverage(output_dir: Path) -> tuple[tuple[Path, ...], tuple[Path, ...]]:
    """Paint evidence grades over the existing declaration-owned corpus report."""
    from benchmark.converter.compatibility_matrix import build_cellprofiler_compatibility_report_for_manifest
    from benchmark.reports.cppipe_figures import FIGURE_STYLE

    manifest = ROOT / "benchmark/results/matched_worker_sweep_20261007_exportfixed/protocol/singlewell/official30-manifest.json"
    evidence_path = Path(__file__).with_name("cellprofiler_coverage_evidence.json")
    results_path = output_dir / "coverage_test_results.xml"
    evidence = json.loads(evidence_path.read_text())
    cases = tuple(ET.parse(results_path).getroot().iter("testcase"))
    report = build_cellprofiler_compatibility_report_for_manifest(manifest)
    corpus = set(report.benchmark_coverage.supported_absorbed_processing_modules)
    catalog = {module.module_name for module in report.modules if module.emits_function_step}
    attributed = {}
    inputs = {manifest, evidence_path, results_path}
    inputs.add(Path(inspect.getfile(build_cellprofiler_compatibility_report_for_manifest)))
    inputs.update(Path(inspect.getfile(module.module_type)) for module in report.modules)
    for group in evidence["groups"]:
        for nodeid in group["test_nodeids"]:
            path, name = nodeid.split("::", 1)
            inputs.add(ROOT / path)
            classname = path.removesuffix(".py").replace("/", ".")
            matches = [case for case in cases if case.get("classname") == classname
                       and (case.get("name") == name or case.get("name", "").startswith(name + "["))]
            if not matches or any(any(case.find(tag) is not None for tag in ("failure", "error", "skipped")) for case in matches):
                raise ValueError(f"Coverage behavior is not qualified by passing results: {nodeid}")
        inputs.update(ROOT / path for path in group["owner_sources"])
        for name in group["modules"]:
            if name not in catalog or name in attributed:
                raise ValueError(f"Unknown or duplicate coverage attribution: {name}")
            attributed[name] = group
    # Universal declaration checks are a weaker tier, never algorithm evidence.
    tiers = ("30-workflow corpus", "Module-specific behavior tested", "Shared-path behavior tested",
             "Declaration/import checks only", "No evidence")
    rows = []
    for name in sorted(catalog):
        group = attributed.get(name)
        tier = tiers[0] if name in corpus else tiers[2 if group["shared_only"] else 1] if group else tiers[4]
        rows.append({"module": name, "tier": tier,
                     "behavior": "Declared-output comparison in corpus" if name in corpus else group["behavior"] if group else "No credited passing test",
                     "test_nodeids": "; ".join(group["test_nodeids"]) if group else ""})
    table = output_dir / "reference_module_coverage.csv"
    with table.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=tuple(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    counts = [sum(row["tier"] == tier for row in rows) for tier in tiers]
    colors = ("#007f78", "#4682b4", "#e2a23b", "#969696", "#b2182b")
    with FIGURE_STYLE.context():
        fig, axes = plt.subplots(1, 2, figsize=(10, 4.5), gridspec_kw={"width_ratios": (1, 1.5)}, layout="constrained")
        present = [index for index, count in enumerate(counts) if count]
        axes[0].pie([counts[i] for i in present], colors=[colors[i] for i in present],
                    autopct=lambda pct: f"{pct:.1f}%", startangle=90,
                    textprops={"fontsize": 11}, wedgeprops={"edgecolor": "white"})
        axes[0].set_title(f"{len(catalog)} executable processing modules")
        axes[1].axis("off")
        for index, (tier, count, color) in enumerate(zip(tiers, counts, colors)):
            y = .91 - index * .14
            axes[1].add_patch(plt.Rectangle((0, y - .02), .035, .035, color=color, transform=axes[1].transAxes))
            axes[1].text(.06, y, f"{tier}: {count}", transform=axes[1].transAxes, va="center", fontsize=11)
        shared = [row for row in rows if row["tier"] == tiers[2]]
        axes[1].text(0, .17, "Shared-only: " + ", ".join(row["module"] for row in shared), transform=axes[1].transAxes, fontsize=9)
        axes[1].text(0, .06, "Strongest supported tier per module.\nZero-count tiers have no pie slice; setup modules excluded.", transform=axes[1].transAxes, fontsize=9)
        outputs = [table]
        for extension in ("png", "svg"):
            path = output_dir / f"reference_module_coverage.{extension}"
            FIGURE_STYLE.save(fig, path)
            outputs.append(path)
        plt.close(fig)
    return tuple(sorted(inputs)), tuple(outputs)
