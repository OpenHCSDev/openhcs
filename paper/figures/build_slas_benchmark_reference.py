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

from build_slas_benchmark import ROOT, sha256, write_provenance


def build_reference_figures(publication_dir: Path, output_dir: Path) -> None:
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
    for schedule in ("may", "fixed12"):
        directory = publication_dir / schedule / "execution"
        path = directory / "first_use_workflow_metrics.csv"
        receipt_path = directory / "figure2_provenance.json"
        receipt = json.loads(receipt_path.read_text())
        if receipt["output_sha256"][path.name] != sha256(path):
            raise ValueError(f"Sweep rows differ from admitted artwork source: {path}")
        inputs.extend((path, receipt_path))
        with path.open(newline="") as stream:
            rows = tuple(figures.BenchmarkMetricRow(
                pipeline_name=r["pipeline_name"], method=r["method"],
                assay_category=r["assay_category"], module_category=r["module_category"],
                accuracy_fraction=float(r["accuracy_fraction"]) if r["accuracy_fraction"] else None,
                raw_seconds=float(r["raw_seconds"]) if r["raw_seconds"] else None,
                speedup=float(r["speedup"]) if r["speedup"] else None,
                peak_memory_mb=None,
            ) for r in csv.DictReader(stream) if not r["method"].startswith("CP first batch"))
        tables[schedule] = rows
    rows = tables["may"]
    methods = tuple(dict.fromkeys(row.method for row in rows))
    names = tuple(sorted({row.pipeline_name for row in rows}))
    if len(names) != 30 or any(sum(r.method == m for r in rows) != 30 for m in methods):
        raise ValueError("Each plotted worker condition must contain all thirty workflows")
    labels = {name: name.replace("IlluminationCorrection", "Illum.")
              .replace("Example", "").replace("cp_tutorial_", "")
              .replace("_", " ") for name in names}
    if len(set(labels.values())) != len(names):
        raise ValueError("Shortened pipeline labels must remain unique")
    display_rows = tuple(replace(row, pipeline_name=labels[row.pipeline_name]) for row in rows)
    averages = tuple(replace(next(r for r in rows if r.method == method),
        pipeline_name="Average", speedup=next(
            mode["scope_statistics"]["execution"]["mean"]
            for mode in claims["mode_statistics"].values()
            if method.startswith(f"{mode['openhcs_worker_count']} worker")
            and f" / {mode['assignment_count']} assignments" in method
        )) for method in methods)
    outputs = list(figures.generate_grouped_benchmark_metric_figures(
        (*display_rows, *averages), metrics=(figures.FigureMetricSpec(
            "speedup", "reference_pipeline_speedup", "Execution speedup by pipeline and worker count",
            "CP first-use reference / OpenHCS", baseline_line=1, log_variant=True,
        ),), methods=methods, pipeline_names=(*(labels[name] for name in names), "Average"), output_dir=output_dir,
        wrap_after=16, group_width_inches=.5,
    ))
    parity = tuple(replace(row, method="OpenHCS") for row in display_rows if row.method == methods[0])
    outputs.extend(figures.generate_grouped_benchmark_metric_figures(
        parity, metrics=(figures.FigureMetricSpec(
            "accuracy_fraction", "reference_parity", "Declared-output agreement by pipeline",
            "Declared-output agreement (%)", percentage=True, baseline_line=100, minimum_ylim=0,
        ),), methods=("OpenHCS",), pipeline_names=tuple(labels[name] for name in names), output_dir=output_dir,
        wrap_after=15, group_width_inches=.5,
    ))
    outputs.extend(figures.FIGURE_STYLE.generate_average_point_figures(
        rows, methods=methods, output_dir=output_dir, output_formats=("png", "svg"),
        filename_stem="reference_core_summary", title="Execution speedup by worker count",
        ylabel="CP first-use reference / OpenHCS", value_key="speedup", target_line=1,
        log_variant=True,
    ))
    # The numerical include owns these statistics; this panel only paints them.
    modes = sorted(claims["mode_statistics"].values(),
                   key=lambda m: (m["openhcs_worker_count"], m["assignment_count"]))
    for log_y in (False, True):
        with figures.FIGURE_STYLE.context():
            fig, axis = plt.subplots(figsize=(9, 4.8), layout="constrained")
            positions = np.arange(len(modes))
            summaries = [m["scope_statistics"]["execution"] for m in modes]
            axis.bar(positions, [s["mean"] for s in summaries], label="Mean",
                     color=[figures.FIGURE_STYLE.color_for_method(m["openhcs_worker_count"] - 1) for m in modes])
            axis.scatter(positions, [s["median"] for s in summaries], marker="D", color="#252525", label="Median", zorder=3)
            axis.scatter(positions, [s["minimum"] for s in summaries], marker="v", color="#b2182b", edgecolors="white", label="Minimum", zorder=4)
            axis.axhline(1, color="#b2182b", linestyle="--")
            axis.set_xticks(positions, [
                f"{m['openhcs_worker_count']}w × {m['assignment_count'] / m['openhcs_worker_count']:g}/worker\n"
                f"{m['assignment_count']} assignments\n"
                + ("CP measured" if m['native_reference_kind'] == 'measured_first_batch' else "CP projected")
                for m in modes], fontsize=10)
            axis.set_xlabel("Workers × assignments per worker (w = worker)")
            axis.set(title="Speedup summary by assignments per worker", ylabel="CP first-use reference / OpenHCS")
            if log_y:
                axis.set_yscale("log")
            else:
                axis.set_ylim(bottom=0)
            axis.grid(axis="y", alpha=.25)
            axis.set_axisbelow(True)
            axis.legend(frameon=False, ncol=3)
            for extension in ("png", "svg"):
                path = output_dir / f"reference_assignments_summary{'_log' if log_y else ''}.{extension}"
                figures.FIGURE_STYLE.save(fig, path)
                outputs.append(path)
            plt.close(fig)
    table = output_dir / "reference_pipeline_metrics.csv"
    figures._write_metric_rows(table, rows)
    outputs.append(table)
    coverage_inputs, coverage_outputs = build_module_test_coverage(output_dir)
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
