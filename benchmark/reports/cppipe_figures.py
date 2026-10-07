"""CellProfiler cppipe benchmark figures."""

from __future__ import annotations

import csv
import hashlib
import json
import math
import re
import statistics
from collections.abc import Iterable, Sequence
from contextlib import contextmanager
from dataclasses import dataclass, replace
from functools import cached_property
from pathlib import Path

import matplotlib

matplotlib.use("Agg")

import matplotlib.pyplot as plt
from matplotlib.ticker import FuncFormatter
from matplotlib.ticker import LogLocator
from matplotlib.ticker import NullFormatter
from matplotlib.ticker import NullLocator

from benchmark.contracts.dataset import BenchmarkCategory
from benchmark.datasets.cppipe_case_catalog import DEFAULT_BENCHMARK_CATEGORY
from benchmark.datasets.cppipe_case_catalog import official_cp3_case_category

CASE_NAME_FIELD = "case_name"
ASSAY_CATEGORY_FIELD = "assay_category"
MODULE_CATEGORY_FIELD = "module_category"
NATIVE_SECONDS_FIELD = "median_native_execution_seconds"
OPENHCS_SECONDS_FIELD = "median_openhcs_execution_seconds"
NATIVE_MEMORY_FIELD = "median_native_peak_memory_mb"
OPENHCS_MEMORY_FIELD = "median_openhcs_peak_memory_mb"
SPEEDUP_FIELD = "median_speedup"
ACCURACY_FIELD = "min_parity_accuracy"
CELLPROFILER_LABEL = "CP"
DEFAULT_OPENHCS_LABEL = "OH1"
DEFAULT_FORMATS = ("png", "svg")
DEFAULT_WRAP_AFTER = 14
DEFAULT_GROUP_WIDTH_INCHES = 0.98
SINGLE_PANEL_HEIGHT_INCHES = 4.4
MULTI_PANEL_HEIGHT_INCHES = 7.2
ACCURACY_ZOOM_PANEL_HEIGHT_INCHES = 4.5
GROUPED_BAR_MAX_WIDTH = 0.22
GROUPED_BAR_FRACTION = 0.9
PIPELINE_LABEL_FONT_SIZE = 7.2
PIPELINE_LABEL_WRAP_THRESHOLD = 29
ACCURACY_ZOOM_HALF_RANGE_PERCENT = 0.001
SPEEDUP_TARGET = 2.0
FIGURE_DPI = 360
PIPELINE_NAME_FIELD = "pipeline_name"
METHOD_FIELD = "method"
AGGREGATE_LABEL = "Aggregate"
ACCURACY_FRACTION_FIELD = "accuracy_fraction"
RAW_SECONDS_FIELD = "raw_seconds"
SPEEDUP_METRIC_KEY = "speedup"
PEAK_MEMORY_MB_FIELD = "peak_memory_mb"
SummaryRow = dict[str, str]
SummaryTable = dict[str, SummaryRow]
SummaryTables = Sequence[SummaryTable]


@dataclass(frozen=True)
class SummarySource:
    """One OpenHCS benchmark variant summary CSV."""

    label: str
    path: Path

    @property
    def native_method(self) -> str:
        """Historical variants share their first CellProfiler baseline."""
        return CELLPROFILER_LABEL

    @property
    def candidate_method(self) -> str:
        return self.label

    def native_summary_row(self, pipeline_name: str, row: SummaryRow | None) -> SummaryRow | None:
        return row

    def comparison_speedup(self, row: SummaryRow | None, native: float | None, candidate: float | None) -> float | None:
        return SUMMARY_ROW_NUMERICS.speedup(row, native, candidate)

    def metric_rows(
        self,
        pipeline_name: str,
        row: SummaryRow | None,
        *,
        category_row: SummaryRow | None,
    ) -> tuple[BenchmarkMetricRow, BenchmarkMetricRow]:
        """Derive the paired methods from this source's actual summary row."""
        category = _category_from_summary_row(pipeline_name, row or category_row)
        native_row = self.native_summary_row(pipeline_name, row)
        native_seconds = SUMMARY_ROW_NUMERICS.optional_float(native_row, NATIVE_SECONDS_FIELD)
        openhcs_seconds = SUMMARY_ROW_NUMERICS.optional_float(
            row, OPENHCS_SECONDS_FIELD
        )
        return (
            BenchmarkMetricRow(
                pipeline_name=pipeline_name,
                method=self.native_method,
                assay_category=category.assay,
                module_category=category.module,
                accuracy_fraction=1.0,
                raw_seconds=native_seconds,
                speedup=1.0,
                peak_memory_mb=SUMMARY_ROW_NUMERICS.optional_float(
                    native_row, NATIVE_MEMORY_FIELD
                ),
            ),
            BenchmarkMetricRow(
                pipeline_name=pipeline_name,
                method=self.candidate_method,
                assay_category=category.assay,
                module_category=category.module,
                accuracy_fraction=SUMMARY_ROW_NUMERICS.optional_float(
                    row, ACCURACY_FIELD
                ),
                raw_seconds=openhcs_seconds,
                speedup=self.comparison_speedup(row, native_seconds, openhcs_seconds),
                peak_memory_mb=SUMMARY_ROW_NUMERICS.optional_float(
                    row, OPENHCS_MEMORY_FIELD
                ),
            ),
        )


@dataclass(frozen=True)
class MeasuredBatchSummarySource(SummarySource):
    """An actual batch comparison with its own measured native baseline."""

    @property
    def native_method(self) -> str:
        counts = {case["mode"]["native_job_count"] for case in self.qualified_custody()["cases"]}
        if len(counts) != 1:
            raise ValueError("Measured mode must have one declared CP process count")
        count = counts.pop()
        return f"CP ({self.label})" if count == 1 else f"CP ({self.label}; {count} independent processes; calibration)"

    @property
    def candidate_method(self) -> str:
        return f"OH ({self.label})"

    @property
    def comparison_description(self) -> str:
        return "CP parallel timings are an external independent-process calibration, not a built-in CellProfiler feature."

    @property
    def custody_path(self) -> Path:
        return self.path.parent / "summary_custody.json"

    def qualified_custody(self) -> dict:
        """The original converter, not publication, qualifies observations."""
        custody = json.loads(self.custody_path.read_text())
        if custody["status"] != "PASS":
            raise ValueError("Measured publication requires qualified matched custody")
        return custody

    @cached_property
    def clock_scope(self) -> str:
        """Identify the converter's clock from its actual qualified observations."""
        table = _load_summary_table(self)
        cases = {case["case"]: case for case in self.qualified_custody()["cases"]}
        matches = []
        for scope in ("execution", "total"):
            if all(
                math.isclose(float(row[field]), statistics.median(
                    observation[f"{engine}_{scope}_seconds"]
                    for observation in cases[name]["rows"]
                ), rel_tol=1e-12, abs_tol=1e-12)
                for name, row in table.items()
                for engine, field in (("native", NATIVE_SECONDS_FIELD), ("openhcs", OPENHCS_SECONDS_FIELD))
            ):
                matches.append(scope)
        if len(matches) != 1:
            raise ValueError("Measured summary must identify one qualified clock scope")
        return matches[0]

    def retained_manifest_path(self) -> Path:
        """Bind the archived declaration to the converter's original digest."""
        declaration = self.qualified_custody()["manifest"]
        original = Path(declaration["path"])
        protocol = self.path.parents[2] / "protocol"
        # Archive placement differs by record; the original name and digest own identity.
        retained = tuple(sorted(path for path in protocol.rglob(original.name)
                                if hashlib.sha256(path.read_bytes()).hexdigest() == declaration["sha256"]))
        if not retained:
            raise ValueError(f"Original qualified manifest is not retained under {protocol}: {original.name}")
        return retained[0]

    def publication_values(
        self, total: MeasuredBatchSummarySource, *, record_name: str, frozen: bool,
    ) -> dict[str, str]:
        """One projection supplies every manuscript and caption claim.

        A qualified capture is not an owner's final publication freeze. Until
        that explicit freeze, numeric claims remain placeholders even though
        checkpoint figures can show the saved observations.
        """
        custody = self.qualified_custody()
        if total.qualified_custody()["source_head"] != custody["source_head"]:
            raise ValueError("Execution and total claims require the same source revision")
        tables = (_load_summary_table(self), _load_summary_table(total))
        if set(tables[0]) != set(tables[1]):
            raise ValueError("Execution and total claims require the same pipeline cohort")
        values = {
            "record_name": record_name,
            "source_revision": custody["source_head"],
            "status": "frozen" if frozen else "pending-final-freeze",
            "case_count": str(len(tables[0])),
        }
        for scope, source, table in zip(("execution", "total"), (self, total), tables, strict=True):
            ratios = tuple(source.metric_rows(name, row, category_row=row)[1].speedup for name, row in table.items())
            if any(value is None or not math.isfinite(value) or value <= 0 for value in ratios):
                raise ValueError("Publication requires positive finite speedups for every case")
            statistics = SpeedupSummaryStatistics.from_series(
                SpeedupDistributionSeries(source.candidate_method, ratios)
            )
            if statistics is None or statistics.sample_count != len(table):
                raise ValueError("Publication statistics must include the complete qualified cohort")
            values[scope + "_min"] = f"{statistics.minimum:.3f}" if frozen else "PENDING"
            values[scope + "_median"] = f"{statistics.median:.3f}" if frozen else "PENDING"
        return values

    def publication_figure(
        self, total: MeasuredBatchSummarySource, *, output_dir: Path,
        output_formats: Sequence[str] = DEFAULT_FORMATS,
    ) -> tuple[Path, ...]:
        """Present both qualified clocks through the original May painter."""
        self.publication_values(total, record_name=output_dir.name, frozen=False)
        methods = ("Execution", "Compile + execution total")
        rows = tuple(
            replace(source.metric_rows(name, row, category_row=row)[1], method=method)
            for method, source in zip(methods, (self, total), strict=True)
            for name, row in _load_summary_table(source).items()
        )
        return FIGURE_STYLE.generate_average_point_figures(
            rows, methods=methods,
            output_dir=output_dir, output_formats=output_formats,
            filename_stem="measured_benchmark_publication",
            title=f"Matched speedups across {len(rows) // 2} imported workflows",
            ylabel="CellProfiler / OpenHCS speedup", value_key="speedup",
            target_line=1.0, log_variant=True, font_scale=1.25,
        )

    def paired_runtime_figure(
        self, total: MeasuredBatchSummarySource, *, output_dir: Path,
        output_formats: Sequence[str] = DEFAULT_FORMATS,
    ) -> tuple[Path, ...]:
        """Show each qualified workflow's paired clocks and measured speedup."""
        # The same owner validates matching revision/cohort and every ratio.
        self.publication_values(total, record_name=output_dir.name, frozen=False)
        execution_table, total_table = _load_summary_table(self), _load_summary_table(total)
        passed = sum(SUMMARY_ROW_NUMERICS.optional_float(row, ACCURACY_FIELD) == 1.0
                     for row in execution_table.values())
        count = len(execution_table)
        names = tuple(sorted(execution_table))
        labels = tuple(PIPELINE_LABEL_LAYOUT.split_label(name) for name in names)
        positions = []
        cursor = 0.0
        for label in labels:
            height = 1.0 + .8 * label.count("\n")
            positions.append(cursor + height / 2)
            cursor += height
        with FIGURE_STYLE.context():
            fig, axes = plt.subplots(1, 2, figsize=(8.0, 9.5), sharey=True)
            fig.subplots_adjust(left=.34, right=.94, top=.87, bottom=.07, wspace=.31)
            fig.suptitle("Matched CellProfiler and OpenHCS runtimes", x=.04, y=.985,
                         ha="left", fontsize=14, fontweight="bold")
            fig.text(.04, .956, f"{passed}/{count} workflows passed declared-output comparisons",
                     fontsize=10)
            fig.text(.04, .930, "One worker · one numerical thread · medians of three measured runs",
                     fontsize=9.5)
            fig.legend(handles=[
                matplotlib.patches.Patch(color=FIGURE_STYLE.color_for_method(0), label="CellProfiler"),
                matplotlib.patches.Patch(color=FIGURE_STYLE.color_for_method(1), label="OpenHCS"),
            ], loc="upper left", bbox_to_anchor=(.035, .916), ncol=2, frameon=False,
                       fontsize=10)
            smallest = min(float(row[field]) for table in (execution_table, total_table)
                           for row in table.values()
                           for field in (NATIVE_SECONDS_FIELD, OPENHCS_SECONDS_FIELD))
            largest = max(float(row[field]) for table in (execution_table, total_table)
                          for row in table.values()
                          for field in (NATIVE_SECONDS_FIELD, OPENHCS_SECONDS_FIELD))
            limits = (10 ** math.floor(math.log10(smallest)),
                      10 ** math.ceil(math.log10(largest)))
            for axis, scope, source, table, letter in zip(
                axes, ("execution", "total"), (self, total),
                (execution_table, total_table), ("A", "B"), strict=True,
            ):
                ratios = tuple(source.metric_rows(name, table[name], category_row=table[name])[1].speedup
                               for name in names)
                for method_index, field in enumerate((NATIVE_SECONDS_FIELD, OPENHCS_SECONDS_FIELD)):
                    axis.barh([position + (method_index - .5) * .32 for position in positions],
                              [float(table[name][field]) for name in names], height=.29,
                              color=FIGURE_STYLE.color_for_method(method_index), zorder=3)
                axis.set_xscale("log")
                axis.set_xlim(*limits)
                axis.set_ylim(cursor, 0)
                axis.set_yticks(positions, labels)
                axis.tick_params(axis="y", length=0, labelsize=8.8, pad=8)
                axis.tick_params(axis="x", labelsize=9)
                axis.xaxis.set_major_formatter(FuncFormatter(_plain_log_tick_label))
                axis.grid(axis="x", color=FIGURE_STYLE.grid_color, zorder=0)
                axis.spines[["top", "right", "left"]].set_visible(False)
                axis.set_title(f"{letter}  {scope.title()} time", loc="left", fontsize=11, pad=28)
                axis.set_xlabel("Seconds (log scale)", fontsize=10)
                axis.text(.0, 1.01, "CellProfiler / OpenHCS speedup →", transform=axis.transAxes,
                          fontsize=8.5)
                for position, ratio in zip(positions, ratios, strict=True):
                    axis.text(1.03, position, f"{ratio:.2f}×", transform=axis.get_yaxis_transform(),
                              va="center", fontsize=8.5)
            outputs = tuple(output_dir / f"measured_benchmark_workflow_runtimes.{extension}" for extension in output_formats)
            for path in outputs:
                FIGURE_STYLE.save(fig, path)
            plt.close(fig)
        return outputs

    def assignment_speedup_rows(self) -> tuple[dict[str, object], ...]:
        """Project actual assignments and clocks through this source's baseline."""
        if self.clock_scope != "total":
            raise ValueError("Assignment response uses qualified total-clock summaries")
        custody = self.qualified_custody()
        table = _load_summary_table(self)
        rows = []
        for case in custody["cases"]:
            name, mode = case["case"], case["mode"]
            native, candidate = self.metric_rows(name, table[name], category_row=table[name])
            rows.append({
                "workflow": name, "assignments": len(mode["wells"]),
                "workers": mode["candidate_worker_count"],
                "source_revision": custody["source_head"],
                "assignment_scope": mode["assignment_scope"],
                "native_total_seconds": native.raw_seconds,
                "openhcs_total_seconds": candidate.raw_seconds,
                "total_speedup": candidate.speedup,
                "summary_source": str(self.path),
            })
        return tuple(rows)

    def amortization_points(self, pipeline_name: str) -> tuple[int, dict[str, float]]:
        """Derive single-core per-assignment clocks from qualified paired observations."""
        custody = self.qualified_custody()
        cases = tuple(case for case in custody["cases"] if case["case"] == pipeline_name)
        if len(cases) != 1:
            raise ValueError(f"Custody must own exactly one case {pipeline_name!r}")
        case = cases[0]
        mode = case["mode"]
        count = len(mode["wells"])
        if count < 1 or len(set(mode["wells"])) != count:
            raise ValueError("Amortization assignment identities must be nonempty and unique")
        if mode["candidate_worker_count"] != 1 or mode["native_job_count"] != 1:
            raise ValueError("Amortization is a single-worker/single-native-job comparison")
        if case["source_commit"] != custody["source_head"]:
            raise ValueError("Amortization case source differs from qualified custody")
        if len(case["native_environment"]["cpu_affinity"]) != 1:
            raise ValueError("Single-core amortization requires one actual native CPU")
        observations = case["rows"]
        if tuple(row["repetition"] for row in observations) != (0, 1, 2):
            raise ValueError("Amortization requires three measured paired repetitions")
        values = {
            "OH execution": statistics.median(row["openhcs_execution_seconds"] for row in observations),
            "OH total": statistics.median(row["openhcs_total_seconds"] for row in observations),
            "OH non-execution": statistics.median(
                row["openhcs_total_seconds"] - row["openhcs_execution_seconds"]
                for row in observations
            ),
            "CP total": statistics.median(row["native_total_seconds"] for row in observations),
        }
        if any(not math.isfinite(value) or value < 0 for value in values.values()):
            raise ValueError("Amortization clocks must be finite and nonnegative")
        row = _load_summary_table(self)[pipeline_name]
        if not math.isclose(float(row[OPENHCS_SECONDS_FIELD]), values["OH execution"], abs_tol=1e-9):
            raise ValueError("Amortization source must be the custody-owned execution summary")
        return count, {key: value / count for key, value in values.items()}


@dataclass(frozen=True)
class SerialCellProfilerBatchSummarySource(MeasuredBatchSummarySource):
    """Built-in OpenHCS workers compared with one measured stock CP process."""

    baseline: MeasuredBatchSummarySource

    @property
    def native_method(self) -> str:
        return "CP (one process)"

    @property
    def comparison_description(self) -> str:
        return "Primary comparison: one stock CellProfiler process versus OpenHCS built-in workers on the same assignments."

    @cached_property
    def baseline_table(self) -> SummaryTable:
        custody, baseline = self.qualified_custody(), self.baseline.qualified_custody()
        if self.clock_scope != self.baseline.clock_scope:
            raise ValueError("Serial baseline must use the same qualified clock scope")
        if custody["source_head"] != baseline["source_head"] or custody["manifest"]["sha256"] != baseline["manifest"]["sha256"]:
            raise ValueError("Serial baseline must share qualified source and pipeline declarations")
        baseline_cases = {case["case"]: case for case in baseline["cases"]}
        for case in custody["cases"]:
            reference = baseline_cases[case["case"]]
            mode, reference_mode = case["mode"], reference["mode"]
            if reference_mode["native_job_count"] != 1:
                raise ValueError("Primary CellProfiler baseline must be one actual process")
            for field in ("wells", "selected_source_wells", "assignment_scope"):
                if mode[field] != reference_mode[field]:
                    raise ValueError(f"Serial baseline assignment scope differs: {field}")
        return _load_summary_table(self.baseline)

    def native_summary_row(self, pipeline_name: str, row: SummaryRow | None) -> SummaryRow:
        return self.baseline_table[pipeline_name]

    def comparison_speedup(self, row: SummaryRow | None, native: float | None, candidate: float | None) -> float | None:
        # The saved speedup belongs to the original matched parallel calibration.
        return None if native is None or candidate is None or candidate <= 0 else native / candidate


@dataclass(frozen=True)
class BenchmarkMetricRow:
    """Long-form metric values for one method on one pipeline."""

    pipeline_name: str
    method: str
    assay_category: str
    module_category: str
    accuracy_fraction: float | None
    raw_seconds: float | None
    speedup: float | None
    peak_memory_mb: float | None


@dataclass(frozen=True)
class FigureMetricSpec:
    """One grouped-bar chart projection."""

    key: str
    filename_stem: str
    title: str
    ylabel: str
    percentage: bool = False
    baseline_line: float | None = None
    target_line: float | None = None
    minimum_ylim: float | None = None
    log_variant: bool = False
    use_axis_break: bool = True


@dataclass(frozen=True)
class SummaryRowNumerics:
    """Typed numeric access to benchmark summary CSV rows."""

    speedup_field: str = SPEEDUP_FIELD

    def optional_float(
        self,
        row: dict[str, str] | None,
        field_name: str,
    ) -> float | None:
        if row is None:
            return None
        value = row.get(field_name)
        if value is None or value == "":
            return None
        numeric = float(value)
        return numeric if math.isfinite(numeric) else None

    def speedup(
        self,
        row: dict[str, str] | None,
        native_seconds: float | None,
        openhcs_seconds: float | None,
    ) -> float | None:
        explicit_speedup = self.optional_float(row, self.speedup_field)
        if explicit_speedup is not None:
            return explicit_speedup
        if native_seconds is None or openhcs_seconds is None or openhcs_seconds <= 0.0:
            return None
        return native_seconds / openhcs_seconds

    def speedup_from_summary_row(self, row: SummaryRow | None) -> float | None:
        if row is None:
            return None
        speedup = self.optional_float(row, self.speedup_field)
        if speedup is not None:
            return speedup
        return self.speedup(
            row,
            self.optional_float(row, NATIVE_SECONDS_FIELD),
            self.optional_float(row, OPENHCS_SECONDS_FIELD),
        )


@dataclass(frozen=True)
class BenchmarkMetricProjection:
    """Metric-specific projection from long-form rows to plot values."""

    def value(
        self,
        row: BenchmarkMetricRow | None,
        metric: FigureMetricSpec,
    ) -> float | None:
        if row is None:
            return None
        value = getattr(row, metric.key)
        if value is None:
            return None
        return float(value) * 100.0 if metric.percentage else float(value)

    def plot_value(self, value: float | None) -> float:
        return math.nan if value is None else value


@dataclass(frozen=True)
class PipelineLabelLayout:
    """Owns panel partitioning and readable pipeline tick labels."""

    wrap_threshold: int = PIPELINE_LABEL_WRAP_THRESHOLD

    def panels(
        self,
        pipeline_names: Sequence[str],
        wrap_after: int,
    ) -> tuple[tuple[str, ...], ...]:
        if wrap_after <= 0 or len(pipeline_names) <= wrap_after:
            return (tuple(pipeline_names),)
        split = math.ceil(len(pipeline_names) / 2)
        return (tuple(pipeline_names[:split]), tuple(pipeline_names[split:]))

    def split_label(self, label: str) -> str:
        tokens = self._tokens(label)
        if len(tokens) < 2 or len(" ".join(tokens)) < self.wrap_threshold:
            return label
        split_at = min(
            range(1, len(tokens)),
            key=lambda index: self._split_cost(tokens, index),
        )
        return f"{' '.join(tokens[:split_at])}\n{' '.join(tokens[split_at:])}"

    @staticmethod
    def _split_cost(tokens: Sequence[str], index: int) -> tuple[int, int]:
        left_length = len(" ".join(tokens[:index]))
        right_length = len(" ".join(tokens[index:]))
        return max(left_length, right_length), abs(left_length - right_length)

    @staticmethod
    def _tokens(label: str) -> tuple[str, ...]:
        spaced = label.replace("_", " ")
        tokens: list[str] = []
        for part in spaced.split():
            tokens.extend(
                token
                for token in re.findall(
                    r"[A-Z]?[a-z]+|[A-Z]+(?=[A-Z][a-z]|\b)|\d+",
                    part,
                )
                if token
            )
        return tuple(tokens) or (label,)


@dataclass(frozen=True)
class GroupedFigureRequest:
    """Shared request context for grouped benchmark figure panels."""

    rows: Sequence[BenchmarkMetricRow]
    methods: Sequence[str]
    pipeline_names: Sequence[str]
    output_dir: Path
    output_formats: Sequence[str]
    wrap_after: int
    group_width_inches: float


@dataclass(frozen=True)
class BenchmarkFigureStyle:
    """Publication-oriented styling for CellProfiler benchmark figures."""

    method_colors: tuple[str, ...] = (
        "#252525",
        "#007f7f",
        "#d95f02",
        "#1b9e77",
        "#7570b3",
    )
    background: str = "#fbfaf7"
    grid_color: str = "#dad4c7"
    spine_color: str = "#5c554b"
    text_color: str = "#252525"
    target_color: str = "#b2182b"
    baseline_color: str = "#5c554b"

    @contextmanager
    def context(self):
        with plt.rc_context(self.rc_params):
            yield

    @property
    def rc_params(self) -> dict[str, object]:
        return {
            "figure.facecolor": self.background,
            "axes.facecolor": self.background,
            "axes.edgecolor": self.spine_color,
            "axes.labelcolor": self.text_color,
            "axes.titlecolor": self.text_color,
            "xtick.color": self.text_color,
            "ytick.color": self.text_color,
            "text.color": self.text_color,
            "font.family": "DejaVu Sans",
            "axes.titleweight": "bold",
            "axes.titlesize": 12,
            "axes.labelsize": 9.5,
            "legend.fontsize": 8.5,
            "xtick.labelsize": PIPELINE_LABEL_FONT_SIZE,
            "ytick.labelsize": 8.5,
            "savefig.facecolor": self.background,
            "savefig.edgecolor": self.background,
        }

    def color_for_method(self, method_index: int) -> str:
        return self.method_colors[method_index % len(self.method_colors)]

    def decorate_axis(
        self, axis, *, metric: FigureMetricSpec, panel_index: int
    ) -> None:
        axis.grid(axis="y", color=self.grid_color, linewidth=0.8, alpha=0.8)
        axis.set_axisbelow(True)
        axis.spines["top"].set_visible(False)
        axis.spines["right"].set_visible(False)
        axis.spines["left"].set_color(self.spine_color)
        axis.spines["bottom"].set_color(self.spine_color)
        if panel_index == 0:
            axis.set_title(metric.title, loc="left", pad=10)

    def save(self, fig, output_path: Path) -> None:
        fig.savefig(output_path, dpi=FIGURE_DPI, bbox_inches="tight")

    def generate_average_point_figures(
        self,
        rows: Sequence["BenchmarkMetricRow"],
        *,
        methods: Sequence[str],
        output_dir: Path,
        output_formats: Sequence[str],
        filename_stem: str,
        title: str,
        ylabel: str,
        value_key: str,
        target_line: float | None = None,
        log_variant: bool,
        font_scale: float = 1.0,
    ) -> tuple[Path, ...]:
        """Plot mean bars with all per-pipeline points for each method."""
        import matplotlib.pyplot as plt
        from matplotlib.ticker import (
            FuncFormatter,
            LogLocator,
            NullFormatter,
            NullLocator,
        )

        method_values = tuple(
            (
                method,
                tuple(
                    float(value)
                    for row in rows
                    if row.method == method
                    and (value := getattr(row, value_key)) is not None
                ),
            )
            for method in methods
        )
        values = tuple(
            value
            for _method, method_values_ in method_values
            for value in method_values_
        )
        if not values:
            return ()
        value_suffix = " MB" if value_key == "peak_memory_mb" else "x"
        outputs: list[Path] = []
        for log_y in (False, True) if log_variant else (False,):
            broken_range = (
                None
                if log_y or value_key == "peak_memory_mb"
                else LINEAR_AXIS_BREAK_POLICY.range_for(values)
            )
            with self.context():
                plt.rcParams.update({key: float(value) * font_scale
                                     for key, value in self.rc_params.items()
                                     if key.endswith("size") and isinstance(value, (int, float))})
                if broken_range is None:
                    fig, axis = plt.subplots(
                        1,
                        1,
                        figsize=(max(5.6, 1.45 * len(method_values) + 3.2), 4.6),
                        layout="constrained",
                    )
                    axes = (axis,)
                else:
                    fig, axes_ = plt.subplots(
                        2,
                        1,
                        figsize=(max(5.6, 1.45 * len(method_values) + 3.2), 5.6),
                        gridspec_kw={"height_ratios": (1.0, 3.2)},
                        sharex=True,
                        layout="constrained",
                    )
                    top_axis, bottom_axis = tuple(axes_)
                    top_axis.set_ylim(broken_range[1], broken_range[2])
                    bottom_axis.set_ylim(0.0, broken_range[0])
                    LINEAR_AXIS_BREAK_POLICY.mark(top_axis, bottom_axis)
                    axes = (top_axis, bottom_axis)
                x_positions = tuple(range(len(method_values)))
                if log_y:
                    for axis in axes:
                        axis.set_yscale("log")
                        axis.yaxis.set_major_locator(LogLocator(base=10.0, numticks=6))
                        axis.yaxis.set_minor_locator(NullLocator())
                        axis.yaxis.set_major_formatter(
                            FuncFormatter(_plain_log_tick_label)
                        )
                        axis.yaxis.set_minor_formatter(NullFormatter())
                if target_line is not None:
                    for axis in axes:
                        axis.axhline(
                            target_line,
                            color=self.target_color,
                            linewidth=1.15,
                            linestyle="--",
                            alpha=0.86,
                        )
                    target_axis = next(
                        (
                            axis
                            for axis in axes
                            if axis.get_ylim()[0] <= target_line <= axis.get_ylim()[1]
                        ),
                        axes[-1],
                    )
                    target_axis.annotate(
                        f"{target_line:g}x",
                        xy=(-0.012, target_line),
                        xycoords=("axes fraction", "data"),
                        xytext=(-2, 3),
                        textcoords="offset points",
                        ha="right",
                        va="bottom",
                        fontsize=7.8 * font_scale,
                        color=self.target_color,
                        annotation_clip=False,
                    )

                def visible_axis_for(value: float):
                    return next(
                        (
                            axis
                            for axis in axes
                            if axis.get_ylim()[0] <= value <= axis.get_ylim()[1]
                        ),
                        None,
                    )

                def annotate_value(
                    *,
                    x: float,
                    value: float,
                    text: str,
                    x_offset: float = 4.0,
                    y_offset: float = 0.0,
                    ha: str = "left",
                    va: str = "center",
                    color: str | None = None,
                    weight: str = "normal",
                ) -> None:
                    axis = visible_axis_for(value)
                    if axis is None:
                        return
                    axis.annotate(
                        text,
                        xy=(x, value),
                        xytext=(x_offset, y_offset),
                        textcoords="offset points",
                        ha=ha,
                        va=va,
                        fontsize=6.2 * font_scale,
                        color=color or self.text_color,
                        fontweight=weight,
                        bbox={
                            "boxstyle": "round,pad=0.08",
                            "facecolor": self.background,
                            "edgecolor": "none",
                            "alpha": 0.72,
                        },
                        clip_on=True,
                        zorder=6,
                    )

                def adjusted_label_values(
                    axis,
                    stats: Sequence[tuple[str, float, str]],
                    *,
                    min_gap_points: float = 11.0,
                    edge_padding_points: float = 5.0,
                ) -> tuple[tuple[str, float, str], ...]:
                    """Return stat label y-values adjusted to avoid text collisions."""
                    if not stats:
                        return ()
                    renderer = fig.canvas.get_renderer()
                    points_to_pixels = renderer.points_to_pixels
                    min_gap_pixels = points_to_pixels(min_gap_points)
                    edge_padding_pixels = points_to_pixels(edge_padding_points)
                    axis_min = axis.bbox.y0 + edge_padding_pixels
                    axis_max = axis.bbox.y1 - edge_padding_pixels

                    positioned = sorted(
                        (
                            (
                                label,
                                value,
                                weight,
                                axis.transData.transform((0.0, value))[1],
                            )
                            for label, value, weight in stats
                        ),
                        key=lambda item: item[3],
                    )
                    adjusted_pixels: list[float] = []
                    for _label, _value, _weight, original_pixels in positioned:
                        adjusted_pixels.append(
                            max(
                                original_pixels,
                                (
                                    adjusted_pixels[-1] + min_gap_pixels
                                    if adjusted_pixels
                                    else axis_min
                                ),
                            )
                        )
                    if adjusted_pixels[-1] > axis_max:
                        adjusted_pixels[-1] = axis_max
                    for index in range(len(adjusted_pixels) - 2, -1, -1):
                        adjusted_pixels[index] = min(
                            adjusted_pixels[index],
                            adjusted_pixels[index + 1] - min_gap_pixels,
                        )
                    for index in range(1, len(adjusted_pixels)):
                        adjusted_pixels[index] = max(
                            adjusted_pixels[index],
                            adjusted_pixels[index - 1] + min_gap_pixels,
                        )

                    return tuple(
                        (
                            label,
                            axis.transData.inverted().transform(
                                (0.0, adjusted_pixels[index])
                            )[1],
                            weight,
                        )
                        for index, (label, _value, weight, _pixels) in enumerate(
                            positioned
                        )
                    )

                def annotate_stat_labels(
                    *,
                    method_index: int,
                    color: str,
                    stats: Sequence[tuple[str, float, str]],
                ) -> None:
                    label_x = method_index - 0.30
                    for axis in axes:
                        visible_stats = tuple(
                            (label, value, weight)
                            for label, value, weight in stats
                            if axis.get_ylim()[0] <= value <= axis.get_ylim()[1]
                        )
                        for label, label_value, weight in adjusted_label_values(
                            axis, visible_stats
                        ):
                            annotate_value(
                                x=label_x,
                                value=label_value,
                                text=label,
                                x_offset=-3.0,
                                y_offset=0.0,
                                ha="right",
                                va="center",
                                color=color,
                                weight=weight,
                            )

                stat_label_groups: list[
                    tuple[int, str, tuple[tuple[str, float, str], ...]]
                ] = []
                for method_index, (_method, values_) in enumerate(method_values):
                    if not values_:
                        continue
                    if value_key == "speedup":
                        summary = SpeedupSummaryStatistics.from_series(
                            SpeedupDistributionSeries(_method, values_)
                        )
                        assert summary is not None
                        mean, median = summary.mean, summary.median
                        minimum, maximum = summary.minimum, summary.maximum
                    else:
                        # Memory is a different metric: preserve zero observations.
                        mean, median = statistics.mean(values_), statistics.median(values_)
                        minimum, maximum = min(values_), max(values_)
                    color = self.color_for_method(method_index + 1)
                    stat_label_groups.append(
                        (
                            method_index,
                            color,
                            ((f"all {mean:.1f}{value_suffix}", mean, "bold"),) if len(values_) == 1 else (
                                (f"min {minimum:.1f}{value_suffix}", minimum, "normal"),
                                (f"med {median:.1f}{value_suffix}", median, "normal"),
                                (f"mean {mean:.1f}{value_suffix}", mean, "bold"),
                                (f"max {maximum:.1f}{value_suffix}", maximum, "normal"),
                            ),
                        )
                    )
                    point_x = tuple(
                        method_index + _deterministic_jitter(index, len(values_))
                        for index in range(len(values_))
                    )
                    for axis in axes:
                        axis.bar(
                            [method_index],
                            [mean],
                            width=0.62,
                            color=color,
                            alpha=0.72,
                            edgecolor=self.background,
                            linewidth=0.55,
                        )
                        axis.scatter(
                            point_x,
                            values_,
                            s=28,
                            color=self.text_color,
                            alpha=0.58,
                            zorder=3,
                        )
                        axis.hlines(
                            median,
                            method_index - 0.31,
                            method_index + 0.31,
                            color=self.text_color,
                            linewidth=1.35,
                            zorder=4,
                            label=(
                                "Median"
                                if method_index == 0 and axis is axes[0]
                                else None
                            ),
                        )
                        axis.grid(
                            axis="y",
                            color=self.grid_color,
                            linewidth=0.8,
                            alpha=0.8,
                        )
                        axis.set_axisbelow(True)
                        axis.spines["top"].set_visible(False)
                        axis.spines["right"].set_visible(False)
                        axis.spines["left"].set_color(self.spine_color)
                        axis.spines["bottom"].set_color(self.spine_color)
                label_axis = axes[-1]
                for axis in axes:
                    axis.set_xlim(-0.80, len(method_values) - 0.48)
                label_axis.set_xticks(list(x_positions))
                label_axis.set_xticklabels(
                    [method for method, _values in method_values]
                )
                label_axis.set_ylabel(ylabel)
                axes[0].set_title(
                    title + (" (log)" if log_y else ""), loc="left", pad=10
                )
                fig.legend(frameon=False, loc="outside lower center")
                fig.canvas.draw()
                for method_index, color, stats in stat_label_groups:
                    annotate_stat_labels(
                        method_index=method_index,
                        color=color,
                        stats=stats,
                    )
                suffix = "_log" if log_y else ""
                for output_format in output_formats:
                    output_path = (
                        output_dir / f"{filename_stem}{suffix}.{output_format}"
                    )
                    self.save(fig, output_path)
                    outputs.append(output_path)
                plt.close(fig)
        return tuple(outputs)

    def decorate_legend(self, axis) -> None:
        """Keep grouped method identities outside the measured bar domain."""
        axis.legend(frameon=False, loc="upper left", bbox_to_anchor=(1.02, 1.0))

    def generate_assignment_speedup_figures(
        self, sources: Sequence[MeasuredBatchSummarySource], *,
        output_dir: Path, output_formats: Sequence[str] = DEFAULT_FORMATS,
    ) -> tuple[Path, ...]:
        """Keep each workflow, worker configuration and revision distinct."""
        rows = tuple(row for source in sources for row in source.assignment_speedup_rows())
        names = tuple(sorted({row["workflow"] for row in rows if row["assignments"] > 1}))
        rows = tuple(row for row in rows if row["workflow"] in names)
        keys = tuple(dict.fromkeys((row["source_revision"], row["workers"]) for row in rows))
        revisions = tuple(dict.fromkeys(revision for revision, _workers in keys))
        worker_counts = tuple(sorted({workers for _revision, workers in keys}))
        markers = dict(zip(worker_counts, ("o", "^", "s", "D"), strict=False))
        output_dir.mkdir(parents=True, exist_ok=True)
        table_path = output_dir / "assignment_total_speedups.csv"
        with table_path.open("w", newline="", encoding="utf-8") as stream:
            writer = csv.DictWriter(stream, fieldnames=tuple(rows[0]))
            writer.writeheader()
            writer.writerows(rows)
        with self.context():
            fig, axes = plt.subplots(len(names), 2, figsize=(8.2, 10.5), squeeze=False)
            fig.subplots_adjust(left=.11, right=.98, top=.91, bottom=.20, hspace=.55, wspace=.36)
            fig.suptitle("Total speedup versus assigned samples", x=.11, y=.99,
                         ha="left", fontsize=14, fontweight="bold")
            fig.text(.11, .955, "Each workflow shown separately; actual one-process CellProfiler baseline",
                     fontsize=9)
            handles = {}
            for index, name in enumerate(names):
                for column, axis in enumerate(axes[index]):
                    for revision, workers in keys:
                        points = sorted((row for row in rows if row["workflow"] == name
                                         and row["source_revision"] == revision and row["workers"] == workers),
                                        key=lambda row: row["assignments"])
                        if not points:
                            continue
                        label = f"{revision[:9]} · {workers} worker{'s' if workers != 1 else ''}"
                        line, = axis.plot([row["assignments"] for row in points],
                                          [row["total_speedup"] for row in points],
                                          marker=markers[workers], markersize=6,
                                          linestyle="-" if len(points) > 1 else "none",
                                          color=self.color_for_method(revisions.index(revision) + 1),
                                          markerfacecolor="white" if workers == 1 else None,
                                          linewidth=1.4, label=label)
                        handles[label] = line
                    axis.axhline(1, linestyle="--", color=self.target_color, linewidth=.8)
                    if column:
                        axis.set_yscale("log")
                        axis.yaxis.set_major_locator(LogLocator(base=10, subs=(1, 2, 3, 5)))
                        axis.yaxis.set_major_formatter(FuncFormatter(_plain_log_tick_label))
                        axis.yaxis.set_minor_formatter(NullFormatter())
                    else:
                        axis.set_ylim(bottom=0)
                    axis.set_xticks(sorted({row["assignments"] for row in rows}))
                    axis.set_xlim(0, max(row["assignments"] for row in rows) + 1)
                    axis.grid(axis="y", color=self.grid_color)
                    axis.spines[["top", "right"]].set_visible(False)
                    axis.set_title(f"{chr(65 + index)}{column + 1}  {PIPELINE_LABEL_LAYOUT.split_label(name)}",
                                   loc="left", fontsize=10)
                    axis.set_ylabel("Total speedup" + (" (log)" if column else ""), fontsize=9)
                    if index == len(names) - 1:
                        axis.set_xlabel("Assigned samples", fontsize=10)
            fig.legend(handles.values(), handles.keys(), loc="lower left",
                       bbox_to_anchor=(.10, .045), ncol=2, frameon=False, fontsize=9)
            repeated_counts = ", ".join(str(count) for count in sorted(
                {row["assignments"] for row in rows if row["assignments"] > 1}))
            fig.text(.11, .015, f"{repeated_counts} assignments repeat the same source sample; they are not independent biological wells.",
                     fontsize=8)
            outputs = tuple(output_dir / f"assignment_total_speedups.{extension}" for extension in output_formats)
            for path in outputs:
                self.save(fig, path)
            plt.close(fig)
        return (table_path, *outputs)


@dataclass(frozen=True)
class LinearAxisBreakPolicy:
    """Automatic linear-axis break policy for extreme benchmark outliers."""

    outlier_ratio: float = 3.0
    max_upper_fraction: float = 0.35
    lower_reference_quantile: float = 0.75
    lower_padding: float = 1.18
    upper_window_bottom: float = 0.92
    break_gap_padding: float = 1.08
    upper_padding: float = 1.06
    marker_size: float = 0.008

    def range_for(self, values: Sequence[float]) -> tuple[float, float, float] | None:
        present = sorted(
            value for value in values if math.isfinite(value) and value > 0.0
        )
        if len(present) < 2:
            return None
        split_index = self._outlier_split_index(present)
        if split_index is None:
            return None
        low_top = present[split_index - 1] * self.lower_padding
        high_bottom = low_top * self.break_gap_padding
        high_top = present[-1] * self.upper_padding
        if high_bottom <= low_top:
            return None
        return low_top, high_bottom, high_top

    def _outlier_split_index(self, present: Sequence[float]) -> int | None:
        max_upper_count = max(1, math.floor(len(present) * self.max_upper_fraction))
        candidates: list[tuple[float, int]] = []
        for index in range(1, len(present)):
            upper_count = len(present) - index
            if upper_count > max_upper_count:
                continue
            lower_values = present[:index]
            reference_index = min(
                len(lower_values) - 1,
                max(
                    0,
                    math.floor((len(lower_values) - 1) * self.lower_reference_quantile),
                ),
            )
            lower_reference = lower_values[reference_index]
            upper_bottom = present[index]
            if upper_bottom < lower_reference * self.outlier_ratio:
                continue
            if (
                upper_bottom * self.upper_window_bottom
                <= present[index - 1] * self.lower_padding
            ):
                continue
            candidates.append((upper_bottom / present[index - 1], index))
        if candidates:
            return max(candidates)[1]
        return None

    def mark(self, top_axis, bottom_axis) -> None:
        top_axis.spines.bottom.set_visible(False)
        bottom_axis.spines.top.set_visible(False)
        top_axis.tick_params(labeltop=False, bottom=False)
        bottom_axis.xaxis.tick_bottom()
        marker_kwargs = dict(transform=top_axis.transAxes, color="k", clip_on=False)
        top_axis.plot(
            (-self.marker_size, +self.marker_size),
            (-self.marker_size, +self.marker_size),
            **marker_kwargs,
        )
        top_axis.plot(
            (1 - self.marker_size, 1 + self.marker_size),
            (-self.marker_size, +self.marker_size),
            **marker_kwargs,
        )
        marker_kwargs.update(transform=bottom_axis.transAxes)
        bottom_axis.plot(
            (-self.marker_size, +self.marker_size),
            (1 - self.marker_size, 1 + self.marker_size),
            **marker_kwargs,
        )
        bottom_axis.plot(
            (1 - self.marker_size, 1 + self.marker_size),
            (1 - self.marker_size, 1 + self.marker_size),
            **marker_kwargs,
        )


FIGURE_STYLE = BenchmarkFigureStyle()
LINEAR_AXIS_BREAK_POLICY = LinearAxisBreakPolicy()
SUMMARY_ROW_NUMERICS = SummaryRowNumerics()
METRIC_PROJECTION = BenchmarkMetricProjection()
PIPELINE_LABEL_LAYOUT = PipelineLabelLayout()


FIGURE_METRICS = (
    FigureMetricSpec(
        "accuracy_fraction",
        "cppipe_accuracy",
        "Parity accuracy",
        "Parity accuracy (%)",
        percentage=True,
        target_line=100.0,
        minimum_ylim=0.0,
    ),
    FigureMetricSpec(
        "raw_seconds",
        "cppipe_raw_seconds",
        "Single-thread execution runtime",
        "Raw execution seconds",
        minimum_ylim=0.0,
        log_variant=True,
    ),
    FigureMetricSpec(
        SPEEDUP_METRIC_KEY,
        "cppipe_speedup",
        "Execution speedup versus native CellProfiler",
        "Speedup (x)",
        baseline_line=1.0,
        target_line=SPEEDUP_TARGET,
        minimum_ylim=0.0,
        log_variant=True,
    ),
    FigureMetricSpec(
        "peak_memory_mb",
        "cppipe_peak_memory",
        "Peak process-tree memory usage",
        "Peak RSS (MB)",
        minimum_ylim=0.0,
        log_variant=True,
    ),
)


def parse_summary_source(value: str) -> SummarySource:
    """Parse ``LABEL=/path/to/summary.csv`` CLI syntax."""
    label, separator, path_text = value.partition("=")
    if not separator:
        return SummarySource(DEFAULT_OPENHCS_LABEL, Path(value))
    clean_label = label.strip()
    if not clean_label:
        raise ValueError(f"Summary source label cannot be empty: {value!r}")
    return SummarySource(clean_label, Path(path_text))


def generate_cppipe_benchmark_figures(
    summary_sources: Sequence[SummarySource],
    *,
    output_dir: Path,
    output_formats: Sequence[str] = DEFAULT_FORMATS,
    include_average: bool = True,
    wrap_after: int = DEFAULT_WRAP_AFTER,
    group_width_inches: float = DEFAULT_GROUP_WIDTH_INCHES,
) -> tuple[Path, ...]:
    """Generate grouped CP/OH cppipe benchmark figures and a long-form CSV."""
    if not summary_sources:
        raise ValueError("At least one summary source is required.")

    source_tables = tuple(_load_summary_table(source) for source in summary_sources)
    pipeline_names = _pipeline_order(source_tables)
    methods = (CELLPROFILER_LABEL,) + tuple(source.label for source in summary_sources)
    rows = tuple(
        _benchmark_metric_rows(
            source_tables,
            summary_sources=summary_sources,
            pipeline_names=pipeline_names,
            include_average=include_average,
        )
    )

    output_dir.mkdir(parents=True, exist_ok=True)
    long_csv_path = output_dir / "cppipe_comparison_metrics_long.csv"
    _write_metric_rows(long_csv_path, rows)

    plotted_pipeline_names = tuple(dict.fromkeys(row.pipeline_name for row in rows))
    outputs: list[Path] = [long_csv_path]
    outputs.extend(
        generate_grouped_benchmark_metric_figures(
            rows,
            metrics=FIGURE_METRICS,
            methods=methods,
            pipeline_names=plotted_pipeline_names,
            output_dir=output_dir,
            output_formats=output_formats,
            wrap_after=wrap_after,
            group_width_inches=group_width_inches,
        )
    )
    grouped_request = GroupedFigureRequest(
        rows=rows,
        methods=methods,
        pipeline_names=plotted_pipeline_names,
        output_dir=output_dir,
        output_formats=output_formats,
        wrap_after=wrap_after,
        group_width_inches=group_width_inches,
    )
    outputs.extend(
        _plot_average_speedup_points(
            source_tables,
            summary_sources=summary_sources,
            pipeline_names=pipeline_names,
            output_dir=output_dir,
            output_formats=output_formats,
        )
    )
    outputs.extend(
        generate_speedup_distribution_artifacts(
            tuple(
                SpeedupDistributionSeries.from_points(
                    _speedup_point_series(
                        table,
                        source=source,
                        pipeline_names=pipeline_names,
                    )
                )
                for source, table in zip(summary_sources, source_tables, strict=True)
            ),
            output_dir=output_dir,
            filename_prefix="cppipe_speedup",
            title="Speedup cumulative distribution",
            xlabel="Execution speedup versus native CellProfiler (x)",
            output_formats=output_formats,
        )
    )
    category_rows = tuple(
        _category_metric_rows(rows, category_key=ASSAY_CATEGORY_FIELD)
    )
    module_rows = tuple(_category_metric_rows(rows, category_key=MODULE_CATEGORY_FIELD))
    category_csv_path = output_dir / "cppipe_comparison_category_metrics_long.csv"
    _write_metric_rows(category_csv_path, (*category_rows, *module_rows))
    outputs.append(category_csv_path)
    outputs.extend(
        generate_grouped_benchmark_metric_figures(
            category_rows,
            metrics=_category_metrics(ASSAY_CATEGORY_FIELD),
            methods=methods,
            pipeline_names=_category_order(category_rows),
            output_dir=output_dir,
            output_formats=output_formats,
            wrap_after=wrap_after,
            group_width_inches=group_width_inches,
        )
    )
    outputs.extend(
        generate_grouped_benchmark_metric_figures(
            module_rows,
            metrics=_category_metrics(MODULE_CATEGORY_FIELD),
            methods=methods,
            pipeline_names=_category_order(module_rows),
            output_dir=output_dir,
            output_formats=output_formats,
            wrap_after=wrap_after,
            group_width_inches=group_width_inches,
        )
    )
    for metric in FIGURE_METRICS:
        if metric.key == ACCURACY_FRACTION_FIELD:
            outputs.extend(_plot_accuracy_zoom(grouped_request))
    figure_index_path = output_dir / "benchmark_figure_index.md"
    _write_benchmark_figure_index(figure_index_path, outputs)
    outputs.append(figure_index_path)
    return tuple(outputs)


def generate_grouped_benchmark_metric_figures(
    rows: Sequence[BenchmarkMetricRow],
    *,
    metrics: Sequence[FigureMetricSpec],
    methods: Sequence[str],
    pipeline_names: Sequence[str],
    output_dir: Path,
    output_formats: Sequence[str] = DEFAULT_FORMATS,
    wrap_after: int = DEFAULT_WRAP_AFTER,
    group_width_inches: float = DEFAULT_GROUP_WIDTH_INCHES,
) -> tuple[Path, ...]:
    """Generate v7-style grouped-bar figures for long-form benchmark rows."""
    request = GroupedFigureRequest(
        rows=rows,
        methods=methods,
        pipeline_names=pipeline_names,
        output_dir=output_dir,
        output_formats=output_formats,
        wrap_after=wrap_after,
        group_width_inches=group_width_inches,
    )
    outputs: list[Path] = []
    for metric in metrics:
        if not any(
            METRIC_PROJECTION.value(row, metric) is not None for row in request.rows
        ):
            continue
        outputs.extend(
            _plot_grouped_metric(
                request,
                metric=metric,
                log_y=False,
            )
        )
        if metric.log_variant:
            outputs.extend(
                _plot_grouped_metric(
                    request,
                    metric=metric,
                    log_y=True,
                )
            )
    return tuple(outputs)


def generate_measured_batch_figures(
    summary_sources: Sequence[MeasuredBatchSummarySource],
    *,
    scope: str,
    output_dir: Path,
    output_formats: Sequence[str] = DEFAULT_FORMATS,
    include_average: bool = True,
    selected_pipeline_names: Sequence[str] | None = None,
) -> tuple[Path, ...]:
    """Render already-qualified measured summaries without projecting native time.

    Each source is one measured well/worker mode. Qualification and clock
    conversion belong to the matched-report producer; plotting never invents
    timings, extends measured well counts, or substitutes absent RAM data.
    """
    if scope not in ("execution", "total", "amortization"):
        raise ValueError(f"Unknown measured timing scope: {scope!r}")
    if not summary_sources:
        raise ValueError("At least one measured summary source is required.")
    methods = tuple(dict.fromkeys(
        method for source in summary_sources
        for method in (source.native_method, source.candidate_method)
    ))
    if (len({source.candidate_method for source in summary_sources}) != len(summary_sources)
            or {source.candidate_method for source in summary_sources} & {source.native_method for source in summary_sources}):
        raise ValueError("Measured mode method labels must be distinct.")
    tables = tuple(_load_summary_table(source) for source in summary_sources)
    if selected_pipeline_names is None:
        pipeline_names = _pipeline_order(tables)
        if any(set(table) != set(pipeline_names) for table in tables):
            raise ValueError("Measured modes must contain the same pipeline cohort.")
    else:
        pipeline_names = tuple(selected_pipeline_names)
        if not pipeline_names or len(set(pipeline_names)) != len(pipeline_names):
            raise ValueError("The selected measured cohort must be nonempty and unique.")
        for source, table in zip(summary_sources, tables, strict=True):
            missing = set(pipeline_names) - set(table)
            if missing:
                raise ValueError(
                    f"Measured source {source.path} lacks selected cases: {sorted(missing)!r}"
                )
    if scope == "amortization":
        return _generate_measured_amortization_figures(
            summary_sources, pipeline_names=pipeline_names,
            output_dir=output_dir, output_formats=output_formats,
        )
    rows = tuple(
        _benchmark_metric_rows(
            tables,
            summary_sources=summary_sources,
            pipeline_names=pipeline_names,
            include_average=include_average and len(pipeline_names) > 1,
        )
    )
    metrics = (
        FigureMetricSpec(
            RAW_SECONDS_FIELD,
            f"measured_{scope}_seconds",
            f"Measured batch {scope} runtime",
            f"{scope.title()} seconds",
            minimum_ylim=0.0,
            log_variant=True,
        ),
        FigureMetricSpec(
            SPEEDUP_METRIC_KEY,
            f"measured_{scope}_speedup",
            f"Measured batch {scope} speedup versus CellProfiler",
            "Speedup (x)",
            baseline_line=1.0,
            target_line=SPEEDUP_TARGET if scope == "execution" else None,
            minimum_ylim=0.0,
            log_variant=True,
        ),
    )
    if scope == "execution":
        metrics = (
            FigureMetricSpec(
                ACCURACY_FRACTION_FIELD,
                "qualified_science_pass",
                "Full scientific comparison passed",
                "Qualified comparison (%)",
                percentage=True,
                target_line=100.0,
                minimum_ylim=0.0,
            ),
            *metrics,
        )
    output_dir.mkdir(parents=True, exist_ok=True)
    csv_path = output_dir / f"measured_{scope}_metrics_long.csv"
    _write_metric_rows(csv_path, rows)
    caption_path = output_dir / f"measured_{scope}_caption.md"
    caption_path.write_text(
        f"Measured batch {scope} comparison. Modes: "
        + "; ".join(source.label for source in summary_sources)
        + ". Each pipeline contributes one speedup: its native CellProfiler "
        "median from the declared baseline divided by its OpenHCS median. "
        "Distribution statistics exclude the plotted Average row and native "
        "baseline rows. Grouped Average bars are arithmetic averages across "
        "the supplied pipeline cohort. Qualification, clock boundaries, and "
        "repetition selection are established by the matched-report producer, "
        "not by plotting. No RAM measurements are supplied. "
        + " ".join(dict.fromkeys(source.comparison_description for source in summary_sources)) + "\n",
        encoding="utf-8",
    )
    return (
        csv_path,
        caption_path,
        *generate_grouped_benchmark_metric_figures(
            rows,
            metrics=metrics,
            methods=methods,
            pipeline_names=tuple(dict.fromkeys(row.pipeline_name for row in rows)),
            output_dir=output_dir,
            output_formats=output_formats,
        ),
        *generate_speedup_distribution_artifacts(
            tuple(
                SpeedupDistributionSeries(
                    source.candidate_method,
                    tuple(
                        row.speedup
                        for row in rows
                        if row.method == source.candidate_method
                        and row.pipeline_name in pipeline_names
                        and row.speedup is not None
                    ),
                )
                for source in summary_sources
            ),
            output_dir=output_dir,
            filename_prefix=f"measured_{scope}_speedup",
            title=f"Measured batch {scope} speedup distribution",
            xlabel=f"{scope.title()} speedup versus native CellProfiler (x)",
            target_line=1.0 if scope == "total" else SPEEDUP_TARGET,
            output_formats=output_formats,
        ),
    )


def _generate_measured_amortization_figures(
    sources: Sequence[MeasuredBatchSummarySource], *, pipeline_names: Sequence[str],
    output_dir: Path, output_formats: Sequence[str],
) -> tuple[Path, ...]:
    """Present actual single-core batch sizes using the existing manuscript style."""
    heads = {
        source.qualified_custody()["source_head"]
        for source in sources
    }
    if len(heads) != 1:
        raise ValueError("Amortization modes must share one qualified source revision")
    points = {
        name: sorted((source.amortization_points(name) for source in sources), key=lambda point: point[0])
        for name in pipeline_names
    }
    for name, series in points.items():
        counts = tuple(count for count, _ in series)
        if len(counts) < 2 or counts[0] != 1 or len(set(counts)) != len(counts):
            raise ValueError(f"Amortization needs measured1 and distinct larger counts: {name}")
    output_dir.mkdir(parents=True, exist_ok=True)
    outputs = []
    metric = FigureMetricSpec(
        RAW_SECONDS_FIELD, "measured_single_core_amortization",
        "Single-core measured amortization", "Seconds per assignment", minimum_ylim=0.0,
    )
    with FIGURE_STYLE.context():
        columns = min(2, len(pipeline_names))
        rows = math.ceil(len(pipeline_names) / columns)
        fig, axes = plt.subplots(rows, columns, squeeze=False,
                                 figsize=(7.2, 3.4 * rows))
        for index, name in enumerate(pipeline_names):
            axis = axes.flat[index]
            series = points[name]
            counts = tuple(count for count, _ in series)
            for method_index, method in enumerate(series[0][1]):
                axis.plot(counts, [values[method] for _, values in series],
                          marker="o", label=method,
                          linestyle=":" if method == "CP total" else "-",
                          color=FIGURE_STYLE.color_for_method(method_index))
            FIGURE_STYLE.decorate_axis(axis, metric=metric, panel_index=index)
            axis.set_title(PIPELINE_LABEL_LAYOUT.split_label(name), loc="left", pad=10)
            axis.set_xlabel("Measured repeated assignments\n(one worker)")
            axis.set_ylabel(metric.ylabel)
            axis.set_xticks(counts)
            axis.tick_params(labelsize=9)
            axis.set_ylim(bottom=0)
        for axis in tuple(axes.flat)[len(pipeline_names):]:
            axis.set_visible(False)
        handles, labels = axes.flat[0].get_legend_handles_labels()
        fig.legend(handles, labels, frameon=False, loc="lower center", ncol=len(labels))
        fig.tight_layout(rect=(0, 0.07, 1, 1))
        for extension in output_formats:
            path = output_dir / f"{metric.filename_stem}.{extension}"
            FIGURE_STYLE.save(fig, path)
            outputs.append(path)
        plt.close(fig)
    caption = output_dir / "measured_single_core_amortization_caption.md"
    caption.write_text(
        "Actual measured assignment counts only; connecting lines are visual guides, "
        "not projections. One CPU/worker per engine, three measured repetitions after warmup. "
        "Execution and total curves use per-engine medians divided by the declared assignment count. "
        "OH non-execution is the median paired (total minus server execution) divided by that count: "
        "compilation plus client submission/polling overhead. It does not separate pixel processing "
        "from generic plumbing inside the server execution interval. "
        "Repeated assignments reuse one biological source sample. OH total includes compilation "
        "and full execution; CP total includes invocation preparation and execution, excluding "
        "one-time pipeline loading and JVM startup. Server/library readiness is excluded for both. "
        "Single-sample compile-plus-run performance relative to native remains visible; "
        "the execution headline excludes compilation. No unmeasured modes or RAM are shown.\n",
        encoding="utf-8",
    )
    return (*outputs, caption)


def _load_summary_table(source: SummarySource) -> SummaryTable:
    with source.path.open(encoding="utf-8", newline="") as handle:
        rows = tuple(csv.DictReader(handle))
    if not rows:
        raise ValueError(f"Summary CSV is empty: {source.path}")
    required = {
        CASE_NAME_FIELD,
        NATIVE_SECONDS_FIELD,
        OPENHCS_SECONDS_FIELD,
        ACCURACY_FIELD,
    }
    missing = required - set(rows[0])
    if missing:
        raise ValueError(
            f"Summary CSV {source.path} missing columns: {sorted(missing)!r}"
        )
    return {row[CASE_NAME_FIELD]: row for row in rows}


def _pipeline_order(source_tables: SummaryTables) -> tuple[str, ...]:
    ordered: list[str] = []
    seen: set[str] = set()
    for table in source_tables:
        for pipeline_name in table:
            if pipeline_name in seen:
                continue
            ordered.append(pipeline_name)
            seen.add(pipeline_name)
    return tuple(ordered)


def _benchmark_metric_rows(
    source_tables: SummaryTables,
    *,
    summary_sources: Sequence[SummarySource],
    pipeline_names: Sequence[str],
    include_average: bool,
) -> Iterable[BenchmarkMetricRow]:
    for pipeline_name in pipeline_names:
        native_methods: set[str] = set()
        category_row = source_tables[0].get(pipeline_name)
        for source, table in zip(summary_sources, source_tables, strict=True):
            native_row, candidate_row = source.metric_rows(
                pipeline_name,
                table.get(pipeline_name),
                category_row=category_row,
            )
            if native_row.method not in native_methods:
                native_methods.add(native_row.method)
                yield native_row
            yield candidate_row
    if include_average:
        yield from _average_rows(
            _benchmark_metric_rows(
                source_tables,
                summary_sources=summary_sources,
                pipeline_names=pipeline_names,
                include_average=False,
            )
        )


def _category_from_summary_row(
    pipeline_name: str,
    row: SummaryRow | None,
) -> BenchmarkCategory:
    """Read persisted case metadata, falling back for old pre-category summaries."""
    if row is not None:
        assay_category = row.get(ASSAY_CATEGORY_FIELD)
        module_category = row.get(MODULE_CATEGORY_FIELD)
        if assay_category or module_category:
            return BenchmarkCategory(
                assay=assay_category or DEFAULT_BENCHMARK_CATEGORY.assay,
                module=module_category or DEFAULT_BENCHMARK_CATEGORY.module,
            )
    return official_cp3_case_category(pipeline_name)


def _average_rows(rows: Iterable[BenchmarkMetricRow]) -> Iterable[BenchmarkMetricRow]:
    by_method: dict[str, list[BenchmarkMetricRow]] = {}
    for row in rows:
        by_method.setdefault(row.method, []).append(row)
    for method, method_rows in by_method.items():
        yield BenchmarkMetricRow(
            pipeline_name="Average",
            method=method,
            assay_category=AGGREGATE_LABEL,
            module_category=AGGREGATE_LABEL,
            accuracy_fraction=_mean_present(
                row.accuracy_fraction for row in method_rows
            ),
            raw_seconds=_mean_present(row.raw_seconds for row in method_rows),
            speedup=_mean_present(row.speedup for row in method_rows),
            peak_memory_mb=_mean_present(row.peak_memory_mb for row in method_rows),
        )


def _write_metric_rows(path: Path, rows: Sequence[BenchmarkMetricRow]) -> None:
    fieldnames = (
        PIPELINE_NAME_FIELD,
        METHOD_FIELD,
        ASSAY_CATEGORY_FIELD,
        MODULE_CATEGORY_FIELD,
        ACCURACY_FRACTION_FIELD,
        RAW_SECONDS_FIELD,
        SPEEDUP_METRIC_KEY,
        PEAK_MEMORY_MB_FIELD,
    )
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow(
                {
                    PIPELINE_NAME_FIELD: row.pipeline_name,
                    METHOD_FIELD: row.method,
                    ASSAY_CATEGORY_FIELD: row.assay_category,
                    MODULE_CATEGORY_FIELD: row.module_category,
                    ACCURACY_FRACTION_FIELD: row.accuracy_fraction,
                    RAW_SECONDS_FIELD: row.raw_seconds,
                    SPEEDUP_METRIC_KEY: row.speedup,
                    PEAK_MEMORY_MB_FIELD: row.peak_memory_mb,
                }
            )


def _category_metric_rows(
    rows: Sequence[BenchmarkMetricRow],
    *,
    category_key: str,
) -> Iterable[BenchmarkMetricRow]:
    grouped: dict[tuple[str, str], list[BenchmarkMetricRow]] = {}
    for row in rows:
        if row.pipeline_name == "Average":
            continue
        category_name = str(getattr(row, category_key))
        grouped.setdefault((category_name, row.method), []).append(row)

    for (category_name, method), category_rows in grouped.items():
        yield BenchmarkMetricRow(
            pipeline_name=category_name,
            method=method,
            assay_category=(
                category_name
                if category_key == ASSAY_CATEGORY_FIELD
                else AGGREGATE_LABEL
            ),
            module_category=(
                category_name
                if category_key == MODULE_CATEGORY_FIELD
                else AGGREGATE_LABEL
            ),
            accuracy_fraction=_mean_present(
                row.accuracy_fraction for row in category_rows
            ),
            raw_seconds=_mean_present(row.raw_seconds for row in category_rows),
            speedup=_mean_present(row.speedup for row in category_rows),
            peak_memory_mb=_mean_present(row.peak_memory_mb for row in category_rows),
        )


def _category_metrics(category_key: str) -> tuple[FigureMetricSpec, ...]:
    prefix = (
        "cppipe_assay_category"
        if category_key == ASSAY_CATEGORY_FIELD
        else "cppipe_module_category"
    )
    label = (
        "assay category" if category_key == ASSAY_CATEGORY_FIELD else "module category"
    )
    return tuple(
        FigureMetricSpec(
            key=metric.key,
            filename_stem=f"{prefix}_{metric.key}",
            title=f"{metric.title} by {label}",
            ylabel=metric.ylabel,
            percentage=metric.percentage,
            baseline_line=metric.baseline_line,
            target_line=metric.target_line,
            minimum_ylim=metric.minimum_ylim,
            log_variant=metric.log_variant,
            use_axis_break=metric.use_axis_break,
        )
        for metric in FIGURE_METRICS
    )


def _category_order(rows: Sequence[BenchmarkMetricRow]) -> tuple[str, ...]:
    return tuple(dict.fromkeys(row.pipeline_name for row in rows))


def _plot_grouped_metric(
    request: GroupedFigureRequest,
    *,
    metric: FigureMetricSpec,
    log_y: bool,
) -> tuple[Path, ...]:
    broken_range = (
        LINEAR_AXIS_BREAK_POLICY.range_for(_grouped_metric_values(request, metric))
        if metric.use_axis_break and not log_y and not metric.percentage
        else None
    )
    if broken_range is not None:
        return _plot_grouped_metric_broken(
            request,
            metric=metric,
            broken_range=broken_range,
        )
    panels = PIPELINE_LABEL_LAYOUT.panels(request.pipeline_names, request.wrap_after)
    fig_width = max(
        8.0,
        max(len(panel) for panel in panels) * request.group_width_inches,
    )
    fig_height = (
        SINGLE_PANEL_HEIGHT_INCHES if len(panels) == 1 else MULTI_PANEL_HEIGHT_INCHES
    )
    with FIGURE_STYLE.context():
        fig, axes = plt.subplots(
            len(panels),
            1,
            figsize=(fig_width, fig_height),
            layout="constrained",
        )
        panel_axes = (axes,) if len(panels) == 1 else tuple(axes)
        width = _bar_width(len(request.methods))
        offsets = _bar_offsets(len(request.methods), width)
        row_index = {(row.pipeline_name, row.method): row for row in request.rows}

        for panel_index, (axis, panel_names) in enumerate(
            zip(panel_axes, panels, strict=True)
        ):
            x_positions = tuple(range(len(panel_names)))
            for method_index, method in enumerate(request.methods):
                values = [
                    METRIC_PROJECTION.plot_value(
                        METRIC_PROJECTION.value(
                            row_index.get((pipeline_name, method)),
                            metric,
                        )
                    )
                    for pipeline_name in panel_names
                ]
                axis.bar(
                    [x + offsets[method_index] for x in x_positions],
                    values,
                    width=width,
                    label=method if panel_index == 0 else None,
                    color=FIGURE_STYLE.color_for_method(method_index),
                    edgecolor=FIGURE_STYLE.background,
                    linewidth=0.55,
                )

            _draw_reference_lines(axis, metric=metric, log_y=log_y)
            FIGURE_STYLE.decorate_axis(axis, metric=metric, panel_index=panel_index)
            axis.set_ylabel(metric.ylabel)
            axis.set_xticks(list(x_positions))
            axis.set_xticklabels(
                [PIPELINE_LABEL_LAYOUT.split_label(name) for name in panel_names],
                rotation=42,
                ha="right",
                fontsize=PIPELINE_LABEL_FONT_SIZE,
            )
            axis.margins(x=0.01)
            if metric.minimum_ylim is not None and not log_y:
                axis.set_ylim(bottom=metric.minimum_ylim)
            if metric.percentage:
                axis.set_ylim(0.0, 105.0)
            if log_y:
                axis.set_yscale("log")
                axis.yaxis.set_major_locator(LogLocator(base=10.0, numticks=6))
                axis.yaxis.set_minor_locator(NullLocator())
                axis.yaxis.set_major_formatter(FuncFormatter(_plain_log_tick_label))
                axis.yaxis.set_minor_formatter(NullFormatter())

        FIGURE_STYLE.decorate_legend(panel_axes[0])
        outputs: list[Path] = []
        filename_stem = f"{metric.filename_stem}_log" if log_y else metric.filename_stem
        for output_format in request.output_formats:
            output_path = request.output_dir / f"{filename_stem}.{output_format}"
            FIGURE_STYLE.save(fig, output_path)
            outputs.append(output_path)
        plt.close(fig)
        return tuple(outputs)


def _plot_grouped_metric_broken(
    request: GroupedFigureRequest,
    *,
    metric: FigureMetricSpec,
    broken_range: tuple[float, float, float],
) -> tuple[Path, ...]:
    panels = (tuple(request.pipeline_names),)
    row_index = {(row.pipeline_name, row.method): row for row in request.rows}
    panel_axis_counts = (2,)
    height_ratios = (1.0, 3.2)
    fig_width = max(
        8.0,
        max(len(panel) for panel in panels) * request.group_width_inches,
    )
    with FIGURE_STYLE.context():
        fig, axes = plt.subplots(
            sum(panel_axis_counts),
            1,
            figsize=(
                fig_width,
                7.2,
            ),
            gridspec_kw={"height_ratios": height_ratios},
            sharex=True,
            layout="constrained",
        )
        all_axes = (axes,) if sum(panel_axis_counts) == 1 else tuple(axes.flat)
        width = _bar_width(len(request.methods))
        offsets = _bar_offsets(len(request.methods), width)

        axis_offset = 0
        for panel_index, panel_names in enumerate(panels):
            top_axis = all_axes[axis_offset]
            bottom_axis = all_axes[axis_offset + 1]
            axis_offset += 2
            panel_axes = (top_axis, bottom_axis)
            label_axis = bottom_axis
            x_positions = tuple(range(len(panel_names)))
            for axis in panel_axes:
                for method_index, method in enumerate(request.methods):
                    values = [
                        METRIC_PROJECTION.plot_value(
                            METRIC_PROJECTION.value(
                                row_index.get((pipeline_name, method)),
                                metric,
                            )
                        )
                        for pipeline_name in panel_names
                    ]
                    axis.bar(
                        [x + offsets[method_index] for x in x_positions],
                        values,
                        width=width,
                        label=(
                            method
                            if panel_index == 0 and axis is panel_axes[0]
                            else None
                        ),
                        color=FIGURE_STYLE.color_for_method(method_index),
                        edgecolor=FIGURE_STYLE.background,
                        linewidth=0.55,
                    )
                if axis is panel_axes[-1]:
                    _draw_reference_lines(axis, metric=metric, log_y=False)
                FIGURE_STYLE.decorate_axis(
                    axis,
                    metric=metric,
                    panel_index=panel_index if axis is panel_axes[0] else -1,
                )
                axis.set_ylabel(metric.ylabel)
                axis.set_xticks(list(x_positions))
                axis.margins(x=0.01)

            top_axis.set_ylim(broken_range[1], broken_range[2])
            bottom_axis.set_ylim(
                metric.minimum_ylim if metric.minimum_ylim is not None else 0.0,
                broken_range[0],
            )
            top_axis.set_xticklabels(())
            LINEAR_AXIS_BREAK_POLICY.mark(top_axis, bottom_axis)
            label_axis.set_xticklabels(
                [PIPELINE_LABEL_LAYOUT.split_label(name) for name in panel_names],
                rotation=42,
                ha="right",
                fontsize=PIPELINE_LABEL_FONT_SIZE,
            )

        FIGURE_STYLE.decorate_legend(all_axes[0])
        outputs: list[Path] = []
        for output_format in request.output_formats:
            output_path = request.output_dir / f"{metric.filename_stem}.{output_format}"
            FIGURE_STYLE.save(fig, output_path)
            outputs.append(output_path)
        plt.close(fig)
        return tuple(outputs)


def _plot_accuracy_zoom(
    request: GroupedFigureRequest,
) -> tuple[Path, ...]:
    """Plot accuracy with a broken y-axis so tiny parity drift is visible."""
    panels = PIPELINE_LABEL_LAYOUT.panels(request.pipeline_names, request.wrap_after)
    panel_count = len(panels)
    fig_width = max(
        8.0,
        max(len(panel) for panel in panels) * request.group_width_inches,
    )
    with FIGURE_STYLE.context():
        fig, axes = plt.subplots(
            panel_count * 2,
            1,
            figsize=(fig_width, ACCURACY_ZOOM_PANEL_HEIGHT_INCHES * panel_count),
            gridspec_kw={"height_ratios": tuple((2.7, 1.0) * panel_count)},
            layout="constrained",
        )
        all_axes = tuple(axes.flat)
        width = _bar_width(len(request.methods))
        offsets = _bar_offsets(len(request.methods), width)
        row_index = {(row.pipeline_name, row.method): row for row in request.rows}
        metric = FIGURE_METRICS[0]

        for panel_index, panel_names in enumerate(panels):
            zoom_axis = all_axes[panel_index * 2]
            context_axis = all_axes[panel_index * 2 + 1]
            x_positions = tuple(range(len(panel_names)))
            for axis in (zoom_axis, context_axis):
                for method_index, method in enumerate(request.methods):
                    values = [
                        METRIC_PROJECTION.plot_value(
                            METRIC_PROJECTION.value(
                                row_index.get((pipeline_name, method)),
                                metric,
                            )
                        )
                        for pipeline_name in panel_names
                    ]
                    axis.bar(
                        [x + offsets[method_index] for x in x_positions],
                        values,
                        width=width,
                        label=(
                            method if panel_index == 0 and axis is zoom_axis else None
                        ),
                        color=FIGURE_STYLE.color_for_method(method_index),
                        edgecolor=FIGURE_STYLE.background,
                        linewidth=0.55,
                    )
                FIGURE_STYLE.decorate_axis(axis, metric=metric, panel_index=panel_index)
                axis.set_xticks(list(x_positions))

            zoom_axis.set_ylim(
                100.0 - ACCURACY_ZOOM_HALF_RANGE_PERCENT,
                100.0 + ACCURACY_ZOOM_HALF_RANGE_PERCENT,
            )
            zoom_axis.axhline(
                100.0,
                color=FIGURE_STYLE.target_color,
                linewidth=1.15,
                linestyle="--",
                alpha=0.85,
            )
            zoom_axis.yaxis.set_major_formatter(FuncFormatter(_percent_tick_label))
            zoom_axis.yaxis.get_offset_text().set_visible(False)
            zoom_axis.set_ylabel("Accuracy (%)")
            zoom_axis.set_xticklabels(())
            context_axis.set_ylim(0.0, 5.0)
            context_axis.set_ylabel("0-5%")
            context_axis.set_xticklabels(
                [PIPELINE_LABEL_LAYOUT.split_label(name) for name in panel_names],
                rotation=42,
                ha="right",
                fontsize=PIPELINE_LABEL_FONT_SIZE,
            )
            zoom_axis.margins(x=0.01)
            context_axis.margins(x=0.01)
            LINEAR_AXIS_BREAK_POLICY.mark(zoom_axis, context_axis)

        FIGURE_STYLE.decorate_legend(all_axes[0])
        outputs: list[Path] = []
        for output_format in request.output_formats:
            output_path = request.output_dir / f"cppipe_accuracy_zoom.{output_format}"
            FIGURE_STYLE.save(fig, output_path)
            outputs.append(output_path)
        plt.close(fig)
        return tuple(outputs)


def _plot_average_speedup_points(
    source_tables: SummaryTables,
    *,
    summary_sources: Sequence[SummarySource],
    pipeline_names: Sequence[str],
    output_dir: Path,
    output_formats: Sequence[str],
) -> tuple[Path, ...]:
    """Plot mean OpenHCS speedup with one point per dataset."""
    series = tuple(
        _speedup_point_series(
            table,
            source=source,
            pipeline_names=pipeline_names,
        )
        for source, table in zip(summary_sources, source_tables, strict=True)
    )
    series = tuple(item for item in series if item.points)
    if not series:
        return ()

    csv_path = output_dir / "cppipe_average_speedup_points.csv"
    _write_average_speedup_points_csv(csv_path, series)

    with FIGURE_STYLE.context():
        fig_width = max(5.2, 1.45 * len(series) + 3.2)
        fig, axis = plt.subplots(
            1,
            1,
            figsize=(fig_width, 4.6),
            layout="constrained",
        )
        x_positions = tuple(range(len(series)))
        for index, speedup_series in enumerate(series):
            color = FIGURE_STYLE.color_for_method(index + 1)
            point_x = [
                index + _deterministic_jitter(point_index, len(speedup_series.points))
                for point_index, _point in enumerate(speedup_series.points)
            ]
            point_y = [point.speedup for point in speedup_series.points]
            axis.scatter(
                point_x,
                point_y,
                s=28,
                color=color,
                alpha=0.76,
                edgecolors=FIGURE_STYLE.background,
                linewidths=0.55,
                zorder=3,
            )
            axis.errorbar(
                [index],
                [speedup_series.mean],
                yerr=[[speedup_series.ci95], [speedup_series.ci95]],
                fmt="o",
                color=FIGURE_STYLE.text_color,
                markerfacecolor=color,
                markeredgecolor=FIGURE_STYLE.text_color,
                markersize=8.5,
                capsize=7,
                elinewidth=1.4,
                zorder=4,
                label=f"{speedup_series.label} mean",
            )
        axis.axhline(
            SPEEDUP_TARGET,
            color=FIGURE_STYLE.target_color,
            linewidth=1.15,
            linestyle="--",
            alpha=0.86,
        )
        axis.annotate(
            f"{SPEEDUP_TARGET:g}x target",
            xy=(0.995, SPEEDUP_TARGET),
            xycoords=("axes fraction", "data"),
            xytext=(-2, 3),
            textcoords="offset points",
            ha="right",
            va="bottom",
            fontsize=7.8,
            color=FIGURE_STYLE.target_color,
        )
        axis.set_title("Average execution speedup", loc="left", pad=10)
        axis.set_ylabel("Speedup versus native CellProfiler (x)")
        axis.set_xticks(list(x_positions))
        axis.set_xticklabels([item.label for item in series])
        axis.set_xlim(-0.6, len(series) - 0.4)
        axis.set_ylim(bottom=0.0)
        axis.grid(axis="y", color=FIGURE_STYLE.grid_color, linewidth=0.8, alpha=0.8)
        axis.set_axisbelow(True)
        axis.spines["top"].set_visible(False)
        axis.spines["right"].set_visible(False)
        axis.spines["left"].set_color(FIGURE_STYLE.spine_color)
        axis.spines["bottom"].set_color(FIGURE_STYLE.spine_color)
        axis.legend(frameon=False, loc="upper left")

        outputs: list[Path] = [csv_path]
        for output_format in output_formats:
            output_path = output_dir / f"cppipe_average_speedup_points.{output_format}"
            FIGURE_STYLE.save(fig, output_path)
            outputs.append(output_path)
        plt.close(fig)
        return tuple(outputs)


@dataclass(frozen=True)
class SpeedupPoint:
    """One dataset speedup point for aggregate plotting."""

    pipeline_name: str
    speedup: float


@dataclass(frozen=True)
class SpeedupPointSeries:
    """Per-method speedup distribution and aggregate interval."""

    label: str
    points: tuple[SpeedupPoint, ...]
    mean: float
    standard_deviation: float
    ci95: float


@dataclass(frozen=True)
class SpeedupDistributionSeries:
    """One labeled speedup distribution for report tables and CDF plots."""

    label: str
    values: tuple[float, ...]

    @classmethod
    def from_points(cls, series: SpeedupPointSeries) -> "SpeedupDistributionSeries":
        """Build a distribution series from per-pipeline speedup points."""
        return cls(series.label, tuple(point.speedup for point in series.points))


@dataclass(frozen=True)
class SpeedupSummaryStatistics:
    """Summary statistics for one speedup distribution."""

    label: str
    sample_count: int
    minimum: float
    maximum: float
    median: float
    mean: float
    standard_deviation: float

    @classmethod
    def from_series(
        cls,
        series: SpeedupDistributionSeries,
    ) -> "SpeedupSummaryStatistics | None":
        """Calculate min/max/median/mean statistics for one distribution."""
        values = tuple(
            value for value in series.values if math.isfinite(value) and value > 0.0
        )
        if not values:
            return None
        return cls(
            label=series.label,
            sample_count=len(values),
            minimum=min(values),
            maximum=max(values),
            median=statistics.median(values),
            mean=sum(values) / len(values),
            standard_deviation=statistics.stdev(values) if len(values) > 1 else 0.0,
        )


@dataclass(frozen=True)
class SpeedupDistributionReport:
    """Owns speedup summary tables and cumulative distribution figures."""

    series: tuple[SpeedupDistributionSeries, ...]
    output_dir: Path
    filename_prefix: str
    title: str
    xlabel: str
    output_formats: tuple[str, ...] = DEFAULT_FORMATS
    target_line: float = SPEEDUP_TARGET

    def outputs(self) -> tuple[Path, ...]:
        """Write all speedup distribution report artifacts."""
        if not self.series:
            return ()
        self.output_dir.mkdir(parents=True, exist_ok=True)
        summary_csv = self.output_dir / f"{self.filename_prefix}_summary_statistics.csv"
        summary_markdown = (
            self.output_dir / f"{self.filename_prefix}_summary_statistics.md"
        )
        cdf_csv = (
            self.output_dir / f"{self.filename_prefix}_cumulative_distribution.csv"
        )
        self.write_summary_statistics(summary_csv)
        self.write_summary_markdown(summary_markdown)
        self.write_cdf_csv(cdf_csv)
        outputs: list[Path] = [summary_csv, summary_markdown, cdf_csv]
        outputs.extend(self.plot_cdf(log_x=False))
        outputs.extend(self.plot_cdf(log_x=True))
        return tuple(outputs)

    def write_summary_statistics(self, path: Path) -> None:
        """Write machine-readable speedup summary statistics."""
        fieldnames = (
            "label",
            "sample_count",
            "min_speedup",
            "max_speedup",
            "median_speedup",
            "mean_speedup",
            "standard_deviation",
        )
        with path.open("w", encoding="utf-8", newline="") as handle:
            writer = csv.DictWriter(handle, fieldnames=fieldnames)
            writer.writeheader()
            for row in self.summary_statistics:
                writer.writerow(
                    {
                        "label": row.label,
                        "sample_count": row.sample_count,
                        "min_speedup": row.minimum,
                        "max_speedup": row.maximum,
                        "median_speedup": row.median,
                        "mean_speedup": row.mean,
                        "standard_deviation": row.standard_deviation,
                    }
                )

    def write_summary_markdown(self, path: Path) -> None:
        """Write human-readable speedup summary statistics."""
        lines = [
            "| Series | n | Min speedup | Median speedup | Mean speedup | Max speedup | SD |",
            "| --- | ---: | ---: | ---: | ---: | ---: | ---: |",
        ]
        lines.extend(
            "| "
            f"{row.label} | {row.sample_count} | {row.minimum:.3f} | "
            f"{row.median:.3f} | {row.mean:.3f} | {row.maximum:.3f} | "
            f"{row.standard_deviation:.3f} |"
            for row in self.summary_statistics
        )
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    def write_cdf_csv(self, path: Path) -> None:
        """Write empirical percent-at-or-above-threshold speedup data."""
        fieldnames = (
            "label",
            "speedup_threshold",
            "percent_at_or_above",
            "count_at_or_above",
            "sample_count",
        )
        with path.open("w", encoding="utf-8", newline="") as handle:
            writer = csv.DictWriter(handle, fieldnames=fieldnames)
            writer.writeheader()
            for item in self.series:
                sample_count = len(item.values)
                for threshold in self.thresholds(item.values):
                    count = sum(1 for value in item.values if value >= threshold)
                    writer.writerow(
                        {
                            "label": item.label,
                            "speedup_threshold": threshold,
                            "percent_at_or_above": 100.0 * count / sample_count,
                            "count_at_or_above": count,
                            "sample_count": sample_count,
                        }
                    )

    def plot_cdf(self, *, log_x: bool) -> tuple[Path, ...]:
        """Plot empirical percent-at-or-above-threshold speedup curves."""
        with FIGURE_STYLE.context():
            fig, axis = plt.subplots(
                1,
                1,
                figsize=(7.4, 4.4),
                layout="constrained",
            )
            self.draw_cdf(axis, log_x=log_x)
            axis.legend(frameon=False, loc="upper left", bbox_to_anchor=(1.02, 1.0))
            outputs: list[Path] = []
            suffix = (
                "_cumulative_distribution_log" if log_x else "_cumulative_distribution"
            )
            for output_format in self.output_formats:
                output_path = (
                    self.output_dir / f"{self.filename_prefix}{suffix}.{output_format}"
                )
                FIGURE_STYLE.save(fig, output_path)
                outputs.append(output_path)
            plt.close(fig)
            return tuple(outputs)

    def draw_cdf(self, axis, *, log_x: bool) -> None:
        """The one empirical CDF painter, for standalone and composed figures."""
        for index, item in enumerate(self.series):
            summary = SpeedupSummaryStatistics.from_series(item)
            if summary is None:
                continue
            thresholds = self.thresholds(item.values)
            y_values = tuple(100.0 * sum(value >= threshold for value in item.values) / len(item.values)
                             for threshold in thresholds)
            axis.step(thresholds, y_values, where="post", linewidth=2.0,
                      color=FIGURE_STYLE.color_for_method(index + 1),
                      label=f"{item.label}\nmin {summary.minimum:.2f}x; median {summary.median:.2f}x")
        axis.axvline(self.target_line, color=FIGURE_STYLE.target_color, linewidth=1.15,
                     linestyle="--", alpha=0.86)
        axis.annotate("Native parity (1x)" if self.target_line == 1.0 else f"{self.target_line:g}x target",
                      xy=(self.target_line, 99.0), xycoords=("data", "data"), xytext=(3, -2),
                      textcoords="offset points", ha="left", va="top", fontsize=10,
                      color=FIGURE_STYLE.target_color)
        if log_x:
            axis.set_xscale("log", base=2)
            axis.xaxis.set_major_locator(LogLocator(base=2, numticks=12))
            axis.xaxis.set_minor_locator(NullLocator())
            axis.xaxis.set_major_formatter(FuncFormatter(_plain_log_tick_label))
            axis.xaxis.set_minor_formatter(NullFormatter())
        axis.set_ylim(0.0, 102.0)
        axis.set_xlabel(self.xlabel)
        axis.set_ylabel("Pipelines at or above threshold (%)")
        axis.set_title(f"{self.title} (log scale)" if log_x else self.title, loc="left", pad=10)
        axis.grid(axis="both", color=FIGURE_STYLE.grid_color, linewidth=0.8, alpha=0.8)
        axis.set_axisbelow(True)
        axis.spines["top"].set_visible(False)
        axis.spines["right"].set_visible(False)
        axis.spines["left"].set_color(FIGURE_STYLE.spine_color)
        axis.spines["bottom"].set_color(FIGURE_STYLE.spine_color)

    @property
    def summary_statistics(self) -> tuple[SpeedupSummaryStatistics, ...]:
        """Return summary rows for every distribution series."""
        return tuple(
            stats
            for item in self.series
            if (stats := SpeedupSummaryStatistics.from_series(item)) is not None
        )

    @staticmethod
    def thresholds(values: Sequence[float]) -> tuple[float, ...]:
        """Return empirical speedup thresholds for CDF/survival reporting."""
        if not values:
            return ()
        return tuple(
            sorted(
                {
                    min(values),
                    max(values),
                    1.0,
                    SPEEDUP_TARGET,
                    *values,
                }
            )
        )


def generate_speedup_distribution_artifacts(
    series: Sequence[SpeedupDistributionSeries],
    *,
    output_dir: Path,
    filename_prefix: str,
    title: str,
    xlabel: str,
    output_formats: Sequence[str] = DEFAULT_FORMATS,
    target_line: float = SPEEDUP_TARGET,
) -> tuple[Path, ...]:
    """Generate speedup summary tables and cumulative distribution figures."""
    clean_series = tuple(
        SpeedupDistributionSeries(
            item.label,
            tuple(
                value for value in item.values if math.isfinite(value) and value > 0.0
            ),
        )
        for item in series
    )
    clean_series = tuple(item for item in clean_series if item.values)
    if not clean_series:
        return ()
    return SpeedupDistributionReport(
        series=clean_series,
        output_dir=output_dir,
        filename_prefix=filename_prefix,
        title=title,
        xlabel=xlabel,
        output_formats=tuple(output_formats),
        target_line=target_line,
    ).outputs()


def _speedup_point_series(
    table: SummaryTable,
    *,
    source: SummarySource,
    pipeline_names: Sequence[str],
) -> SpeedupPointSeries:
    points = tuple(
        SpeedupPoint(pipeline_name, speedup)
        for pipeline_name in pipeline_names
        if (
            speedup := source.metric_rows(
                pipeline_name, table.get(pipeline_name), category_row=table.get(pipeline_name)
            )[1].speedup
        )
        is not None
    )
    values = tuple(point.speedup for point in points)
    mean = _mean_present(values) or math.nan
    standard_deviation = statistics.stdev(values) if len(values) > 1 else 0.0
    ci95 = 1.96 * standard_deviation / math.sqrt(len(values)) if values else math.nan
    return SpeedupPointSeries(
        label=source.label,
        points=points,
        mean=mean,
        standard_deviation=standard_deviation,
        ci95=ci95,
    )


def _write_average_speedup_points_csv(
    path: Path,
    series: Sequence[SpeedupPointSeries],
) -> None:
    fieldnames = (
        "method",
        PIPELINE_NAME_FIELD,
        SPEEDUP_METRIC_KEY,
        "mean_speedup",
        "standard_deviation",
        "ci95",
    )
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for item in series:
            for point in item.points:
                writer.writerow(
                    {
                        "method": item.label,
                        PIPELINE_NAME_FIELD: point.pipeline_name,
                        SPEEDUP_METRIC_KEY: point.speedup,
                        "mean_speedup": item.mean,
                        "standard_deviation": item.standard_deviation,
                        "ci95": item.ci95,
                    }
                )


def _deterministic_jitter(index: int, count: int) -> float:
    if count <= 1:
        return 0.0
    spread = 0.18
    return ((index / (count - 1)) - 0.5) * spread


def _grouped_metric_values(
    request: GroupedFigureRequest,
    metric: FigureMetricSpec,
) -> tuple[float, ...]:
    return tuple(
        value
        for row in request.rows
        if (value := METRIC_PROJECTION.value(row, metric)) is not None
        and math.isfinite(value)
        and value > 0.0
    )


def _draw_reference_lines(axis, *, metric: FigureMetricSpec, log_y: bool) -> None:
    if metric.baseline_line is not None:
        axis.axhline(
            metric.baseline_line,
            color=FIGURE_STYLE.baseline_color,
            linewidth=1.0,
            alpha=0.72,
        )
    if metric.target_line is None:
        return
    if log_y and metric.target_line <= 0.0:
        return
    axis.axhline(
        metric.target_line,
        color=FIGURE_STYLE.target_color,
        linewidth=1.15,
        linestyle="--",
        alpha=0.86,
    )
    label = (
        f"{metric.target_line:g}x target"
        if metric.key == SPEEDUP_METRIC_KEY else "target"
    )
    axis.annotate(
        label,
        xy=(0.995, metric.target_line),
        xycoords=("axes fraction", "data"),
        xytext=(-2, 3),
        textcoords="offset points",
        ha="right",
        va="bottom",
        fontsize=7.8,
        color=FIGURE_STYLE.target_color,
    )


def _plain_log_tick_label(value: float, position: int) -> str:
    del position
    if value <= 0.0 or not math.isfinite(value):
        return ""
    if value >= 100.0:
        return f"{value:.0f}"
    if value >= 10.0:
        return f"{value:.1f}".rstrip("0").rstrip(".")
    if value >= 1.0:
        return f"{value:.2f}".rstrip("0").rstrip(".")
    return f"{value:.3f}".rstrip("0").rstrip(".")


def _percent_tick_label(value: float, position: int) -> str:
    del position
    if not math.isfinite(value):
        return ""
    return f"{value:.3f}"


def _bar_offsets(method_count: int, width: float) -> tuple[float, ...]:
    center = (method_count - 1) / 2.0
    return tuple((index - center) * width for index in range(method_count))


def _bar_width(method_count: int) -> float:
    return min(GROUPED_BAR_MAX_WIDTH, GROUPED_BAR_FRACTION / max(method_count, 1))


def _mean_present(values: Iterable[float | None]) -> float | None:
    present = [float(value) for value in values if value is not None]
    if not present:
        return None
    return sum(present) / len(present)


def _write_benchmark_figure_index(path: Path, outputs: Sequence[Path]) -> None:
    figure_names = {output.name for output in outputs}
    lines = [
        "# CellProfiler Benchmark Figure Index",
        "",
        "Autogenerated benchmark figures for the OpenHCS paper draft.",
        "",
        "## Manuscript Benchmark Panels",
        "",
        "- `cppipe_accuracy.*`: parity across imported `.cppipe` workflows.",
        "- `cppipe_accuracy_zoom.*`: broken-axis parity view for tiny numeric drift near 100%.",
        "- `cppipe_raw_seconds.*`: single-thread execution runtime in seconds.",
        "- `cppipe_raw_seconds_log.*`: runtime on a log scale for mixed short and long pipelines.",
        f"- `cppipe_speedup.*`: execution speedup versus native CellProfiler with the {SPEEDUP_TARGET:g}x target line.",
        "- `cppipe_speedup_log.*`: speedup on a log scale for wide dynamic range.",
        "- `cppipe_speedup_summary_statistics.*`: min, max, median, and mean speedup tables.",
        "- `cppipe_speedup_cumulative_distribution.*`: percent of datasets at or above each speedup threshold.",
        "- `cppipe_speedup_cumulative_distribution_log.*`: cumulative speedup distribution with a log x-axis.",
        "- `cppipe_average_speedup_points.*`: aggregate speedup mean with per-dataset points and a 95% confidence interval.",
        "- `cppipe_average_speedup_points.csv`: per-dataset speedups and aggregate statistics used by the point/error chart.",
        "- `cppipe_peak_memory*`: peak RSS figures when memory metrics are present.",
        "- `cppipe_assay_category_*`: manifest-declared assay category summaries.",
        "- `cppipe_module_category_*`: manifest-declared module category summaries.",
        "- `cppipe_comparison_metrics_long.csv`: long-form per-pipeline plotting table.",
        "- `cppipe_comparison_category_metrics_long.csv`: long-form category plotting table.",
        "",
        "## Files Present",
        "",
    ]
    lines.extend(f"- `{name}`" for name in sorted(figure_names))
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
