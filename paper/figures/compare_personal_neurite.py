"""Compare current native well measurements, without processing or tuning images.

The identity key is evaluation-only: never give it to a blind analysis author.
This entrypoint selects one run and an explicit well-aggregation protocol, never
a mixture of attempts. Its outputs do not establish segmentation accuracy.
Previously published comparison tables remain immutable historical evidence;
this reader consumes the current unit-bearing OpenHCS summary declaration.
"""

import argparse
from abc import ABC, abstractmethod
import csv
from dataclasses import asdict, dataclass, field, fields
import hashlib
import json
import math
from pathlib import Path
from statistics import mean, stdev
from typing import ClassVar


@dataclass(frozen=True)
class SummaryEndpoint:
    """One endpoint declaration supplies native decoding and reference identity."""

    label: str
    reference_column: str
    native_column: str

    def native_value(self, summary, cells):
        return float(summary[self.native_column])


class CellMeanEndpoint(SummaryEndpoint):
    """Mean of per-cell endpoints, not a pooled graph-segment statistic."""

    def native_value(self, summary, cells):
        return mean(float(row[self.native_column]) for row in cells)


@dataclass(frozen=True)
class WellEndpoints:
    mean_outgrowth: float = field(metadata={"endpoint": SummaryEndpoint(
        "Mean outgrowth per cell / control", "Mean Outgrowth Per Cell (Neurite Outgrowth)", "mean_outgrowth_per_cell")})
    cell_count: float = field(metadata={"endpoint": SummaryEndpoint(
        "Detected cells / control", "Number of Cells (Neurite Outgrowth)", "number_of_cells")})
    total_outgrowth: float = field(metadata={"endpoint": SummaryEndpoint(
        "Total outgrowth / control", "Total Outgrowth (Neurite Outgrowth)", "total_outgrowth")})
    branches_per_cell: float = field(metadata={"endpoint": SummaryEndpoint(
        "Branches per cell / control", "Mean Branches Per Cell (Neurite Outgrowth)", "mean_branches_per_cell")})
    mean_process_length: float = field(metadata={"endpoint": CellMeanEndpoint(
        "Mean cell process length / control", "Cell: Mean Process Length (Neurite Outgrowth)", "mean_process_length")})
    median_process_length: float = field(metadata={"endpoint": CellMeanEndpoint(
        "Mean cell median process length / control", "Cell: Median Process Length (Neurite Outgrowth)", "median_process_length")})


METRICS = tuple(field.name for field in fields(WellEndpoints))
DEFAULT_METRICS = ("mean_outgrowth", "cell_count")


def endpoint_declarations():
    return {item.name: item.metadata["endpoint"] for item in fields(WellEndpoints)}


def read_rows(path):
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))


def write_rows(path, rows):
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=tuple(rows[0]), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


@dataclass(frozen=True)
class NativeSummary:
    """The measured endpoint projection of one exported native plane."""

    coordinate_unit: ClassVar[str] = "micrometers"
    well: str
    site: str | None
    endpoints: WellEndpoints

    @staticmethod
    def cells_path(path):
        return path.with_name(path.name.replace("_neurite_outgrowth_summary_", "_neurite_outgrowth_cells_"))

    @classmethod
    def read(cls, path):
        rows = read_rows(path)
        if len(rows) != 1:
            raise ValueError(f"Expected one native plane summary: {path}")
        row = rows[0]
        if (int(row["neurite_channel_index"]), int(row["cell_body_channel_index"]),
                int(row["nuclear_channel_index"])) != (1, 1, 0):
            raise ValueError(f"Unexpected channel assignment: {path}")
        if row["coordinate_unit"] != cls.coordinate_unit:
            raise ValueError(f"Expected calibrated micrometer measurements: {path}")
        count, length = int(row["number_of_cells"]), float(row["total_outgrowth"])
        measured_mean = float(row["mean_outgrowth_per_cell"])
        if count <= 0 or not math.isfinite(length) or not math.isfinite(measured_mean):
            raise ValueError(f"No valid per-cell length denominator: {path}")
        if not math.isclose(length / count, measured_mean, rel_tol=1e-9):
            raise ValueError(f"Inconsistent mean outgrowth: {path}")
        if (int(row["z_index"]), int(row["timepoint"])) != (1, 1):
            raise ValueError(f"Unexpected acquisition plane: {path}")
        cells = read_rows(cls.cells_path(path))
        if len(cells) != count or len({int(cell["cell"]) for cell in cells}) != count:
            raise ValueError(f"Cell identities disagree with summary: {path}")
        if any(cell["coordinate_unit"] != cls.coordinate_unit or
               cell["well"] != row["well"] or cell.get("site") != row.get("site")
               for cell in cells):
            raise ValueError(f"Cell measurements use another source or calibration: {path}")
        for cell_column, summary_column in (("total_outgrowth", "total_outgrowth"),
                                            ("branches", "total_branches")):
            if not math.isclose(sum(float(cell[cell_column]) for cell in cells),
                                float(row[summary_column]), rel_tol=1e-9, abs_tol=1e-9):
                raise ValueError(f"Cell {cell_column} does not reconcile to summary: {path}")
        if not math.isclose(float(row["total_branches"]) / count,
                            float(row["mean_branches_per_cell"]), rel_tol=1e-9):
            raise ValueError(f"Inconsistent branch denominator: {path}")
        values = {name: declaration.native_value(row, cells)
                  for name, declaration in endpoint_declarations().items()}
        if not all(math.isfinite(value) and value >= 0 for value in values.values()):
            raise ValueError(f"Invalid native endpoint: {path}")
        return cls(row["well"], row.get("site"), WellEndpoints(**values))


class WellAggregation(ABC):
    """Each sampling protocol owns its well endpoint and coverage rule."""

    name: str
    description: str
    figure_label: str
    process_length_description: str
    total_outgrowth_description: str

    @abstractmethod
    def aggregate(self, rows):
        """Return well endpoints without silently changing sampled area."""

    def load(self, summaries):
        grouped, paths = {}, []
        for path in sorted(summaries.glob("*_neurite_outgrowth_summary_*details.csv")):
            row = NativeSummary.read(path)
            grouped.setdefault(row.well, []).append(row)
            paths.append(path)
            paths.append(NativeSummary.cells_path(path))
        return {well: self.aggregate(rows) for well, rows in grouped.items()}, paths


class MosaicWellAggregation(WellAggregation):
    name = "mosaic"
    description = "OpenHCS mosaic total length / detected cells; MetaXpress well export"
    figure_label = "Stitched-mosaic well means from a fixed-pipeline transfer evaluation"
    process_length_description = "Mean of per-cell mean/median root-partition lengths in the mosaic; not pooled segment statistics. MetaXpress cell-summary aggregation is not declared."
    total_outgrowth_description = "Total traced length in the site-collapsed mosaic, not a sum of overlapping field totals."

    def aggregate(self, rows):
        if len(rows) != 1 or rows[0].site is not None:
            raise ValueError("Mosaic protocol requires exactly one site-collapsed summary per well")
        row = rows[0]
        return row.endpoints


class SiteMeanWellAggregation(WellAggregation):
    name = "site-mean"
    description = "Unweighted mean of nine native site endpoints; MetaXpress well export"
    figure_label = "Nine-field well means from a fixed-pipeline transfer evaluation"
    process_length_description = "Mean of per-cell mean/median root-partition lengths within each site, then unweighted site mean; not pooled segment statistics. MetaXpress cell-summary aggregation is not declared."
    total_outgrowth_description = "Unweighted mean of field totals; overlap is not deduplicated and field totals are not summed as unique-well length."

    def aggregate(self, rows):
        if len(rows) != 9 or {row.site for row in rows} != {str(site) for site in range(1, 10)}:
            raise ValueError("Site-mean protocol requires nine unique measured sites, 1–9, for each well")
        return WellEndpoints(**{metric: mean(getattr(row.endpoints, metric) for row in rows)
                                for metric in METRICS})


def reference_rows(reference, workbook, metrics):
    """Use the existing well metadata; decode original workbook endpoints once."""
    rows = read_rows(reference)
    if workbook is not None:
        from openpyxl import load_workbook
        book = load_workbook(workbook, read_only=True, data_only=True)
        try:
            wanted = {(row["excel_sheet"], int(row["excel_row"])): row for row in rows}
            declarations = endpoint_declarations()
            for sheet in book:
                headers = None
                for number, values in enumerate(sheet.iter_rows(values_only=True), 1):
                    if "Number of Cells (Neurite Outgrowth)" in values:
                        headers = values
                    target = wanted.get((sheet.title, number))
                    if target is None:
                        continue
                    if headers is None or values[0] != target["well"]:
                        raise ValueError(f"Workbook source row identity changed: {sheet.title}/{number}")
                    for metric in metrics:
                        target[metric] = values[headers.index(declarations[metric].reference_column)]
                    del wanted[(sheet.title, number)]
            if wanted:
                raise ValueError("Reference metadata names missing workbook rows")
        finally:
            book.close()
    for row in rows:
        for metric in metrics:
            if metric not in row or not math.isfinite(float(row[metric])) or float(row[metric]) < 0:
                raise ValueError(f"Missing or invalid reference endpoint {metric}: {row['plate']}/{row['well']}")
    return rows


def compare(reference, key, summaries, output, aggregation, coded_plate, pipeline,
            *, metrics=DEFAULT_METRICS, workbook=None):
    inputs = [reference, key, pipeline]
    if workbook is not None:
        inputs.append(workbook)
    mapping = {}
    for image in json.loads(key.read_text())["images"]:
        plate, filename = image["coded_relative_path"].split("/")
        coded_well = filename.split("_")[0]
        # Original acquisition directory, not the randomized coded plate,
        # carries physical plate identity.
        physical_plate = Path(image["source_path"]).parents[1].name.rsplit("_", 1)[1]
        identity = (physical_plate, image["source_well"])
        coded = (plate, coded_well)
        if coded in mapping and mapping[coded] != identity:
            raise ValueError(f"Inconsistent source identity: {coded}")
        mapping[coded] = identity
    measured, paths = aggregation.load(summaries)
    native = {mapping[(coded_plate, well)]: asdict(endpoints) for well, endpoints in measured.items()}
    if len(native) != len(measured):
        raise ValueError("Multiple coded wells map to the same physical well")
    inputs.extend(paths)
    joined = []
    for row in reference_rows(reference, workbook, metrics):
        identity = (row["plate"], row["well"])
        if identity not in native:
            continue
        joined.append({**row, **{f"openhcs_{metric}": native[identity][metric]
                                for metric in metrics}})
    effects = []
    for condition in dict.fromkeys(row["condition"] for row in joined):
        curve = [row for row in joined if row["condition"] == condition]
        control = [row for row in curve if float(row["nominal_dose_uM"]) == 0]
        if len(control) != 2:
            raise ValueError(f"Missing curve-specific controls: {condition}")
        for dose in (0, 5, 10, 20, 40):
            drug = [row for row in curve if float(row["nominal_dose_uM"]) == dose]
            if len(drug) != 2:
                raise ValueError(f"Missing technical replicate: {condition}/{dose}")
            for metric in metrics:
                result = {"plate": drug[0]["plate"], "condition": condition,
                          "dose_uM": dose, "metric": metric,
                          "baseline_wells": ";".join(row["well"] for row in control),
                          "treatment_wells": ";".join(row["well"] for row in drug),
                          "n_control": len(control), "n_treatment": len(drug)}
                for method, column in (("metaxpress", metric), ("openhcs", f"openhcs_{metric}")):
                    control_points = [float(row[column]) for row in control]
                    baseline = mean(control_points)
                    points = [float(row[column]) for row in drug]
                    if baseline <= 0 or not all(math.isfinite(value) for value in (baseline, *points)):
                        raise ValueError(f"Invalid measurements: {condition}/{dose}/{metric}")
                    value = mean(points)
                    result.update({f"{method}_control_mean": baseline,
                                   f"{method}_control_sd": stdev(control_points),
                                   f"{method}_treatment_mean": value,
                                   f"{method}_treatment_sd": stdev(points),
                                   f"{method}_delta": value - baseline,
                                   f"{method}_fold_change": value / baseline,
                                   f"{method}_fractional_change": value / baseline - 1})
                result["fractional_change_difference"] = result["openhcs_fractional_change"] - result["metaxpress_fractional_change"]
                effects.append(result)
    output.mkdir(parents=True, exist_ok=True)
    write_rows(output / "joined_wells.csv", joined)
    write_rows(output / "treatment_effects.csv", effects)
    hashes = {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in inputs}
    (output / "source_evidence.json").write_text(json.dumps({
        "sources_sha256": hashes, "matched_wells": len(joined),
        "comparison": "fixed-run treatment evaluation; not a manual accuracy score",
        "aggregation_protocol": aggregation.name,
        "aggregation": aggregation.description,
        "coded_plate": coded_plate,
        "metrics": list(metrics),
        "process_length_aggregation": aggregation.process_length_description,
        "total_outgrowth_aggregation": aggregation.total_outgrowth_description,
        "coordinate_unit": NativeSummary.coordinate_unit,
        "pipeline_source": str(pipeline),
        "protocol_figure_label": aggregation.figure_label,
        "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "baseline": "each drug curve's own zero-dose DMSO wells",
    }, indent=2) + "\n")
    print(f"Compared {len(joined)} physical wells; wrote {len(effects)} endpoint/dose rows to {output}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("reference", "key", "summaries", "output", "pipeline"):
        parser.add_argument(f"--{name}", type=Path, required=True)
    parser.add_argument("--coded-plate", required=True,
                        help="Source plate identity in the evaluation key, not the output directory name")
    parser.add_argument("--metrics", nargs="+", choices=METRICS, default=DEFAULT_METRICS)
    parser.add_argument("--reference-workbook", type=Path,
                        help="Original workbook supplies selected endpoints at the CSV's retained Excel row identities.")
    protocols = {protocol.name: protocol for protocol in WellAggregation.__subclasses__()}
    parser.add_argument("--aggregation", choices=protocols, required=True)
    args = parser.parse_args()
    compare(args.reference, args.key, args.summaries, args.output,
            protocols[args.aggregation](), args.coded_plate, args.pipeline,
            metrics=tuple(args.metrics), workbook=args.reference_workbook)
