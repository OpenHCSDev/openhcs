"""Compare retained well measurements, without processing or tuning images.

The identity key is evaluation-only: never give it to a blind analysis author.
This entrypoint selects one run and an explicit well-aggregation protocol, never
a mixture of attempts. Its outputs do not establish segmentation accuracy.
"""

import argparse
from abc import ABC, abstractmethod
import csv
from dataclasses import asdict, dataclass, fields
import hashlib
import json
import math
from pathlib import Path
from statistics import mean, stdev


@dataclass(frozen=True)
class WellEndpoints:
    mean_outgrowth: float
    cell_count: float


METRICS = tuple(field.name for field in fields(WellEndpoints))


def read_rows(path):
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))


def write_rows(path, rows):
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=tuple(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


@dataclass(frozen=True)
class NativeSummary:
    """The measured endpoint projection of one exported native plane."""

    well: str
    site: str | None
    cell_count: int
    mean_outgrowth: float

    @classmethod
    def read(cls, path):
        rows = read_rows(path)
        if len(rows) != 1:
            raise ValueError(f"Expected one native plane summary: {path}")
        row = rows[0]
        if (int(row["neurite_channel_index"]), int(row["cell_body_channel_index"]),
                int(row["nuclear_channel_index"])) != (1, 1, 0):
            raise ValueError(f"Unexpected channel assignment: {path}")
        count, length = int(row["number_of_cells"]), float(row["total_outgrowth_um"])
        measured_mean = float(row["mean_outgrowth_per_cell_um"])
        if count <= 0 or not math.isfinite(length) or not math.isfinite(measured_mean):
            raise ValueError(f"No valid per-cell length denominator: {path}")
        if not math.isclose(length / count, measured_mean, rel_tol=1e-9):
            raise ValueError(f"Inconsistent mean outgrowth: {path}")
        if (int(row["z_index"]), int(row["timepoint"])) != (1, 1):
            raise ValueError(f"Unexpected acquisition plane: {path}")
        return cls(row["well"], row.get("site"), count, measured_mean)


class WellAggregation(ABC):
    """Each sampling protocol owns its well endpoint and coverage rule."""

    name: str
    description: str
    figure_label: str

    @abstractmethod
    def aggregate(self, rows):
        """Return well endpoints without silently changing sampled area."""

    def load(self, summaries):
        grouped, paths = {}, []
        for path in sorted(summaries.glob("*_neurite_outgrowth_summary_*details.csv")):
            row = NativeSummary.read(path)
            grouped.setdefault(row.well, []).append(row)
            paths.append(path)
        return {well: self.aggregate(rows) for well, rows in grouped.items()}, paths


class MosaicWellAggregation(WellAggregation):
    name = "mosaic"
    description = "OpenHCS mosaic total length / detected cells; MetaXpress well export"
    figure_label = "Retained mosaic measurements; not the current field pipeline"

    def aggregate(self, rows):
        if len(rows) != 1 or rows[0].site is not None:
            raise ValueError("Mosaic protocol requires exactly one site-collapsed summary per well")
        row = rows[0]
        return WellEndpoints(row.mean_outgrowth, row.cell_count)


class SiteMeanWellAggregation(WellAggregation):
    name = "site-mean"
    description = "Unweighted mean of nine native site mean-outgrowth/cell-count endpoints; MetaXpress well export"
    figure_label = "Nine-field well means from a fixed-pipeline transfer evaluation"

    def aggregate(self, rows):
        if len(rows) != 9 or {row.site for row in rows} != {str(site) for site in range(1, 10)}:
            raise ValueError("Site-mean protocol requires nine unique measured sites, 1–9, for each well")
        return WellEndpoints(mean(row.mean_outgrowth for row in rows),
                             mean(row.cell_count for row in rows))


def compare(reference, key, summaries, output, aggregation):
    inputs = [reference, key]
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
    coded_plate = summaries.parent.name.removesuffix("_openhcs")
    measured, paths = aggregation.load(summaries)
    native = {mapping[(coded_plate, well)]: asdict(endpoints) for well, endpoints in measured.items()}
    if len(native) != len(measured):
        raise ValueError("Multiple coded wells map to the same physical well")
    inputs.extend(paths)
    joined = []
    for row in read_rows(reference):
        identity = (row["plate"], row["well"])
        if identity not in native:
            continue
        joined.append({**row, **{f"openhcs_{metric}": native[identity][metric]
                                for metric in METRICS}})
    effects = []
    for condition in ("FC-A", "Y27"):
        curve = [row for row in joined if row["condition"] == condition]
        control = [row for row in curve if float(row["nominal_dose_uM"]) == 0]
        if len(control) != 2:
            raise ValueError(f"Missing curve-specific controls: {condition}")
        for dose in (0, 5, 10, 20, 40):
            drug = [row for row in curve if float(row["nominal_dose_uM"]) == dose]
            if len(drug) != 2:
                raise ValueError(f"Missing technical replicate: {condition}/{dose}")
            for metric in METRICS:
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
        "protocol_figure_label": aggregation.figure_label,
        "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "baseline": "each drug curve's own zero-dose DMSO wells",
    }, indent=2) + "\n")
    print(f"Compared {len(joined)} physical wells; wrote {len(effects)} endpoint/dose rows to {output}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("reference", "key", "summaries", "output"):
        parser.add_argument(f"--{name}", type=Path, required=True)
    protocols = {protocol.name: protocol for protocol in WellAggregation.__subclasses__()}
    parser.add_argument("--aggregation", choices=protocols, required=True)
    args = parser.parse_args()
    compare(args.reference, args.key, args.summaries, args.output, protocols[args.aggregation]())
