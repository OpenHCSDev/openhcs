"""Compare retained well measurements, without processing or tuning images.

The identity key is evaluation-only: never give it to a blind analysis author.
This entrypoint deliberately selects one retained mosaic run, not a mixture of
attempts. Its outputs do not establish segmentation accuracy or autonomous
acceptance. MetaXpress site averaging and OpenHCS mosaic measurement differ.
"""

import argparse
import csv
import hashlib
import json
import math
from pathlib import Path
from statistics import mean, stdev


METRICS = {
    "mean_outgrowth": "mean_outgrowth_per_cell_um",
    "cell_count": "number_of_cells",
}


def read_rows(path):
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))


def write_rows(path, rows):
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=tuple(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def compare(reference, key, summaries, output):
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
    native = {}
    for path in sorted(summaries.glob("*_neurite_outgrowth_summary_*details.csv")):
        records = read_rows(path)
        if len(records) != 1:
            raise ValueError(f"Expected one mosaic summary: {path}")
        row = records[0]
        if "site" in row or "_site-" in path.name:
            raise ValueError("Field summaries require a declared site aggregation, not this mosaic comparison")
        identity = mapping[(summaries.parent.name.removesuffix("_openhcs"), row["well"])]
        if identity in native:
            raise ValueError(f"Duplicate well: {identity}")
        if (int(row["neurite_channel_index"]), int(row["nuclear_channel_index"])) != (1, 0):
            raise ValueError(f"Unexpected channel assignment: {path}")
        count, length = float(row["number_of_cells"]), float(row["total_outgrowth_um"])
        if count <= 0 or not math.isclose(length / count, float(row["mean_outgrowth_per_cell_um"]), rel_tol=1e-9):
            raise ValueError(f"Inconsistent mean outgrowth: {path}")
        native[identity] = row
        inputs.append(path)
    joined = []
    for row in read_rows(reference):
        identity = (row["plate"], row["well"])
        if identity not in native:
            continue
        joined.append({**row, **{f"openhcs_{metric}": native[identity][column]
                                for metric, column in METRICS.items()}})
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
        "comparison": "retained mosaic-run evaluation; not current field-pipeline validation",
        "aggregation": "MetaXpress well export versus OpenHCS mosaic total length / detected cells",
        "baseline": "each drug curve's own zero-dose DMSO wells",
    }, indent=2) + "\n")
    print(f"Compared {len(joined)} physical wells; wrote {len(effects)} endpoint/dose rows to {output}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("reference", "key", "summaries", "output"):
        parser.add_argument(f"--{name}", type=Path, required=True)
    args = parser.parse_args()
    compare(args.reference, args.key, args.summaries, args.output)
