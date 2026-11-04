"""Audit frozen branching tables without rerunning or changing an image analysis."""
from collections import defaultdict
import argparse
import hashlib
import json
from math import isclose
from pathlib import Path
from statistics import mean
import sys
import subprocess

ROOT = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--workbook", type=Path, required=True)
parser.add_argument("--output", type=Path, required=True)
arguments = parser.parse_args()
workbook = arguments.workbook.resolve()
sys.path.insert(0, str(ROOT / "paper/figures"))
from compare_personal_neurite import RatioEndpoint, endpoint_declarations, read_rows, reference_rows

COHORT = ROOT / "paper/supplementary/personal_neurite_autonomous"
record = json.loads((COHORT / "cohort.json").read_text())
provenance_path = COHORT / record["authors"][0]["tables"] / "source_evidence.json"
provenance = json.loads(provenance_path.read_text())["sources_sha256"]
expected_workbook_hash, = [digest for path, digest in provenance.items() if Path(path).suffix == ".xlsx"]
if hashlib.sha256(workbook.read_bytes()).hexdigest() != expected_workbook_hash:
    raise ValueError("The supplied workbook differs from the frozen source record")
inputs = [COHORT / "cohort.json", provenance_path, workbook]
branching = endpoint_declarations()["branches_per_cell"]
reference = None
methods = []
for author in record["authors"]:
    folder = COHORT / author["tables"]
    paths = [folder / name for name in ("paired_sites.csv", "joined_wells.csv", "treatment_effects.csv")]
    inputs.extend(paths)
    sites, wells, effects = map(read_rows, paths)
    workbook_rows = reference_rows(paths[1], workbook, tuple(endpoint_declarations()))
    for saved, original in zip(wells, workbook_rows, strict=True):
        for metric in endpoint_declarations():
            assert isclose(float(saved[metric]), float(original[metric]), rel_tol=1e-9, abs_tol=1e-9)
    grouped = defaultdict(list)
    assert len(sites) == 180 and len(wells) == 20
    errors = []
    for site in sites:
        assert site["coordinate_unit"] == "micrometers"
        branches = float(site["openhcs_total_branches"])
        cells = float(site["openhcs_cell_count"])
        exported = float(site["openhcs_branches_per_cell"])
        assert cells > 0
        error = abs(RatioEndpoint.ratio(branches, cells) - exported)
        errors.append(error)
        assert isclose(branches / cells, exported, rel_tol=1e-9, abs_tol=1e-9)
        grouped[site["plate"], site["well"]].append(site)
    alternative = {}
    differences = []
    for well in wells:
        points = grouped[well["plate"], well["well"]]
        assert len(points) == 9 and {int(p["site"]) for p in points} == set(range(1, 10))
        site_mean = mean(float(p["openhcs_branches_per_cell"]) for p in points)
        assert isclose(site_mean, float(well["openhcs_branches_per_cell"]), rel_tol=1e-9)
        pooled = RatioEndpoint.ratio(sum(float(p["openhcs_total_branches"]) for p in points),
                                    sum(float(p["openhcs_cell_count"]) for p in points))
        alternative[well["plate"], well["well"]] = pooled
        differences.append(abs(pooled - site_mean))
    vendor_rows = [{key: well[key] for key in (
        "plate", "well", "condition", "nominal_dose_uM", "excel_sheet", "excel_row",
        "branches_per_cell", "total_branches", "cell_count", "total_processes", "branches_per_process"
    )} for well in wells]
    assert reference is None or vendor_rows == reference
    reference = vendor_rows
    dose_effects = []
    for condition in sorted({w["condition"] for w in wells}):
        controls = [w for w in wells if w["condition"] == condition and float(w["nominal_dose_uM"]) == 0]
        treated = [w for w in wells if w["condition"] == condition and float(w["nominal_dose_uM"]) == 40]
        assert len(controls) == len(treated) == 2
        original = branching.treatment_effect([float(w["openhcs_branches_per_cell"]) for w in controls],
                                             [float(w["openhcs_branches_per_cell"]) for w in treated])
        pooled = branching.treatment_effect([alternative[w["plate"], w["well"]] for w in controls],
                                           [alternative[w["plate"], w["well"]] for w in treated])
        vendor = branching.treatment_effect([float(w["branches_per_cell"]) for w in controls],
                                           [float(w["branches_per_cell"]) for w in treated])
        vendor_total_ratio = branching.treatment_effect(
            [RatioEndpoint.ratio(float(w["total_branches"]), float(w["cell_count"])) for w in controls],
            [RatioEndpoint.ratio(float(w["total_branches"]), float(w["cell_count"])) for w in treated])
        saved, = [e for e in effects if e["condition"] == condition and e["metric"] == "branches_per_cell" and float(e["dose_uM"]) == 40]
        assert isclose(original["delta"], float(saved["openhcs_delta"]), rel_tol=1e-9)
        assert isclose(vendor["delta"], float(saved["metaxpress_delta"]), rel_tol=1e-9)
        dose_effects.append({"condition": condition, "dose_uM": 40,
                            "openhcs_exported_site_mean": original, "openhcs_cell_pooled_sensitivity": pooled,
                            "metaxpress_exported": vendor, "metaxpress_exported_total_ratio_sensitivity": vendor_total_ratio})
    methods.append({"analysis": author["label"], "matched_sites": len(sites), "matched_wells": len(wells),
                    "max_site_formula_error": max(errors), "max_well_pooling_difference": max(differences),
                    "dose_effects": dose_effects})
report = {
    "analysis_rerun": False,
    "scope": "Saved540 matched site records and60 method-well records; arithmetic sensitivity only, no images processed or records changed.",
    "sources_sha256": {str(p.resolve()): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs},
    "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    "frozen_software_commit": record["frozen_software_commit"],
    "original_workbook_endpoints_checked": 20 * len(endpoint_declarations()) * len(methods),
    "original_workbook_sha256_matches_retained_provenance": hashlib.sha256(workbook.read_bytes()).hexdigest() == expected_workbook_hash,
    "frozen_source_sha256": hashlib.sha256(subprocess.check_output(
        ["git", "show", f"{record['frozen_software_commit']}:openhcs/processing/backends/analysis/neurite_outgrowth.py"], cwd=ROOT
    )).hexdigest(),
    "units": {name: definition.unit for name, definition in endpoint_declarations().items()},
    "methods": methods,
    "reference_wells": reference,
    "limits": ["The pooled alternatives are sensitivity calculations, not replacement scientific measurements.",
               "Vendor exported mean branches/cell and its exported totals are distinct recorded endpoints; their internal aggregation is not inferred from disagreement.",
               "Frozen OpenHCS branches are qualified, owner-specific junction clusters, not graph paths, roots or branch-segment counts.",
               "No biological ground-truth tracing or vendor-internal topology implementation is supplied by these tables."]
}
output = arguments.output.resolve()
if output in {path.resolve() for path in inputs}:
    raise ValueError("The diagnostic output must not overwrite a scientific input")
output.parent.mkdir(parents=True, exist_ok=True)
output.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({"report": str(output), "sites_checked": sum(m["matched_sites"] for m in methods),
                  "maximum_site_formula_error": max(m["max_site_formula_error"] for m in methods),
                  "effects": [{"analysis": m["analysis"], "condition": e["condition"],
                               "site_mean_delta": e["openhcs_exported_site_mean"]["delta"],
                               "pooled_delta": e["openhcs_cell_pooled_sensitivity"]["delta"],
                               "reference_delta": e["metaxpress_exported"]["delta"],
                               "reference_total_ratio_delta": e["metaxpress_exported_total_ratio_sensitivity"]["delta"]}
                              for m in methods for e in m["dose_effects"]]}, indent=2))
