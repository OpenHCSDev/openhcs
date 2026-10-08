"""Small declared-summary fixtures; never open retained scientific results."""

import csv
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SOURCE = Path(__file__).resolve().parents[2] / "paper/figures/compare_personal_neurite.py"
SPEC = importlib.util.spec_from_file_location("personal_neurite_comparator", SOURCE)
evaluator = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = evaluator
SPEC.loader.exec_module(evaluator)


class GuidedComparisonTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="neurite-comparator-fixture-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.blind, self.guided = self.root / "blind", self.root / "guided"
        self.blind.mkdir()
        self.guided.mkdir()
        self.pipeline = self.root / "pipeline.py"
        self.pipeline.write_text("# Synthetic declaration fixture, not a scientific pipeline\n")
        self.guided_pipeline = self.root / "guided.py"
        self.guided_pipeline.write_text("# Distinct guided declaration fixture\n")
        self.reference, self.key = self.root / "reference.csv", self.root / "key.json"
        images, reference = [], []
        for number in range(1, 11):
            well = f"A{number:02}"
            dose = (0, 5, 10, 20, 40)[(number - 1) // 2]
            length, branches = 100 + dose, 2 + dose // 5
            endpoint = evaluator.WellEndpoints(length, 1, length, branches,
                                              length / 2, length / 2, branches, 2, branches / 2)
            reference.append({"plate": "physical", "well": well, "condition": "fixture",
                              "nominal_dose_uM": dose, **evaluator.asdict(endpoint)})
            images.append({"coded_relative_path": f"P001/{well}_w1.tif",
                           "source_path": f"/fixture/acquisition_physical/Images/{well}_w1.tif",
                           "source_well": well})
            for site in range(1, 10):
                self.write_plane(self.blind, well, site, length, branches)
                self.write_plane(self.guided, well, site, length * 2, branches * 2)
        evaluator.write_rows(self.reference, reference)
        self.key.write_text(json.dumps({"images": images}))

    def write_plane(self, directory, well, site, length, branches, processes=2, unit="micrometers"):
        path = directory / f"{well}_s{site}_neurite_outgrowth_summary_plane_details.csv"
        evaluator.write_rows(path, [{"well": well, "site": str(site), "z_index": 1,
                                    "timepoint": 1, "neurite_channel_index": 1,
                                    "cell_body_channel_index": 1, "nuclear_channel_index": 0,
                                    "coordinate_unit": unit, "number_of_cells": 1,
                                    "total_outgrowth": length, "mean_outgrowth_per_cell": length,
                                    "total_branches": branches, "mean_branches_per_cell": branches,
                                    "total_processes": processes}])
        evaluator.write_rows(evaluator.NativeSummary.cells_path(path), [
            {"well": well, "site": str(site), "cell": 1, "coordinate_unit": unit,
             "total_outgrowth": length, "branches": branches, "processes": processes,
             "mean_process_length": length / processes if processes else 0,
             "median_process_length": length / processes if processes else 0}])

    def compare(self, output, **options):
        return evaluator.compare(self.reference, self.key, self.blind, output,
                                 evaluator.SiteMeanWellAggregation(), "P001", self.pipeline,
                                 **options)

    def guided_options(self):
        return {"guided_summaries": self.guided, "guided_pipeline": self.guided_pipeline,
                "guided_label": "Scientist-guided fixture"}

    def test_actual_cli_legacy_and_three_methods(self):
        common = [sys.executable, str(SOURCE), "--reference", str(self.reference),
                  "--key", str(self.key), "--summaries", str(self.blind),
                  "--pipeline", str(self.pipeline), "--coded-plate", "P001",
                  "--aggregation", "site-mean"]
        legacy, paired = self.root / "legacy", self.root / "paired"
        subprocess.run([*common, "--output", str(legacy)], check=True, capture_output=True, text=True)
        subprocess.run([*common, "--output", str(paired), "--guided-summaries", str(self.guided),
                        "--guided-pipeline", str(self.guided_pipeline),
                        "--guided-label", "Scientist-guided fixture"],
                       check=True, capture_output=True, text=True)
        old_effects = evaluator.read_rows(legacy / "treatment_effects.csv")
        self.assertEqual(len(old_effects), 10)
        self.assertFalse((legacy / "paired_sites.csv").exists())
        self.assertEqual(set(old_effects[0]), {
            "plate", "condition", "dose_uM", "metric", "baseline_wells", "treatment_wells",
            "n_control", "n_treatment", "fractional_change_difference",
            *[f"{method}_{field}" for method in ("metaxpress", "openhcs")
              for field in ("control_mean", "control_sd", "treatment_mean", "treatment_sd",
                            "delta", "fold_change", "fractional_change")]})
        effects = evaluator.read_rows(paired / "treatment_effects.csv")
        self.assertEqual(len(effects), 5 * len(evaluator.METRICS))
        length = next(row for row in effects if row["metric"] == "total_outgrowth" and row["dose_uM"] == "40")
        for method in ("metaxpress", "openhcs", "guided_openhcs"):
            self.assertEqual(float(length[f"{method}_fold_change"]), 1.4)
            self.assertEqual(length[f"{method}_direction"], "increase")
        self.assertEqual(length["baseline_wells"], "A01;A02")
        sites = evaluator.read_rows(paired / "paired_sites.csv")
        self.assertEqual(len(sites), 90)
        self.assertEqual(float(sites[0]["guided_over_blind_total_outgrowth"]), 2)
        self.assertEqual(float(sites[0]["guided_minus_blind_total_outgrowth"]), 100)
        wells = evaluator.read_rows(paired / "joined_wells.csv")
        self.assertEqual(len(wells), 10)
        self.assertEqual(float(wells[0]["guided_openhcs_cell_count"]), 1)
        evidence = json.loads((paired / "source_evidence.json").read_text())
        self.assertEqual(evidence["guided_openhcs"]["matched_sites"], 90)
        self.assertIn(str(self.guided_pipeline), evidence["sources_sha256"])
        self.assertIn(str(self.pipeline), evidence["sources_sha256"])
        self.assertEqual(evidence["aggregation_protocol"], "site-mean")
        self.assertEqual(evidence["endpoint_units"]["total_outgrowth"], "micrometers")

    def test_pair_requires_complete_labelled_input(self):
        with self.assertRaisesRegex(ValueError, "explicit label"):
            self.compare(self.root / "bad", guided_summaries=self.guided)
        self.assertFalse((self.root / "bad").exists())

    def test_coverage_units_protocol_and_reconciliation(self):
        path = self.guided / "A01_s9_neurite_outgrowth_summary_plane_details.csv"
        original = path.read_text()
        path.unlink()
        with self.assertRaisesRegex(ValueError, "coverage must match"):
            self.compare(self.root / "bad", **self.guided_options())
        path.write_text(original)
        self.write_plane(self.guided, "A01", 9, 200, 4, unit="pixels")
        with self.assertRaisesRegex(ValueError, "calibrated micrometer"):
            self.compare(self.root / "bad", **self.guided_options())
        self.write_plane(self.guided, "A01", 9, 200, 4)
        with self.assertRaisesRegex(ValueError, "site-collapsed"):
            evaluator.MosaicWellAggregation().load(self.guided)
        cells_path = evaluator.NativeSummary.cells_path(path)
        rows = evaluator.read_rows(cells_path)
        rows[0]["branches"] = 999
        evaluator.write_rows(cells_path, rows)
        with self.assertRaisesRegex(ValueError, "does not reconcile"):
            self.compare(self.root / "bad", **self.guided_options())
        self.assertFalse((self.root / "bad").exists())

    def test_undefined_ratio_and_zero_baseline_are_not_zero_folds(self):
        for well in ("A01", "A02"):
            self.write_plane(self.guided, well, 1, 200, 4, processes=0)
        output = self.root / "undefined"
        self.compare(output, **self.guided_options())
        effects = evaluator.read_rows(output / "treatment_effects.csv")
        ratio = next(row for row in effects if row["metric"] == "branches_per_process")
        self.assertEqual(ratio["guided_openhcs_fold_change"], "")
        self.assertEqual(ratio["guided_openhcs_direction"], "undefined")
        branch_endpoint = evaluator.endpoint_declarations()["total_branches"]
        effect = branch_endpoint.treatment_effect([0, 0], [1, 1], allow_undefined=True)
        self.assertIsNone(effect["fold_change"])
        self.assertEqual(effect["direction"], "increase")
        with self.assertRaises(ValueError):
            branch_endpoint.treatment_effect([0, 0], [1, 1])


if __name__ == "__main__":
    unittest.main()
