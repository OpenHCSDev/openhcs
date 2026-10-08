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

    def write_plane(self, directory, well, site, length, branches, processes=2, unit="micrometers", empty=False):
        path = directory / f"{well}_s{site}_neurite_outgrowth_summary_plane_details.csv"
        evaluator.write_rows(path, [{"well": well, "site": str(site), "z_index": 1,
                                    "timepoint": 1, "neurite_channel_index": 1,
                                    "cell_body_channel_index": 1, "nuclear_channel_index": 0,
                                    "coordinate_unit": unit, "number_of_cells": 0 if empty else 1,
                                    "total_outgrowth": length, "mean_outgrowth_per_cell": 0 if empty else length,
                                    "total_branches": branches, "mean_branches_per_cell": 0 if empty else branches,
                                    "total_processes": processes}])
        cell = {"well": well, "site": str(site), "cell": 1, "coordinate_unit": unit,
                "total_outgrowth": length, "branches": branches, "processes": processes,
                "mean_process_length": length / processes if processes else 0,
                "median_process_length": length / processes if processes else 0}
        with evaluator.NativeSummary.cells_path(path).open("w", newline="") as stream:
            writer = csv.DictWriter(stream, fieldnames=tuple(cell))
            writer.writeheader()
            writer.writerows([] if empty else [cell])

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
        effect = branch_endpoint.treatment_effect([0, 0], [1, 1])
        self.assertIsNone(effect["fold_change"])
        self.assertEqual(effect["direction"], "increase")

    def test_complete_empty_field_keeps_zero_totals_and_undefined_means(self):
        self.write_plane(self.blind, "A01", 1, 0, 0, processes=0, empty=True)
        planes, _ = evaluator.SiteMeanWellAggregation().load_planes(self.blind)
        self.assertEqual(len(planes), 90)
        empty = planes[("A01", "1")].endpoints
        for metric in ("cell_count", "total_outgrowth", "total_branches", "total_processes"):
            self.assertEqual(getattr(empty, metric), 0)
        for metric in ("mean_outgrowth", "branches_per_cell", "mean_process_length",
                       "median_process_length", "branches_per_process"):
            self.assertIsNone(getattr(empty, metric))
        wells = evaluator.SiteMeanWellAggregation().aggregate_planes(planes)
        self.assertEqual(wells["A01"].cell_count, 8 / 9)
        self.assertIsNone(wells["A01"].mean_outgrowth)
        # Undefined endpoints must not depend on whether a guided run is present.
        old, paired = self.root / "empty_legacy", self.root / "empty_paired"
        self.compare(old)
        self.compare(paired, **self.guided_options())
        for output in (old, paired):
            row = evaluator.read_rows(output / "joined_wells.csv")[0]
            self.assertEqual(row["openhcs_mean_outgrowth"], "")
            effects = evaluator.read_rows(output / "treatment_effects.csv")
            effect = next(row for row in effects if row["metric"] == "mean_outgrowth")
            self.assertEqual(effect["openhcs_fold_change"], "")
        self.assertEqual(len(evaluator.read_rows(paired / "paired_sites.csv")), 90)
        self.write_plane(self.blind, "A01", 1, 1, 0, processes=0, empty=True)
        with self.assertRaisesRegex(ValueError, "reconcile"):
            evaluator.NativeSummary.read(self.blind / "A01_s1_neurite_outgrowth_summary_plane_details.csv")
        self.write_plane(self.blind, "A01", 1, 0, 0, processes=0, empty=True)
        summary = self.blind / "A01_s1_neurite_outgrowth_summary_plane_details.csv"
        evaluator.NativeSummary.cells_path(summary).write_text("")
        with self.assertRaisesRegex(ValueError, "Missing CSV header"):
            evaluator.NativeSummary.read(summary)

    def test_missing_csv_ratio_is_not_known_undefined_but_workbook_zero_is(self):
        rows = evaluator.read_rows(self.reference)
        for missing in ("", None):
            if missing is None:
                rows[0].pop("branches_per_process", None)
                # CSV with an absent column is a different missing-input case.
                evaluator.write_rows(self.root / "missing.csv", [{k: v for k, v in row.items()
                                                                   if k != "branches_per_process"} for row in rows])
            else:
                rows[0]["branches_per_process"] = missing
                evaluator.write_rows(self.root / "missing.csv", rows)
            with self.assertRaisesRegex(ValueError, "Missing or invalid reference"):
                evaluator.reference_rows(self.root / "missing.csv", None, ("branches_per_process",))
        from openpyxl import Workbook
        book = Workbook()
        sheet = book.active
        sheet.title = "Synthetic"
        sheet.append(["Well", "Number of Cells (Neurite Outgrowth)",
                      "Total Branches (Neurite Outgrowth)", "Total Processes (Neurite Outgrowth)"])
        sheet.append(["A01", 1, 4, 0])
        sheet.append(["A02", 1, 6, 2])
        workbook = self.root / "synthetic.xlsx"
        book.save(workbook)
        book.close()
        metadata = self.root / "workbook_metadata.csv"
        evaluator.write_rows(metadata, [{"plate": "physical", "well": well,
                                         "excel_sheet": "Synthetic", "excel_row": row}
                                        for well, row in (("A01", 2), ("A02", 3))])
        decoded = evaluator.reference_rows(metadata, workbook, ("branches_per_process",))
        self.assertIsNone(decoded[0]["branches_per_process"])
        self.assertEqual(decoded[1]["branches_per_process"], 3)


if __name__ == "__main__":
    unittest.main()
