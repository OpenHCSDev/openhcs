"""Plot frozen well endpoints and matched eligibility; no image analysis."""

from abc import ABC, abstractmethod
from dataclasses import dataclass
import json
from math import isclose, isfinite
from pathlib import Path
from statistics import mean, stdev

from build_slas_visual_story import BLUE, TEAL, INK, MUTED, ROOT, FigureSheet


SOURCE = ROOT / "paper/supplementary/task_only_analysis/bbbc013-fresh23-plot-source.json"


@dataclass(frozen=True)
class WellEndpoint:
    well: str
    median_log2: float
    nuclei: int
    eligible: int

    @property
    def eligibility(self) -> float:
        return self.eligible / self.nuclei

    @classmethod
    def decode(cls, row: dict[str, str]) -> "WellEndpoint":
        endpoint = cls(row["well"], float(row["median_log2_ratio"]),
                       int(row["nucleus_count"]), int(row["eligible_count"]))
        if not isclose(endpoint.eligibility, float(row["eligibility_fraction"]), abs_tol=1e-12):
            raise ValueError(f"Eligibility disagrees with counts: {endpoint.well}")
        return endpoint


@dataclass(frozen=True)
class DoseGroup:
    concentration: float
    wells: tuple[WellEndpoint, ...]

    @classmethod
    def decode(cls, row: dict[str, str], wells: tuple[WellEndpoint, ...]) -> "DoseGroup":
        if len(wells) != int(row["well_count"]) or len(wells) != int(row["finite_well_count"]):
            raise ValueError("Dose group does not match its frozen well count")
        values = [well.median_log2 for well in wells]
        if not all(isfinite(value) for value in values):
            raise ValueError("Non-finite dose endpoint")
        checks = (
            (mean(values), float(row["mean_well_median_log2_ratio"])),
            (stdev(values), float(row["sd_well_median_log2_ratio"])),
            (min(well.eligibility for well in wells), float(row["minimum_eligibility_fraction"])),
            (sum(well.nuclei for well in wells), int(row["total_nuclei"])),
            (sum(well.eligible for well in wells), int(row["eligible_cells"])),
        )
        if not all(isclose(actual, recorded, abs_tol=1e-12) for actual, recorded in checks):
            raise ValueError("Well-derived values disagree with the frozen dose table")
        return cls(float(row["concentration"]), wells)


@dataclass(frozen=True)
class AssaySeries:
    compound: str
    unit: str
    doses: tuple[DoseGroup, ...]
    negative_control: DoseGroup
    positive_control: DoseGroup

    @property
    def control_zprime(self) -> float:
        negative = [well.median_log2 for well in self.negative_control.wells]
        positive = [well.median_log2 for well in self.positive_control.wells]
        return 1 - 3 * (stdev(negative) + stdev(positive)) / abs(mean(positive) - mean(negative))

    @classmethod
    def load(cls, path: Path) -> tuple["AssaySeries", ...]:
        """Decode the retained external tables once; rendering uses typed values."""
        card = json.loads(path.read_text())
        if (card["author_run"], card["execution"]) != ("BBBC013_FRESH23_96", "FULL_S08"):
            raise ValueError("Wrong scientific execution for this figure")
        endpoints = tuple(WellEndpoint.decode(row) for row in card["well_tables"])
        by_well = {well.well: well for well in endpoints}
        if len(endpoints) != 96 or len(by_well) != 96:
            raise ValueError("Expected 96 unique retained wells")
        design = {well: (block, role, concentration)
                  for well, block, role, concentration in card["plate_design"]}
        units = {well: unit for well, unit, treatment in card["source_metadata"]}
        grouped: dict[tuple[str, str], list[DoseGroup]] = {}
        for row in card["dose_response"]:
            if row["assay_role"] != "dose":
                continue
            block, concentration = row["assay_block"], float(row["concentration"])
            wells = tuple(sorted((well for well in endpoints
                                  if design[well.well] == (block, "dose", concentration)),
                                 key=lambda well: well.well))
            if any(units[well.well] != row["concentration_unit"] for well in wells):
                raise ValueError("Dose units disagree with retained source metadata")
            grouped.setdefault((block, row["concentration_unit"]), []).append(DoseGroup.decode(row, wells))
        def control(block: str, role: str) -> DoseGroup:
            rows = [row for row in card["dose_response"]
                    if row["assay_block"] == block and row["assay_role"] == role]
            if len(rows) != 1:
                raise ValueError("Expected one retained control group per role")
            row = rows[0]
            wells = tuple(sorted((well for well in endpoints
                                  if design[well.well] == (block, role, float(row["concentration"]))),
                                 key=lambda well: well.well))
            if len(wells) != 4:
                raise ValueError("Control separation requires four independent wells per group")
            return DoseGroup.decode(row, wells)

        series = tuple(cls(block, unit, tuple(sorted(doses, key=lambda dose: dose.concentration)),
                           control(block, "negative_control"), control(block, "positive_control"))
                       for (block, unit), doses in sorted(grouped.items()))
        if len(series) != 2 or any(len(item.doses) != 9 for item in series):
            raise ValueError("Expected two nine-dose series")
        if any(len(dose.wells) != 4 for item in series for dose in item.doses):
            raise ValueError("Expected four well replicates per dose")
        return series


class WellMetric(ABC):
    label: str
    limits: tuple[float, float]

    @abstractmethod
    def value(self, well: WellEndpoint) -> float:
        """One definition of the displayed per-well quantity."""

    def draw(self, axis, series: AssaySeries, color: str) -> None:
        for index, dose in enumerate(series.doses):
            values = [self.value(well) for well in dose.wells]
            axis.errorbar(index, mean(values), yerr=stdev(values), color=color,
                          fmt="_", markersize=12, capsize=3, linewidth=1.3, zorder=2)
            positions = [index + offset for offset in (-0.16, -0.053, 0.053, 0.16)]
            axis.scatter(positions, values, s=22, color=color, edgecolor="white",
                         linewidth=0.5, zorder=3)
        axis.set(ylim=self.limits, xlim=(-0.5, len(series.doses) - 0.5), ylabel=self.label)
        axis.set_xticks(range(len(series.doses)), [f"{dose.concentration:g}" for dose in series.doses])
        axis.tick_params(labelsize=8, colors=INK)
        axis.yaxis.label.set(color=INK, fontsize=10)
        axis.spines[["top", "right"]].set_visible(False)
        axis.grid(axis="y", color="#e7ebef", linewidth=0.6)
        axis.set_axisbelow(True)


class MedianLog2Ratio(WellMetric):
    label = "Well median cell log₂(N/C GFP)"
    limits = (-0.5, 2.7)

    def value(self, well: WellEndpoint) -> float:
        return well.median_log2


class EligibilityFraction(WellMetric):
    label = "Eligible nuclei (fraction)"
    limits = (0.6, 1.0)

    def value(self, well: WellEndpoint) -> float:
        return well.eligibility


class Fresh23TranslocationFigure(FigureSheet):
    def __init__(self, series: tuple[AssaySeries, ...]):
        super().__init__("translocation_fresh23", "Task-only analysis recovers a dose response", 7.5)
        self.source(Path(__file__))
        self.source(SOURCE)
        self.text(3, 91, "BBBC013 · final self-repaired blind method · 96 paired DNA/GFP wells",
                  size=11, color=MUTED)
        for column, (assay, color) in enumerate(zip(series, (TEAL, BLUE))):
            left = 0.105 + column * 0.49
            self.panel(chr(65 + column), assay.compound, left * 100, 85)
            for metric, bottom, height in ((MedianLog2Ratio(), 0.48, 0.31),
                                           (EligibilityFraction(), 0.18, 0.21)):
                axis = self.figure.add_axes((left, bottom, 0.365, height))
                metric.draw(axis, assay, color)
                axis.set_xlabel(f"Concentration ({assay.unit})", fontsize=10, color=INK)
        self.text(3, 10, "Dots: four wells per dose. Horizontal marks and whiskers: mean ± between-well SD.", size=10)
        self.text(3, 6.5, "Dose positions are equally spaced; dots offset for visibility. Lower panels use the same wells.", size=10)
        self.text(3, 3, "Response is conditional on eligible compartments; not calibrated potency or mask accuracy.", size=10)


def main() -> None:
    Fresh23TranslocationFigure(AssaySeries.load(SOURCE)).save()


if __name__ == "__main__":
    main()
