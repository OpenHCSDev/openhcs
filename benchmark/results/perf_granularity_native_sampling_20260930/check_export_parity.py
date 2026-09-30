"""Check complete ordinary-run exports without weakening CP tolerances."""

import argparse
import csv
import json
import math
from pathlib import Path


def compare(control, candidate):
    differences = 0
    maximum = 0.0
    rows = 0
    with control.open(newline="") as left, candidate.open(newline="") as right:
        for number, (expected_row, actual_row) in enumerate(
            zip(csv.reader(left), csv.reader(right), strict=True)
        ):
            assert len(expected_row) == len(actual_row)
            for column, (expected, actual) in enumerate(
                zip(expected_row, actual_row, strict=True)
            ):
                if expected == actual:
                    continue
                assert number >= 1, (number, column, expected, actual)
                x, y = float(expected), float(actual)
                assert (math.isnan(x) and math.isnan(y)) or math.isclose(
                    x, y, rel_tol=1e-6, abs_tol=1e-6
                ), (number, column, x, y)
                differences += 1
                if math.isfinite(x) and math.isfinite(y):
                    maximum = max(maximum, abs(x - y))
            rows += 1
    return dict(
        csv_rows=rows,
        different_numeric_cells=differences,
        maximum_absolute_difference=maximum,
        all_non_numeric_cells_exact=True,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--control", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = compare(
        next(args.control.rglob("BF_cells_on_grid.csv")),
        next(args.candidate.rglob("BF_cells_on_grid.csv")),
    )
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
