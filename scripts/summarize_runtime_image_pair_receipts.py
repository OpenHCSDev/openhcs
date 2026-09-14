#!/usr/bin/env python3
"""Write decoded-pixel receipts for explicitly selected runtime image pairs."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path

import numpy as np

from openhcs.core.equivalence.comparison import _comparable_image_pixels
from openhcs.core.equivalence.images import RuntimeImageSnapshot

FIELDNAMES = (
    "comparison_name",
    "reference_path",
    "candidate_path",
    "reference_shape",
    "candidate_shape",
    "compared_shape",
    "reference_dtype",
    "candidate_dtype",
    "reference_pixel_digest",
    "candidate_pixel_digest",
    "raw_digest_equal",
    "abs_tolerance",
    "rel_tolerance",
    "compared_pixel_count",
    "out_of_tolerance_pixel_count",
    "max_abs_difference",
    "equivalent",
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--pair",
        action="append",
        nargs=3,
        required=True,
        metavar=("NAME", "REFERENCE", "CANDIDATE"),
    )
    parser.add_argument("--abs-tolerance", type=float, default=1e-6)
    parser.add_argument("--rel-tolerance", type=float, default=1e-6)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    rows = tuple(
        comparison_row(
            name,
            Path(reference_path),
            Path(candidate_path),
            abs_tolerance=args.abs_tolerance,
            rel_tolerance=args.rel_tolerance,
        )
        for name, reference_path, candidate_path in args.pair
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=FIELDNAMES)
        writer.writeheader()
        writer.writerows(rows)
    print(f"comparisons={len(rows)}")
    print(f"equivalent={sum(bool(row['equivalent']) for row in rows)}")
    print(f"output={args.output}")
    return 0


def comparison_row(
    name: str,
    reference_path: Path,
    candidate_path: Path,
    *,
    abs_tolerance: float,
    rel_tolerance: float,
) -> dict[str, object]:
    """Return one receipt using the runtime comparator's shape normalization."""

    reference = RuntimeImageSnapshot.from_image_file(reference_path)
    candidate = RuntimeImageSnapshot.from_image_file(candidate_path)
    comparable = _comparable_image_pixels(reference, candidate)
    if comparable is None:
        return {
            "comparison_name": name,
            "reference_path": str(reference_path.resolve()),
            "candidate_path": str(candidate_path.resolve()),
            "reference_shape": json.dumps(reference.shape),
            "candidate_shape": json.dumps(candidate.shape),
            "compared_shape": "",
            "reference_dtype": reference.dtype,
            "candidate_dtype": candidate.dtype,
            "reference_pixel_digest": reference.pixel_digest,
            "candidate_pixel_digest": candidate.pixel_digest,
            "raw_digest_equal": reference.pixel_digest == candidate.pixel_digest,
            "abs_tolerance": abs_tolerance,
            "rel_tolerance": rel_tolerance,
            "compared_pixel_count": 0,
            "out_of_tolerance_pixel_count": "",
            "max_abs_difference": "",
            "equivalent": False,
        }

    reference_pixels, candidate_pixels = comparable
    close_pixels = np.isclose(
        reference_pixels.astype(np.float64, copy=False),
        candidate_pixels.astype(np.float64, copy=False),
        rtol=rel_tolerance,
        atol=abs_tolerance,
        equal_nan=True,
    )
    out_of_tolerance = int(close_pixels.size - np.count_nonzero(close_pixels))
    absolute_differences = np.abs(
        reference_pixels.astype(np.float64, copy=False)
        - candidate_pixels.astype(np.float64, copy=False)
    )
    maximum_difference = (
        float(np.nanmax(absolute_differences)) if absolute_differences.size else 0.0
    )
    return {
        "comparison_name": name,
        "reference_path": str(reference_path.resolve()),
        "candidate_path": str(candidate_path.resolve()),
        "reference_shape": json.dumps(reference.shape),
        "candidate_shape": json.dumps(candidate.shape),
        "compared_shape": json.dumps(tuple(int(axis) for axis in close_pixels.shape)),
        "reference_dtype": reference.dtype,
        "candidate_dtype": candidate.dtype,
        "reference_pixel_digest": reference.pixel_digest,
        "candidate_pixel_digest": candidate.pixel_digest,
        "raw_digest_equal": reference.pixel_digest == candidate.pixel_digest,
        "abs_tolerance": abs_tolerance,
        "rel_tolerance": rel_tolerance,
        "compared_pixel_count": int(close_pixels.size),
        "out_of_tolerance_pixel_count": out_of_tolerance,
        "max_abs_difference": maximum_difference,
        "equivalent": out_of_tolerance == 0,
    }


if __name__ == "__main__":
    raise SystemExit(main())
