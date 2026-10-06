"""One-to-one voxel-coordinate score for a frozen 3-D point detection result."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path

import numpy as np
from scipy.optimize import linear_sum_assignment
from scipy.spatial.distance import cdist


def _points(points: np.ndarray, name: str) -> np.ndarray:
    points = np.asarray(points, dtype=float)
    if points.size == 0:
        return points.reshape(0, 3)
    if points.ndim != 2 or points.shape[1] != 3 or not np.all(np.isfinite(points)):
        raise ValueError(f"{name} must be a finite N × 3 coordinate table")
    return points


def score_points(
    reference: np.ndarray, prediction: np.ndarray, threshold_voxels: float
) -> dict[str, object]:
    """Maximise admissible matches, then minimise their Euclidean distances."""
    reference = _points(reference, "reference")
    prediction = _points(prediction, "prediction")
    if not np.isfinite(threshold_voxels) or threshold_voxels <= 0:
        raise ValueError("threshold_voxels must be finite and positive")
    n_ref, n_pred = len(reference), len(prediction)
    distances = cdist(reference, prediction)
    penalty = threshold_voxels + 1
    costs = np.zeros((n_ref + n_pred, n_ref + n_pred), dtype=float)
    costs[:n_ref, :n_pred] = np.where(
        distances <= threshold_voxels, distances, 3 * penalty
    )
    costs[:n_ref, n_pred:] = penalty
    costs[n_ref:, :n_pred] = penalty
    rows, cols = linear_sum_assignment(costs)
    is_pair = (rows < n_ref) & (cols < n_pred)
    paired_rows, paired_cols = rows[is_pair], cols[is_pair]
    admissible = distances[paired_rows, paired_cols] <= threshold_voxels
    matched_distances = distances[paired_rows[admissible], paired_cols[admissible]]
    tp = int(len(matched_distances))
    precision = tp / n_pred if n_pred else (1.0 if n_ref == 0 else 0.0)
    recall = tp / n_ref if n_ref else 1.0
    f1 = 2 * precision * recall / (precision + recall) if precision + recall else 0.0
    return {
        "coordinate_order": "z,y,x",
        "distance_unit": "unscaled_voxels",
        "threshold_voxels": threshold_voxels,
        "reference_points": n_ref,
        "predicted_points": n_pred,
        "true_positives": tp,
        "false_positives": n_pred - tp,
        "false_negatives": n_ref - tp,
        "signed_count_error": n_pred - n_ref,
        "precision": precision,
        "recall": recall,
        "f1": f1,
        "mean_localisation_error_voxels": (
            float(np.mean(matched_distances)) if tp else None
        ),
        "max_localisation_error_voxels": (
            float(np.max(matched_distances)) if tp else None
        ),
        "ambiguous_reference_points": int(np.count_nonzero((distances <= threshold_voxels).sum(axis=1) > 1)),
        "ambiguous_prediction_points": int(np.count_nonzero((distances <= threshold_voxels).sum(axis=0) > 1)),
    }


def read_csv_points(path: Path, columns: tuple[str, str, str]) -> np.ndarray:
    with path.open(newline="") as source:
        reader = csv.DictReader(source)
        if reader.fieldnames is None or not set(columns) <= set(reader.fieldnames):
            raise ValueError(f"{path} requires columns {columns}")
        rows = [[float(row[column]) for column in columns] for row in reader]
    return _points(np.asarray(rows, dtype=float), str(path))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, required=True)
    parser.add_argument("--prediction", type=Path, required=True)
    parser.add_argument("--threshold-voxels", type=float, default=30.0)
    args = parser.parse_args()
    reference = read_csv_points(args.reference, ("axis-0", "axis-1", "axis-2"))
    prediction = read_csv_points(args.prediction, ("z", "y", "x"))
    print(json.dumps(score_points(reference, prediction, args.threshold_voxels), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
