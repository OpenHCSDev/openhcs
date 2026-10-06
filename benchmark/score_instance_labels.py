"""Score a frozen 2-D instance-label image without relying on label-ID order."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
import tifffile
from scipy.optimize import linear_sum_assignment


def _labels(array: np.ndarray, name: str) -> np.ndarray:
    if array.ndim != 2:
        raise ValueError(f"{name} must be a 2-D label image, got {array.shape}")
    if not np.issubdtype(array.dtype, np.number):
        raise ValueError(f"{name} must contain numeric labels")
    if not np.all(np.isfinite(array)) or np.any(array < 0):
        raise ValueError(f"{name} has non-finite or negative labels")
    if not np.all(array == np.floor(array)):
        raise ValueError(f"{name} has non-integer label values")
    return array.astype(np.int64, copy=False)


def score_instances(reference: np.ndarray, prediction: np.ndarray) -> dict[str, object]:
    """Match objects by maximum IoU; background is zero in both arrays."""
    reference = _labels(np.asarray(reference), "reference")
    prediction = _labels(np.asarray(prediction), "prediction")
    if reference.shape != prediction.shape:
        raise ValueError(f"shape mismatch: {reference.shape} vs {prediction.shape}")

    ref_ids, ref_inverse = np.unique(reference, return_inverse=True)
    pred_ids, pred_inverse = np.unique(prediction, return_inverse=True)
    ref_fg = np.flatnonzero(ref_ids != 0)
    pred_fg = np.flatnonzero(pred_ids != 0)
    n_ref, n_pred = len(ref_fg), len(pred_fg)
    if len(ref_ids) * len(pred_ids) > 10_000_000:
        raise ValueError("too many label pairs for the dense contingency score")

    overlap = np.bincount(
        ref_inverse.ravel() * len(pred_ids) + pred_inverse.ravel(),
        minlength=len(ref_ids) * len(pred_ids),
    ).reshape(len(ref_ids), len(pred_ids))
    ref_area = overlap.sum(axis=1)[ref_fg]
    pred_area = overlap.sum(axis=0)[pred_fg]
    intersection = overlap[np.ix_(ref_fg, pred_fg)]
    union = ref_area[:, None] + pred_area[None, :] - intersection
    iou = np.divide(
        intersection,
        union,
        out=np.zeros_like(intersection, dtype=float),
        where=union != 0,
    )
    rows, cols = linear_sum_assignment(-iou)
    accepted = iou[rows, cols] >= 0.5
    matched_rows, matched_cols = rows[accepted], cols[accepted]
    matched_iou = iou[matched_rows, matched_cols]
    ref_mask, pred_mask = reference != 0, prediction != 0
    foreground_xor = int(np.count_nonzero(ref_mask ^ pred_mask))
    foreground_union = int(np.count_nonzero(ref_mask | pred_mask))
    foreground_intersection = int(np.count_nonzero(ref_mask & pred_mask))
    true_positives = int(len(matched_rows))

    return {
        "shape": list(reference.shape),
        "reference_objects": n_ref,
        "predicted_objects": n_pred,
        "foreground_xor_pixels": foreground_xor,
        "foreground_iou": (
            foreground_intersection / foreground_union
            if foreground_union else 1.0
        ),
        "matches_at_iou_0_5": true_positives,
        "false_positive_objects": n_pred - true_positives,
        "false_negative_objects": n_ref - true_positives,
        "mean_matched_iou": float(np.mean(matched_iou)) if true_positives else 0.0,
        "mean_matched_area_error_pixels": (
            float(np.mean(np.abs(ref_area[matched_rows] - pred_area[matched_cols])))
            if true_positives else None
        ),
        "partition_exact_up_to_label_ids": bool(
            foreground_xor == 0
            and n_ref == n_pred == true_positives
            and np.all(matched_iou == 1.0)
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, required=True)
    parser.add_argument("--prediction", type=Path, required=True)
    args = parser.parse_args()
    result = score_instances(
        tifffile.imread(args.reference), tifffile.imread(args.prediction)
    )
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
