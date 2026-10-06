"""Matching behaviour of the blinded 3-D centre scorer."""

import numpy as np
import pytest

from benchmark.score_point_centres import score_points


def test_one_to_one_matching_and_count_error() -> None:
    reference = np.array([[0, 0, 0], [0, 20, 0]])
    prediction = np.array([[0, 2, 0], [0, 19, 0], [0, 100, 0]])
    score = score_points(reference, prediction, 5)
    assert (score["true_positives"], score["false_positives"], score["false_negatives"]) == (2, 1, 0)
    assert score["signed_count_error"] == 1
    assert score["mean_localisation_error_voxels"] == 1.5


def test_duplicate_prediction_is_not_a_second_match() -> None:
    score = score_points(np.array([[0, 0, 0]]), np.array([[0, 1, 0], [0, 2, 0]]), 3)
    assert score["true_positives"] == 1
    assert score["false_positives"] == 1
    assert score["ambiguous_reference_points"] == 1


def test_empty_tables() -> None:
    score = score_points(np.empty((0, 3)), np.empty((0, 3)), 30)
    assert score["f1"] == 1.0
    assert score["true_positives"] == 0


@pytest.mark.parametrize("threshold", [0, -1, float("nan")])
def test_invalid_threshold(threshold: float) -> None:
    with pytest.raises(ValueError):
        score_points(np.empty((0, 3)), np.empty((0, 3)), threshold)
