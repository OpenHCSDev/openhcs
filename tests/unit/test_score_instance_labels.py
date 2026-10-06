"""Small, ID-invariant checks for the blind-task instance scorer."""

import numpy as np
import pytest

from benchmark.score_instance_labels import score_instances


def test_permuted_ids_are_exact() -> None:
    reference = np.array([[0, 1, 1], [2, 2, 0]])
    prediction = np.array([[0, 20, 20], [10, 10, 0]])
    score = score_instances(reference, prediction)
    assert score["partition_exact_up_to_label_ids"] is True
    assert score["foreground_xor_pixels"] == 0
    assert score["matches_at_iou_0_5"] == 2


def test_missing_object_and_extra_foreground() -> None:
    reference = np.array([[1, 1, 0], [0, 2, 0]])
    prediction = np.array([[7, 7, 3], [0, 0, 0]])
    score = score_instances(reference, prediction)
    assert score["matches_at_iou_0_5"] == 1
    assert score["false_negative_objects"] == 1
    assert score["false_positive_objects"] == 1
    assert score["foreground_xor_pixels"] == 2


@pytest.mark.parametrize("bad", [np.array([[1.5]]), np.array([[-1]]), np.array([[[1]]])])
def test_invalid_labels_are_rejected(bad: np.ndarray) -> None:
    with pytest.raises(ValueError):
        score_instances(np.array([[0]]), bad)
