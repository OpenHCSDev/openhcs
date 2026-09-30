"""Behavioral checks for CP vertex ordering and requested row positions."""

import numpy as np
import pytest

from openhcs.processing.backends.cellprofiler.label_geometry import (
    CellProfilerLabelHull,
    minimum_enclosing_circle_from_labels,
)


@pytest.mark.parametrize("shape", [(1, 1), (1, 9), (9, 1), (12, 17), (91, 103)])
@pytest.mark.parametrize("storage", ["contiguous", "strided", "readonly"])
def test_requested_hull_preserves_duplicate_missing_and_nonpositive_rows(
    shape, storage
):
    import centrosome.cpmorphology

    labels = np.random.default_rng(3009).choice([0, 2, 5], size=shape).astype(np.int32)
    if storage == "strided":
        backing = np.zeros((shape[0], 2 * shape[1]), dtype=np.int32)
        backing[:, ::2] = labels
        labels = backing[:, ::2]
    elif storage == "readonly":
        labels.setflags(write=False)
    original = labels.tobytes()
    requested = np.array([5, 2, 5, 0, -1, 17], dtype=np.int32)
    expected_labels = np.zeros(shape, dtype=np.int32)
    expected_labels[labels == 5] = 1
    expected_labels[labels == 2] = 2
    expected_hull, expected_counts = centrosome.cpmorphology.convex_hull(
        expected_labels, np.arange(1, 7, dtype=np.int32)
    )
    actual_hull, actual_counts = CellProfilerLabelHull.from_requested_positions(
        labels, requested
    ).vertices()
    np.testing.assert_array_equal(actual_hull, expected_hull)
    np.testing.assert_array_equal(actual_counts, expected_counts)
    np.testing.assert_array_equal(actual_counts[2:], np.zeros(4, dtype=np.int32))
    assert labels.tobytes() == original


@pytest.mark.parametrize("fill", [0, 11])
@pytest.mark.parametrize("shape", [(1, 1), (1, 9), (9, 1), (12, 17)])
def test_requested_circle_preserves_empty_and_constant_frontiers(fill, shape):
    labels = np.full(shape, fill, dtype=np.int32)
    requested = np.array([11, 31], dtype=np.int32)
    centers, radii = minimum_enclosing_circle_from_labels(labels, requested)
    if fill == 0:
        assert np.isnan(centers).all()
        np.testing.assert_array_equal(radii, [0.0, 0.0])
    else:
        expected_center = (np.asarray(shape) - 1) / 2
        np.testing.assert_array_equal(centers[0], expected_center)
        np.testing.assert_allclose(
            radii[0], np.linalg.norm(expected_center), rtol=1e-6, atol=1e-6
        )
        assert np.isnan(centers[1]).all()
        assert radii[1] == 0


def test_requested_hull_handles_sparse_large_ids_without_label_extent_allocation():
    labels = np.zeros((17, 23), dtype=np.int32)
    labels[1:8, 2:11] = 1_000_000_007
    labels[10:16, 15:22] = 71
    requested = np.array([71, 1_000_000_007, 17], dtype=np.int32)
    compact = np.zeros_like(labels)
    compact[labels == 71] = 1
    compact[labels == 1_000_000_007] = 2
    actual = CellProfilerLabelHull.from_requested_positions(
        labels, requested
    ).vertices()
    expected = CellProfilerLabelHull.from_labels(
        compact, np.arange(1, 4, dtype=np.int32)
    ).vertices()
    for left, right in zip(actual, expected, strict=True):
        np.testing.assert_array_equal(left, right)


def test_requested_hull_has_empty_output_for_empty_requested_domain():
    labels = np.ones((7, 9), dtype=np.int32)
    hull, counts = CellProfilerLabelHull.from_requested_positions(
        labels, np.empty(0, dtype=np.int32)
    ).vertices()
    assert hull.shape == (0, 3)
    assert counts.shape == (0,)
    assert hull.dtype == counts.dtype == np.int32
