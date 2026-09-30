"""Physical quantile conventions and native workspace boundary regressions."""

from __future__ import annotations

import sys
from array import array

import numpy as np
import pytest

from openhcs.processing.backends.cellprofiler._intensity_native import grouped_quantiles
from openhcs.processing.backends.cellprofiler.intensity_object_quantiles_numba import (
    ObjectIntensityPixelGroups,
)


def cp_quantile(values, fraction):
    """Independent sorted reference for CP's count*fraction convention."""
    if not len(values):
        return 0.0
    ordered = np.sort(values)
    index = len(ordered) * fraction
    lower = int(index)
    if lower >= len(ordered) - 1:
        return ordered[-1]
    weight = index - lower
    return ordered[lower] * (1.0 - weight) + ordered[lower + 1] * weight


@pytest.mark.parametrize("size", [0, 1, 2, 3, 4, 5, 7, 16, 31, 129, 1024])
@pytest.mark.parametrize("fraction", [0.0, 0.25, 1.0 / 3.0, 0.5, 0.75, 1.0])
def test_group_quantiles_preserve_cp_ranks_and_retained_samples(size, fraction):
    rng = np.random.default_rng(39123 + size)
    samples = rng.integers(-4, 6, size).astype(np.float64)
    saved = samples.copy()
    groups = ObjectIntensityPixelGroups(
        samples, np.asarray([0, size], dtype=np.int64), (1,)
    )
    lower, median, upper, mad = groups.quantiles(fraction)
    expected_median = cp_quantile(saved, 0.5)
    np.testing.assert_array_equal(
        [lower[0], median[0], upper[0], mad[0]],
        [
            cp_quantile(saved, 0.25),
            expected_median,
            cp_quantile(saved, 0.75),
            cp_quantile(np.abs(saved - expected_median), fraction),
        ],
    )
    np.testing.assert_array_equal(samples, saved)


@pytest.mark.parametrize("dtype", [np.float32, np.float64])
def test_2d_groups_preserve_requested_order_and_filter_nonfinite(dtype):
    image = np.asarray([[1, 2, np.nan, 3, 4], [8, np.inf, 6, 7, 9]], dtype=dtype)
    labels = np.asarray([[7, 2, 7, 0, 2], [7, 9, 2, 7, 9]], dtype=np.int32)
    # Sparse/reordered IDs; label 9 is deliberately outside the measurement domain.
    lookup = np.full(10, -1, dtype=np.int64)
    lookup[7], lookup[2], lookup[5] = 0, 1, 2
    image, labels = image[:, ::-1], labels[:, ::-1]
    image.flags.writeable = labels.flags.writeable = False
    groups = ObjectIntensityPixelGroups.from_dense_2d(
        image, labels, lookup, np.asarray([3, 3, 0], dtype=np.int64)
    )
    np.testing.assert_array_equal(groups.offsets, [0, 3, 6, 6])
    outputs = groups.quantiles()
    for index, label in enumerate([7, 2, 5]):
        values = image[(labels == label) & np.isfinite(image)].astype(np.float64)
        median = cp_quantile(values, 0.5)
        np.testing.assert_array_equal(
            [column[index] for column in outputs],
            [
                cp_quantile(values, 0.25),
                median,
                cp_quantile(values, 0.75),
                cp_quantile(np.abs(values - median), 0.5),
            ],
        )


def test_dense_and_sparse_3d_groups_preserve_image_major_order_and_mad():
    rng = np.random.default_rng(44920)
    images = rng.standard_normal((3, 4, 5, 6)).astype(np.float32)
    labels = rng.choice([0, 2, 7], (4, 5, 6)).astype(np.int32)
    images[0, 0, 0, 0] = np.nan
    images[1, 1, 1, 1] = np.inf
    images = images[:, :, :, ::-1]
    labels = labels[:, :, ::-1]
    images.flags.writeable = labels.flags.writeable = False
    lookup = np.full(8, -1, dtype=np.int64)
    lookup[7], lookup[2] = 0, 1
    counts = np.asarray(
        [
            [
                np.count_nonzero((labels == label) & np.isfinite(image))
                for label in (7, 2, 5)
            ]
            for image in images
        ],
        dtype=np.int64,
    )
    dense = ObjectIntensityPixelGroups.from_dense_3d_batch(
        images, labels, lookup, counts
    )
    z, y, x = np.nonzero(labels)
    sparse = ObjectIntensityPixelGroups.from_sparse_3d_batch(
        images, z, y, x, lookup[labels[z, y, x]], counts
    )
    np.testing.assert_array_equal(dense.values, sparse.values)
    np.testing.assert_array_equal(dense.offsets, sparse.offsets)
    dense_outputs = dense.quantiles(1.0 / 3.0)
    sparse_outputs = sparse.quantiles(1.0 / 3.0)
    for left, right in zip(dense_outputs, sparse_outputs, strict=True):
        assert left.shape == (3, 3)
        np.testing.assert_array_equal(left, right)
    for image_index, image in enumerate(images):
        for object_index, label in enumerate((7, 2, 5)):
            values = image[(labels == label) & np.isfinite(image)].astype(np.float64)
            median = cp_quantile(values, 0.5)
            np.testing.assert_array_equal(
                [column[image_index, object_index] for column in dense_outputs],
                [
                    cp_quantile(values, 0.25),
                    median,
                    cp_quantile(values, 0.75),
                    cp_quantile(np.abs(values - median), 1.0 / 3.0),
                ],
            )


def native_arguments():
    return [
        np.asarray([1.0, 3.0, 2.0]),
        np.asarray([0, 3], dtype=np.int64),
        *(np.empty(1, dtype=np.float64) for _ in range(4)),
    ]


@pytest.mark.parametrize("offsets", [[], [1, 3], [0, 2], [0, 4, 3], [0, -1, 3]])
def test_native_rejects_malformed_offsets(offsets):
    arguments = native_arguments()
    arguments[1] = np.asarray(offsets, dtype=np.int64)
    for index in range(2, 6):
        arguments[index] = np.empty(max(0, len(offsets) - 1))
    with pytest.raises(ValueError):
        grouped_quantiles(*arguments, 0.5)


@pytest.mark.parametrize("fraction", [-0.1, 1.1, np.nan, np.inf])
def test_native_rejects_invalid_mad_fraction(fraction):
    with pytest.raises(ValueError, match="MAD fraction"):
        grouped_quantiles(*native_arguments(), fraction)


@pytest.mark.parametrize("index", range(6))
def test_native_rejects_wrong_element_types_and_releases_all_leases(index):
    arguments = [array("d", [1, 3, 2]), array("q", [0, 3])]
    arguments.extend(array("d", [0]) for _ in range(4))
    arguments[index] = array("i", (int(value) for value in arguments[index]))
    references = [sys.getrefcount(array) for array in arguments]
    with pytest.raises(ValueError):
        grouped_quantiles(*arguments, 0.5)
    assert references == [sys.getrefcount(array) for array in arguments]
    for buffer in arguments:
        buffer.append(0)


@pytest.mark.parametrize("index", [0, 2, 3, 4, 5])
def test_native_rejects_readonly_workspaces_and_outputs(index):
    arguments = native_arguments()
    arguments[index].flags.writeable = False
    with pytest.raises(ValueError):
        grouped_quantiles(*arguments, 0.5)


def test_native_rejects_overlap_shape_capacity_and_alignment():
    for index in range(2, 6):
        arguments = native_arguments()
        arguments[index] = arguments[0][:1]
        with pytest.raises(ValueError, match="overlap"):
            grouped_quantiles(*arguments, 0.5)
    arguments = native_arguments()
    arguments[2] = np.empty(2)
    with pytest.raises(ValueError, match="output sizes"):
        grouped_quantiles(*arguments, 0.5)
    arguments = native_arguments()
    arguments[0] = arguments[0].reshape(1, 3)
    with pytest.raises(ValueError, match="1-D"):
        grouped_quantiles(*arguments, 0.5)
    arguments = native_arguments()
    arguments[0] = np.ndarray((3,), dtype=np.float64, buffer=bytearray(25), offset=1)
    with pytest.raises(ValueError):
        grouped_quantiles(*arguments, 0.5)


def test_native_accepts_empty_domains_and_readonly_offsets():
    offsets = np.asarray([0], dtype=np.int64)
    offsets.flags.writeable = False
    assert (
        grouped_quantiles(np.empty(0), offsets, *(np.empty(0) for _ in range(4)), 0.5)
        is None
    )
    groups = ObjectIntensityPixelGroups(
        np.empty(0), np.asarray([0, 0, 0], dtype=np.int64), (2,)
    )
    for column in groups.quantiles():
        np.testing.assert_array_equal(column, np.zeros(2))
