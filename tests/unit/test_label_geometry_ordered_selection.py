"""Frozen legacy permutations and coordinates constrain selective partitioning."""

import numpy as np
import pytest
from numba.core.dispatcher import Dispatcher

from openhcs.processing.backends.cellprofiler.label_geometry import (
    _numpy124_aquicksort_indices,
    _numpy124_partition_indices_numba,
)
from openhcs.processing.backends.cellprofiler.shape import (
    NumbaNumpyShapeMeasurementBackendStrategy,
)


LEGACY_ORDERS = (
    (
        np.zeros(24),
        [0, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6,
         5, 4, 3, 2, 1, 22, 23],
    ),
    (
        np.tile(np.array([1.0, 2.0, 0.0]), 12),
        [17, 32, 29, 26, 23, 20, 14, 11, 35, 2, 8, 5, 9, 33, 30, 27, 3,
         24, 21, 0, 18, 15, 6, 12, 34, 16, 4, 25, 13, 28, 7, 31, 1, 10,
         19, 22],
    ),
    (
        np.array([np.nan, 2.0, -np.inf, 4.0, np.nan, np.inf, 0.0, -0.0,
                  3.0, 3.0, 1.0, 2.0, 0.0, 3.0, np.nan, 0.0, 5.0, 5.0,
                  0.0, 2.0]),
        [0, 2, 15, 14, 12, 6, 7, 18, 10, 11, 19, 5, 4, 1, 13, 8, 9, 3,
         16, 17],
    ),
)


@pytest.mark.parametrize("values,expected", LEGACY_ORDERS)
def test_full_order_retains_frozen_numpy124_permutation(values, expected):
    np.testing.assert_array_equal(_numpy124_aquicksort_indices(values), expected)


@pytest.mark.parametrize("values,expected", LEGACY_ORDERS)
@pytest.mark.parametrize("selection", ("empty", "all", "sparse", "alternating"))
def test_selected_positions_keep_their_exact_legacy_relative_order(
    values, expected, selection
):
    retained = np.zeros(values.size, dtype=bool)
    if selection == "all":
        retained[:] = True
    elif selection == "sparse":
        retained[[0, values.size // 2, values.size - 1]] = True
    elif selection == "alternating":
        retained[::2] = True
    order = _numpy124_partition_indices_numba(values, retained)
    expected_order = np.asarray(expected, dtype=np.int64)
    np.testing.assert_array_equal(
        order[retained[order]], expected_order[retained[expected_order]]
    )


@pytest.mark.parametrize(
    "nonfinite,masked,expected",
    (
        (False, False, ([[4, 0], [1, 1], [1, 1]], [[8, 9], [0, 0], [0, 0]])),
        (False, True, ([[1, 3], [0, 0], [0, 0]], [[2, 9], [6, 6], [6, 6]])),
        (True, False, ([[2, 4], [1, 1], [1, 1]], [[1, 3], [6, 6], [6, 6]])),
        (True, True, ([[2, 1], [1, 1], [1, 1]], [[2, 3], [6, 6], [6, 6]])),
    ),
)
def test_shape_backend_preserves_mask_nan_and_absent_label_coordinates(
    nonfinite, masked, expected
):
    image = np.tile(np.array([0.0, 1.0, 2.0, 2.0, 0.0, -1.0]), 12).reshape(6, 12)
    labels = np.tile(np.array([0, 1, 1, 2, 2, -1], np.int32), 12).reshape(6, 12)
    requested = np.array([[1, 2], [0, -1], [3, 4]], dtype=np.int32)
    if nonfinite:
        image.flat[9] = np.nan
        image.flat[25] = np.inf
        image.flat[37] = -np.inf
    mask = (np.arange(72).reshape(6, 12) % 4) != 0 if masked else None
    actual = NumbaNumpyShapeMeasurementBackendStrategy().maximum_position_of_labels(
        image, labels, requested, mask=mask
    )
    for actual_axis, expected_axis in zip(actual, expected, strict=True):
        np.testing.assert_array_equal(actual_axis, expected_axis)


def test_backend_preparation_covers_full_and_selected_array_abis(monkeypatch):
    backend = NumbaNumpyShapeMeasurementBackendStrategy()
    backend.prepare_backend()
    original = Dispatcher.compile

    def reject_unprepared_signature(dispatcher, signature):
        assert signature in dispatcher.signatures, (
            dispatcher.py_func.__qualname__, signature, dispatcher.signatures
        )
        return original(dispatcher, signature)

    monkeypatch.setattr(Dispatcher, "compile", reject_unprepared_signature)
    labels = np.array([[0, 1, 1], [0, 1, 0], [2, 2, 0]], dtype=np.int32)
    mask = labels != 0
    for dtype in (np.float32, np.float64):
        image = np.arange(9, dtype=dtype).reshape(3, 3)
        _numpy124_aquicksort_indices(image.ravel())
        for immutable in (False, True):
            requested = np.array([1, 2], dtype=np.int32)
            requested.setflags(write=not immutable)
            for selected_mask in (None, mask):
                actual = backend.maximum_position_of_labels(
                    image, labels, requested, mask=selected_mask
                )
                np.testing.assert_array_equal(actual[0], [1.0, 2.0])
                np.testing.assert_array_equal(actual[1], [1.0, 1.0])
