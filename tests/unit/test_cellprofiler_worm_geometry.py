from __future__ import annotations

import numpy as np

from openhcs.processing.backends.cellprofiler.worm_geometry import (
    _cellprofiler_line_points,
    rebuild_worm_from_control_points_approx,
)


def test_fractional_control_points_match_canonical_centrosome_pixels() -> None:
    control_points = np.array(
        [
            [10.2, 10.2],
            [10.8, 10.8],
            [11.2, 13.2],
        ]
    )
    radii = np.array([2.0, 1.0, 2.0])
    expected_pixels = np.array(
        [
            [8, 10],
            [9, 9],
            [9, 10],
            [9, 11],
            [9, 12],
            [10, 8],
            [10, 9],
            [10, 10],
            [10, 11],
            [10, 12],
            [10, 13],
            [11, 9],
            [11, 10],
            [11, 11],
            [11, 12],
            [11, 13],
            [11, 14],
            [12, 10],
            [12, 12],
            [12, 13],
        ]
    )

    rows, columns = rebuild_worm_from_control_points_approx(
        control_points,
        radii,
        (24, 24),
    )

    actual_pixels = np.column_stack((rows, columns))
    row_major_order = np.lexsort((actual_pixels[:, 1], actual_pixels[:, 0]))
    np.testing.assert_array_equal(actual_pixels[row_major_order], expected_pixels)


def test_line_points_preserve_cellprofiler_truncation_and_ties() -> None:
    index, count, rows, columns = _cellprofiler_line_points(
        np.array([0.8, 3.9, -2.8]),
        np.array([0.8, 1.9, -2.8]),
        np.array([3.2, 0.1, -2.1]),
        np.array([1.2, 0.1, -2.1]),
    )

    np.testing.assert_array_equal(index, [0, 4, 8])
    np.testing.assert_array_equal(count, [4, 4, 1])
    np.testing.assert_array_equal(rows, [0, 1, 2, 3, 3, 2, 1, 0, -2])
    np.testing.assert_array_equal(columns, [0, 0, 1, 1, 1, 1, 0, 0, -2])
