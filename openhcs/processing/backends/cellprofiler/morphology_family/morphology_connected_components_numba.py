"""Exact same-value connected components from spatial row runs."""

import numpy as np
from numba import njit


@njit(cache=True)
def _find_root(parents, run):
    while parents[run] != run:
        parents[run] = parents[parents[run]]
        run = parents[run]
    return run


@njit(cache=True)
def _unite_runs(parents, left_run, right_run):
    root_a = _find_root(parents, left_run)
    root_b = _find_root(parents, right_run)
    if root_a < root_b:
        parents[root_b] = root_a
    elif root_b < root_a:
        parents[root_a] = root_b


@njit(cache=True)
def equal_value_components_numba(labels: np.ndarray) -> np.ndarray:
    """Label 26-connected equal values; x runs preserve scan-first numbering."""
    depth, height, width = labels.shape
    run_count = 0
    for z in range(depth):
        for y in range(height):
            previous_value = 0
            for x in range(width):
                value = labels[z, y, x]
                if value != 0 and value != previous_value:
                    run_count += 1
                previous_value = value
    run_start = np.empty(run_count, np.intp)
    run_stop = np.empty(run_count, np.intp)
    run_values = np.empty(run_count, labels.dtype)
    parents = np.arange(run_count, dtype=np.intp)
    row_runs = np.empty((depth, height, 2), np.intp)
    run_index = 0
    for z in range(depth):
        for y in range(height):
            row_runs[z, y, 0] = run_index
            x = 0
            while x < width:
                value = labels[z, y, x]
                begin_x = x
                x += 1
                while x < width and labels[z, y, x] == value:
                    x += 1
                if value == 0:
                    continue
                run_start[run_index] = begin_x
                run_stop[run_index] = x
                run_values[run_index] = value
                run_index += 1
            row_runs[z, y, 1] = run_index
            # The preceding y row and three preceding-z rows cover all 13
            # backward neighbors. Their run intervals retain value equality.
            for previous_row in range(4):
                previous_z = z
                previous_y = y - 1
                if previous_row > 0:
                    previous_z = z - 1
                    previous_y = y + previous_row - 2
                if previous_z < 0 or previous_y < 0 or previous_y >= height:
                    continue
                previous_start = row_runs[previous_z, previous_y, 0]
                previous_stop = row_runs[previous_z, previous_y, 1]
                for current_run in range(row_runs[z, y, 0], run_index):
                    # Intervals are exclusive-ended; x-adjacency allows touching ends.
                    while (
                        previous_start < previous_stop
                        and run_stop[previous_start] < run_start[current_run]
                    ):
                        previous_start += 1
                    previous_run = previous_start
                    while (
                        previous_run < previous_stop
                        and run_start[previous_run] <= run_stop[current_run]
                    ):
                        if run_values[previous_run] == run_values[current_run]:
                            _unite_runs(parents, previous_run, current_run)
                        previous_run += 1
    output = np.zeros(labels.shape, np.int32)
    root_labels = np.zeros(run_count, np.int32)
    next_label = 0
    for z in range(depth):
        for y in range(height):
            for run in range(row_runs[z, y, 0], row_runs[z, y, 1]):
                root = _find_root(parents, run)
                label_id = root_labels[root]
                if label_id == 0:
                    next_label += 1
                    label_id = next_label
                    root_labels[root] = label_id
                for x in range(run_start[run], run_stop[run]):
                    output[z, y, x] = label_id
    return output
