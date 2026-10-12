"""Low-level Numba Costes prefix/Pearson kernels."""

from __future__ import annotations

import numpy as np
from openhcs.processing.backends.cellprofiler.colocalization_costes_prefix_numba_pearson import (
    _correlation_slopes_numba,
    _cellprofiler_mean_variance_float32,
    _costes_manders_numba,
    _event_count_for_threshold_numba,
    _integer_unit_interval_codes_for_scale_numba,
    _linear_costes_numba,
    _linear_costes_sorted_events_numba,
    _max_from_prefix_numba,
    _max_pair_numba,
    _pearson_below_threshold_numba,
    _prefix_pearson_from_count_numba,
    _prefix_pearson_numba,
    _prefix_value_numba,
    _regression_line_numba,
)


class UnitIntervalDenseRankSemantics:
    """Shared dense-code/rank semantics for quantized CellProfiler intensities."""

    @classmethod
    def ranks(
        cls,
        values: np.ndarray,
        *,
        preferred_scale: int | None = None,
        proven_unit_interval_scale: int | None = None,
    ) -> np.ndarray:
        if proven_unit_interval_scale is not None:
            return cls.ranks_for_proven_unit_interval(
                values,
                int(proven_unit_interval_scale),
            )
        quantized_ranks = cls.ranks_for_integer_unit_interval(
            values,
            preferred_scale=preferred_scale,
        )
        if quantized_ranks is not None:
            return quantized_ranks
        return np.ascontiguousarray(
            np.unique(values, return_inverse=True)[1],
            dtype=np.int64,
        )

    @staticmethod
    def ranks_for_proven_unit_interval(
        values: np.ndarray,
        scale: int,
    ) -> np.ndarray:
        """Return dense ranks when metadata proves values are exact code / scale."""
        codes = np.rint(np.asarray(values) * int(scale)).astype(np.int64, copy=False)
        present = np.bincount(codes.ravel(), minlength=int(scale) + 1) > 0
        lookup = np.cumsum(present, dtype=np.int64) - 1
        return np.ascontiguousarray(lookup[codes], dtype=np.int64)

    @classmethod
    def ranks_for_integer_unit_interval(
        cls,
        values: np.ndarray,
        *,
        preferred_scale: int | None = None,
    ) -> np.ndarray | None:
        code_result = cls.integer_codes(values, preferred_scale=preferred_scale)
        if code_result is None:
            return None
        codes, scale = code_result
        return cls.dense_codes_and_values(codes, scale)[0]

    @staticmethod
    def integer_codes(
        values: np.ndarray,
        *,
        preferred_scale: int | None = None,
    ) -> tuple[np.ndarray, int] | None:
        values_array = np.asarray(values)
        if values_array.size == 0 or values_array.dtype.kind not in {"f", "u", "i"}:
            return None
        minimum = np.min(values_array)
        maximum = np.max(values_array)
        if not np.isfinite(minimum) or not np.isfinite(maximum):
            return None
        if minimum < 0.0 or maximum > 1.0:
            return None
        scales = (
            (preferred_scale, 65535, 255)
            if preferred_scale is not None
            else (65535, 255)
        )
        for scale in dict.fromkeys(int(candidate) for candidate in scales if candidate):
            valid, codes = _integer_unit_interval_codes_for_scale_numba(
                np.ascontiguousarray(values_array.ravel(), dtype=np.float64),
                scale,
            )
            if valid:
                return codes, scale
        return None

    @staticmethod
    def dense_codes_and_values(
        codes: np.ndarray,
        scale: int,
    ) -> tuple[np.ndarray, np.ndarray]:
        present = np.bincount(codes.ravel()) > 0
        lookup = np.cumsum(present, dtype=np.int64) - 1
        dense = np.ascontiguousarray(lookup[codes], dtype=np.int64)
        values = np.flatnonzero(present).astype(np.float32, copy=False)
        return dense, (values / np.float32(scale)).astype(np.float64, copy=False)
