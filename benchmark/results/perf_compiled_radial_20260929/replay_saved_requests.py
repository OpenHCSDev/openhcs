"""Replay captured production radial requests through both public backends."""

import argparse
import hashlib
import json
from pathlib import Path
import pickle
import time
import numpy as np
from openhcs.processing.backends.cellprofiler.intensity_distribution import (
    NativeNumpyRadialDistributionBackendStrategy,
    NumbaNumpyRadialDistributionBackendStrategy,
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    native = NativeNumpyRadialDistributionBackendStrategy()
    compiled = NumbaNumpyRadialDistributionBackendStrategy()
    records = []
    for path in sorted(args.input_dir.glob("request_*.pkl")):
        request = pickle.loads(path.read_bytes())
        before = [
            hashlib.sha256(array.tobytes()).hexdigest() for array in request.arrays()
        ]
        start = time.perf_counter()
        expected = native.measure(request)
        native_seconds = time.perf_counter() - start
        start = time.perf_counter()
        actual = compiled.measure(request)
        compiled_seconds = time.perf_counter() - start
        errors = {}
        for name in ("fraction_at_distance", "mean_pixel_fraction", "radial_cv_by_bin"):
            a, b = getattr(expected, name), getattr(actual, name)
            finite = np.isfinite(a) & np.isfinite(b)
            np.testing.assert_allclose(b, a, rtol=1e-6, atol=1e-6, equal_nan=True)
            errors[name] = dict(
                maximum_absolute_difference=float(
                    np.abs(a[finite] - b[finite]).max(initial=0)
                ),
                failed_cells=0,
                cells=a.size,
            )
        np.testing.assert_array_equal(
            actual.object_has_pixels, expected.object_has_pixels
        )
        assert actual.n_bins == expected.n_bins
        assert before == [
            hashlib.sha256(array.tobytes()).hexdigest() for array in request.arrays()
        ]
        records.append(
            dict(
                source=path.name,
                shape=request.image.shape,
                dtype=str(request.image.dtype),
                native_seconds=native_seconds,
                numba_seconds=compiled_seconds,
                tolerances_pass=True,
                errors=errors,
            )
        )
    assert records, "No saved requests found."
    args.output.write_text(json.dumps(records, indent=2) + "\n")


if __name__ == "__main__":
    main()
