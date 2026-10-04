"""Modest synthetic original/substitute native leaf observation for issue616.

One mode per process permits independent peak-RSS measurements. Never use real
images or a full retinal-sized array. This is not registered-callable acceptance.
"""

import argparse
import json
import resource
import time

import cv2
import numpy as np
from scipy import ndimage
from skimage import morphology


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("original", "opencv"))
    parser.add_argument("--radius", type=int, required=True)
    parser.add_argument("--height", type=int, default=96)
    parser.add_argument("--width", type=int, default=128)
    args = parser.parse_args()
    cv2.setNumThreads(1)
    image = np.random.default_rng(616).uniform(-2, 3, (args.height, args.width)).astype(np.float32)
    image[0, 0] = 7
    image[-1, -1] = -5
    footprint = morphology.disk(args.radius)
    baseline_kib = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    started = time.perf_counter()
    if args.mode == "original":
        opened = ndimage.maximum_filter(
            ndimage.minimum_filter(image, footprint=footprint), footprint=footprint,
        )
    else:
        opened = cv2.morphologyEx(
            image, cv2.MORPH_OPEN, footprint.astype(np.uint8),
            borderType=cv2.BORDER_REFLECT,
        )
    result = image - opened
    elapsed = time.perf_counter() - started
    peak_kib = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    # Original/native equivalence is computed only at the same modest size.
    if args.mode == "opencv":
        expected = image - ndimage.maximum_filter(
            ndimage.minimum_filter(image, footprint=footprint), footprint=footprint,
        )
        np.testing.assert_array_equal(result, expected)
    print(json.dumps({
        "mode": args.mode, "radius": args.radius, "shape": list(image.shape),
        "scipy": __import__("scipy").__version__, "opencv": cv2.__version__,
        "native_leaf_seconds": elapsed, "baseline_peak_kib": baseline_kib,
        "native_leaf_peak_kib": peak_kib,
        "offset_formula_bytes": min(args.height, footprint.shape[0]) * min(args.width, footprint.shape[1]) * int(footprint.sum()) * np.dtype(np.intp).itemsize,
        "finite": bool(np.isfinite(result).all()),
        "native_parity": args.mode == "opencv",
        "registered_callable_verified": False,
    }))


if __name__ == "__main__":
    main()
