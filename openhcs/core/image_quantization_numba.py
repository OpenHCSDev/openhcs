"""Typed numerical kernels for the image serialization strategy family."""

import numpy as np
from numba import njit


@njit(cache=True)
def quantize_image_uint8(values, output, factor):
    """Retain input-precision scaling and nearest-even uint8 quantization."""
    scale = True
    for value in values:
        if np.isfinite(value) and (value < 0 or value > 1):
            scale = False
            break
    for index in range(values.size):
        value = values[index]
        if scale:
            value = value * factor
        if np.isnan(value) or value <= 0:
            output[index] = 0
        elif value >= 255:
            output[index] = 255
        else:
            output[index] = np.rint(value)
