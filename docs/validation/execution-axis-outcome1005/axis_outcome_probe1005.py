"""Synthetic execution failure probe; no scientific data or external effects."""

import numpy as np

from openhcs.core.memory import numpy


@numpy
def axis_outcome_probe1005(image, fail_above: float = 2.0):
    """Preserve pixels, or fail deterministically for the high-valued axis."""
    if float(np.mean(image)) > fail_above:
        raise RuntimeError("SYNTHETIC_AXIS_1005: high-valued axis rejected")
    return image.copy()
