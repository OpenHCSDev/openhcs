"""Importable functions used only by complete diagnostic pipeline fixtures."""

from __future__ import annotations

import numpy as np
from skimage.segmentation import expand_labels

from openhcs.core.memory import numpy
from openhcs.processing.backends.lib_registry.unified_registry import (
    ProcessingContract,
)


@numpy(contract=ProcessingContract.PURE_2D)
def expand_labels_without_overlap(
    label_image: np.ndarray,
    radius: int = 1,
) -> np.ndarray:
    """Expand labels by ``radius`` pixels without assigning overlap twice."""

    return expand_labels(label_image, distance=radius)
