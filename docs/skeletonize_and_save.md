## Skeletonize and Save

This file contains a complete, runnable OpenHCS-compatible Python function that performs per-slice skeletonization and exports labeled ROI masks for materialization.

```python
from openhcs.core.memory import numpy, pyclesperanto, cupy
from openhcs.core.pipeline.function_contracts import special_outputs, special_inputs
from openhcs.processing.materialization import (
    MaterializationSpec,
    CsvOptions,
    JsonOptions,
    ROIOptions,
    TiffStackOptions,
    TextOptions,
)
from dataclasses import dataclass
from typing import List, Tuple, Optional
import numpy as np

@numpy
@special_outputs(("skeleton_rois", MaterializationSpec(ROIOptions())))
def skeletonize_and_save(
    image,
    threshold: Optional[float] = None,
    min_component_size: int = 1
) -> Tuple[np.ndarray, List[np.ndarray]]:
    """Compute per-slice skeletonization and return labeled ROI masks.

    Parameters
    - image: 3D array (Z, Y, X) or (C, Y, X) where function treats first axis as slices.
    - threshold: optional global threshold; if None, Otsu is used per-slice.
    - min_component_size: remove skeleton components smaller than this size.

    Returns
    - (image, masks): original image and a list of labeled 2D arrays (one per slice).
    """
    from skimage.filters import threshold_otsu
    from skimage.morphology import skeletonize, remove_small_objects
    from skimage.measure import label

    masks: List[np.ndarray] = []

    for i, slice_2d in enumerate(image):
        slice_2d = np.asarray(slice_2d)

        if threshold is None:
            try:
                th = threshold_otsu(slice_2d)
            except Exception:
                th = float(np.mean(slice_2d))
        else:
            th = float(threshold)

        binary = slice_2d > th
        skel = skeletonize(binary)
        if min_component_size > 1:
            skel = remove_small_objects(skel.astype(bool), min_size=min_component_size)

        labeled = label(skel)
        masks.append(np.asarray(labeled, dtype=np.int32))

    return image, masks
```

Usage: the file provides the ready-to-materialize function for OpenHCS pipelines.
