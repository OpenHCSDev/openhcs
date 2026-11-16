from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
import numpy as np
from skimage.filters import gaussian

@numpy(contract=ProcessingContract.PURE_3D)
def selected_channel_gaussian_v1(image: np.ndarray, channel_index: int = 1,
                                sigma: float = 0.7) -> np.ndarray:
    """Smooth one pipeline-selected CYX plane in original intensity units.

    The pipeline must assemble CHANNEL on axis0. Nonselected planes retain
    exactly their original values in float64. Sigma is spatial source pixels;
    no channel mixing, normalization, clipping, or filesystem access occurs.
    Return a CYX float64 array, including empty spatial inputs, unchanged shape.
    """
    array = np.asarray(image)
    if array.ndim != 3:
        raise ValueError('Expected pipeline-assembled CYX image')
    if not 0 <= channel_index < array.shape[0]:
        raise ValueError('Selected channel is outside CYX stack')
    if not np.isfinite(sigma) or sigma < 0:
        raise ValueError('Sigma must be finite and nonnegative')
    result = array.astype(np.float64, copy=True)
    if result.size and sigma > 0:
        result[channel_index] = gaussian(array[channel_index], sigma=sigma,
                                        preserve_range=True, channel_axis=None,
                                        mode='nearest')
    return result
