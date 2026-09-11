"""Small image-processing extension used for the manuscript interface example."""

from openhcs.core.memory import numpy


@numpy
def paper_rescale_signal(image, gain: float = 1.2, offset: float = 0.0):
    """Rescale image intensities with a gain and offset.

    Args:
        image: Input image array supplied by the pipeline.
        gain: Multiplicative intensity scale.
        offset: Constant added after scaling.

    Returns:
        Image array with the same shape as the input.
    """
    return image * gain + offset
