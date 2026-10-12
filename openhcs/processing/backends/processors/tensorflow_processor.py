"""TensorFlow processor registrations.

Shared operations are written once in ``image_stack_operations``; this module
registers them for TensorFlow and holds the TensorFlow-specific algorithms.
"""

from __future__ import annotations

from typing import List, Optional, Tuple

from arraybridge import MemoryType

from openhcs.core.artifacts.specs import ArtifactSpec
from openhcs.core.artifacts.kinds import ImageArtifactType
from openhcs.utils.import_utils import optional_import_placeholder
from openhcs.core.memory import tensorflow as tensorflow_func
from openhcs.core.pipeline.function_contracts import artifact_inputs
from openhcs.processing.backends.processors import image_stack_operations as operations
from openhcs.processing.backends.processors.method_axes import (
    StackProjectionMethod,
)

tf = optional_import_placeholder("tensorflow")

OPERATIONS = MemoryType.TENSORFLOW.library


@tensorflow_func
def create_linear_weight_mask(
    height: int, width: int, margin_ratio: float = 0.1
) -> "tf.Tensor":
    """
    Create a 2D weight mask that linearly ramps from 0 at the edges to 1 in the center.

    Args:
        height: Height of the mask
        width: Width of the mask
        margin_ratio: Ratio of the margin to the image size

    Returns:
        2D TensorFlow weight mask of shape (height, width)
    """
    return operations.linear_weight_mask(
        OPERATIONS, height, width, margin_ratio, ramp_endpoint=True
    )


def _gaussian_blur(image: "tf.Tensor", sigma: float) -> "tf.Tensor":
    """
    Apply Gaussian blur to a 2D image.

    Args:
        image: 2D TensorFlow tensor of shape (H, W)
        sigma: Standard deviation of the Gaussian kernel

    Returns:
        Blurred 2D TensorFlow tensor of shape (H, W)
    """
    # Calculate kernel size based on sigma
    kernel_size = max(3, int(2 * 4 * sigma + 1))
    if kernel_size % 2 == 0:
        kernel_size += 1  # Ensure odd kernel size

    # Add batch and channel dimensions for tf.image.gaussian_blur
    img = tf.expand_dims(tf.expand_dims(image, 0), -1)

    # Apply Gaussian blur
    blurred = tf.image.gaussian_blur(img, [kernel_size, kernel_size], sigma, "REFLECT")

    # Remove batch and channel dimensions
    return tf.squeeze(blurred)


@tensorflow_func
def sharpen(
    image: "tf.Tensor", radius: float = 1.0, amount: float = 1.0
) -> "tf.Tensor":
    """
    Sharpen a 3D image using unsharp masking.

    This applies sharpening to each Z-slice independently.

    Args:
        image: 3D TensorFlow tensor of shape (Z, Y, X)
        radius: Radius of Gaussian blur
        amount: Sharpening strength

    Returns:
        Sharpened 3D TensorFlow tensor of shape (Z, Y, X)
    """
    operations.require_stack(OPERATIONS, image)

    # Store original dtype
    dtype = image.dtype

    # Process each Z-slice independently
    result_list = []

    for z in range(image.shape[0]):
        # Convert to float for processing
        slice_float = tf.cast(image[z], tf.float32) / tf.reduce_max(image[z])

        # Create blurred version for unsharp mask
        blurred = _gaussian_blur(slice_float, sigma=radius)

        # Apply unsharp mask: original + amount * (original - blurred)
        sharpened = slice_float + amount * (slice_float - blurred)

        # Clip to valid range
        sharpened = tf.clip_by_value(sharpened, 0.0, 1.0)

        # Scale back to original range
        min_val = tf.reduce_min(sharpened)
        max_val = tf.reduce_max(sharpened)
        if max_val > min_val:
            sharpened = (sharpened - min_val) * 65535.0 / (max_val - min_val)

        result_list.append(sharpened)

    # Stack results back into a 3D tensor
    result = tf.stack(result_list, axis=0)

    # Convert back to original dtype
    if dtype == tf.uint16:
        result = tf.cast(tf.clip_by_value(result, 0, 65535), tf.uint16)
    else:
        result = tf.cast(result, dtype)

    return result


@tensorflow_func
def percentile_normalize(
    image: "tf.Tensor",
    low_percentile: float = 1.0,
    high_percentile: float = 99.0,
    target_min: float = 0.0,
    target_max: float = 65535.0,
) -> "tf.Tensor":
    """
    Normalize a 3D image using percentile-based contrast stretching.

    This applies normalization to each Z-slice independently.

    Args:
        image: 3D TensorFlow tensor of shape (Z, Y, X)
        low_percentile: Lower percentile (0-100)
        high_percentile: Upper percentile (0-100)
        target_min: Target minimum value
        target_max: Target maximum value

    Returns:
        Normalized 3D TensorFlow tensor of shape (Z, Y, X)
    """
    operations.require_stack(OPERATIONS, image)

    # Process each Z-slice independently
    result_list = []

    for z in range(image.shape[0]):
        # Get percentile values for this slice
        # TensorFlow doesn't have a direct percentile function, so we use a workaround
        flat_slice = tf.reshape(image[z], [-1])
        sorted_slice = tf.sort(flat_slice)

        # Calculate indices for percentiles
        slice_size = tf.cast(tf.size(flat_slice), tf.float32)
        low_idx = tf.cast(tf.math.floor(slice_size * low_percentile / 100.0), tf.int32)
        high_idx = tf.cast(
            tf.math.floor(slice_size * high_percentile / 100.0), tf.int32
        )

        # Get percentile values
        p_low = sorted_slice[low_idx]
        p_high = sorted_slice[high_idx]

        # Avoid division by zero
        if p_high == p_low:
            result_list.append(tf.ones_like(image[z], dtype=tf.float32) * target_min)
            continue

        # Clip and normalize to target range
        clipped = tf.clip_by_value(tf.cast(image[z], tf.float32), p_low, p_high)
        scale = (target_max - target_min) / (p_high - p_low)
        normalized = (clipped - p_low) * scale + target_min
        result_list.append(normalized)

    # Stack results back into a 3D tensor
    result = tf.stack(result_list, axis=0)

    # Convert to uint16
    result = tf.cast(tf.clip_by_value(result, 0, 65535), tf.uint16)

    return result


@tensorflow_func
def stack_percentile_normalize(
    stack: "tf.Tensor",
    low_percentile: float = 1.0,
    high_percentile: float = 99.0,
    target_min: float = 0.0,
    target_max: float = 65535.0,
) -> "tf.Tensor":
    """
    Normalize a stack using global percentile-based contrast stretching.

    This ensures consistent normalization across all Z-slices by computing
    global percentiles across the entire stack.

    Args:
        stack: 3D TensorFlow tensor of shape (Z, Y, X)
        low_percentile: Lower percentile (0-100)
        high_percentile: Upper percentile (0-100)
        target_min: Target minimum value
        target_max: Target maximum value

    Returns:
        Normalized 3D TensorFlow tensor of shape (Z, Y, X)
    """
    operations.require_stack(OPERATIONS, stack)

    # Calculate global percentiles across the entire stack using TensorFlow Probability
    # This is memory-efficient and doesn't require sorting the entire array
    try:
        import tensorflow_probability as tfp

        p_low = tf.cast(tfp.stats.percentile(stack, low_percentile), tf.float32)
        p_high = tf.cast(tfp.stats.percentile(stack, high_percentile), tf.float32)
    except ImportError:
        # Fallback to manual calculation if TensorFlow Probability is not available
        # This is less memory-efficient but works
        flat_stack = tf.reshape(stack, [-1])
        sorted_stack = tf.sort(flat_stack)

        # Calculate indices for percentiles
        stack_size = tf.cast(tf.size(flat_stack), tf.float32)
        low_idx = tf.cast(tf.math.floor(stack_size * low_percentile / 100.0), tf.int32)
        high_idx = tf.cast(
            tf.math.floor(stack_size * high_percentile / 100.0), tf.int32
        )

        # Get percentile values and cast to float32 for consistency
        p_low = tf.cast(sorted_stack[low_idx], tf.float32)
        p_high = tf.cast(sorted_stack[high_idx], tf.float32)

    # Avoid division by zero
    if p_high == p_low:
        return tf.ones_like(stack) * target_min

    # Clip and normalize to target range (match NumPy implementation exactly)
    clipped = tf.clip_by_value(stack, p_low, p_high)
    normalized = (clipped - p_low) * (target_max - target_min) / (
        p_high - p_low
    ) + target_min
    normalized = tf.cast(normalized, tf.uint16)

    return normalized


@tensorflow_func
def create_composite(
    images: List["tf.Tensor"], weights: Optional[List[float]] = None
) -> "tf.Tensor":
    """
    Create a composite image from multiple 3D arrays.

    Args:
        images: List of 3D TensorFlow tensors, each of shape (Z, Y, X)
        weights: List of weights for each image. If None, equal weights are used.

    Returns:
        Composite 3D TensorFlow tensor of shape (Z, Y, X)
    """
    # Ensure images is a list
    if not isinstance(images, list):
        raise TypeError("images must be a list of TensorFlow tensors")

    # Check for empty list early
    if not images:
        raise ValueError("images list cannot be empty")

    # Validate all images are 3D TensorFlow tensors with the same shape
    for i, img in enumerate(images):
        operations.require_stack(OPERATIONS, img, f"images[{i}]")
        if img.shape != images[0].shape:
            raise ValueError(
                f"All images must have the same shape. "
                f"images[0] has shape {images[0].shape}, "
                f"images[{i}] has shape {img.shape}"
            )

    # Default weights if none provided
    if weights is None:
        # Equal weights for all images
        weights = [1.0 / len(images)] * len(images)
    elif not isinstance(weights, list):
        raise TypeError("weights must be a list of values")

    # Make sure weights list is at least as long as images list
    if len(weights) < len(images):
        weights = weights + [0.0] * (len(images) - len(weights))
    # Truncate weights if longer than images
    weights = weights[: len(images)]

    first_image = images[0]
    shape = first_image.shape
    dtype = first_image.dtype

    # Create empty composite
    composite = tf.zeros(shape, dtype=tf.float32)
    total_weight = 0.0

    # Add each image with its weight
    for i, image in enumerate(images):
        weight = weights[i]
        if weight <= 0.0:
            continue

        # Add to composite
        composite += tf.cast(image, tf.float32) * weight
        total_weight += weight

    # Normalize by total weight
    if total_weight > 0:
        composite /= total_weight

    # Convert back to original dtype (usually uint16)
    if OPERATIONS.dtype_name(dtype) in operations.CLAMPED_INTEGER_DTYPES:
        composite = tf.cast(tf.clip_by_value(composite, 0, dtype.max), dtype)
    else:
        composite = tf.cast(composite, dtype)

    return composite


@artifact_inputs(ArtifactSpec.input("mask", ImageArtifactType, parameter_name="mask"))
@tensorflow_func
def apply_mask(image: "tf.Tensor", mask: "tf.Tensor") -> "tf.Tensor":
    """
    Apply a mask to a 3D image.

    This applies the mask to each Z-slice independently if mask is 2D,
    or applies the 3D mask directly if mask is 3D.

    Args:
        image: 3D TensorFlow tensor of shape (Z, Y, X)
        mask: 3D TensorFlow tensor of shape (Z, Y, X) or 2D TensorFlow tensor of shape (Y, X)

    Returns:
        Masked 3D TensorFlow tensor of shape (Z, Y, X)
    """
    return operations.apply_mask(OPERATIONS, image, mask)


@tensorflow_func
def create_weight_mask(
    shape: Tuple[int, int], margin_ratio: float = 0.1
) -> "tf.Tensor":
    """
    Create a weight mask for blending images.

    Args:
        shape: Shape of the mask (height, width)
        margin_ratio: Ratio of image size to use as margin

    Returns:
        2D TensorFlow weight mask of shape (Y, X)
    """
    return create_linear_weight_mask(*operations.weight_mask_extent(shape), margin_ratio)


@tensorflow_func
def max_projection(stack: "tf.Tensor") -> "tf.Tensor":
    """
    Create a maximum intensity projection from a Z-stack.

    Args:
        stack: 3D TensorFlow tensor of shape (Z, Y, X)

    Returns:
        3D TensorFlow tensor of shape (1, Y, X)
    """
    return operations.max_projection(OPERATIONS, stack)


@tensorflow_func
def mean_projection(stack: "tf.Tensor") -> "tf.Tensor":
    """
    Create a mean intensity projection from a Z-stack.

    Args:
        stack: 3D TensorFlow tensor of shape (Z, Y, X)

    Returns:
        3D TensorFlow tensor of shape (1, Y, X)
    """
    return operations.mean_projection(OPERATIONS, stack)


@tensorflow_func
def stack_equalize_histogram(
    stack: "tf.Tensor",
    bins: int = 65536,
    range_min: float = 0.0,
    range_max: float = 65535.0,
) -> "tf.Tensor":
    """
    Apply histogram equalization to an entire stack.

    This ensures consistent contrast enhancement across all Z-slices by
    computing a global histogram across the entire stack.

    Args:
        stack: 3D TensorFlow tensor of shape (Z, Y, X)
        bins: Number of bins for histogram computation
        range_min: Minimum value for histogram range
        range_max: Maximum value for histogram range

    Returns:
        Equalized 3D TensorFlow tensor of shape (Z, Y, X)
    """
    operations.require_stack(OPERATIONS, stack)

    # Remember input dtype to preserve it
    input_dtype = stack.dtype

    # TensorFlow doesn't have a direct histogram equalization function
    # We'll implement it manually

    # Flatten the entire stack to compute the global histogram
    flat_stack = tf.reshape(tf.cast(stack, tf.float32), [-1])

    # Calculate the histogram
    # TensorFlow doesn't have a direct equivalent to numpy's histogram
    # We'll use tf.histogram_fixed_width
    hist = tf.histogram_fixed_width(flat_stack, [range_min, range_max], nbins=bins)

    # Calculate cumulative distribution function (CDF)
    cdf = tf.cumsum(hist)

    # Normalize the CDF to the input dtype range
    # Avoid division by zero
    if tf.reduce_max(cdf) > 0:
        if OPERATIONS.dtype_name(input_dtype) in operations.CLAMPED_INTEGER_DTYPES:
            cdf = float(input_dtype.max) * cdf / tf.cast(cdf[-1], tf.float32)
        else:
            # For float dtypes, normalize to [0, 1]
            cdf = cdf / tf.cast(cdf[-1], tf.float32)

    # We don't need bin width for the lookup table approach

    # Scale input values to bin indices
    indices = tf.cast(
        tf.clip_by_value(
            tf.math.floor((flat_stack - range_min) / (range_max - range_min) * bins),
            0,
            bins - 1,
        ),
        tf.int32,
    )

    # Look up CDF values
    equalized_flat = tf.gather(cdf, indices)

    # Reshape back to original shape
    equalized_stack = tf.reshape(equalized_flat, stack.shape)

    # Convert back to input dtype
    return tf.cast(equalized_stack, input_dtype)


@tensorflow_func
def create_projection(
    stack: "tf.Tensor",
    method: StackProjectionMethod = StackProjectionMethod.MAX,
) -> "tf.Tensor":
    """
    Create a projection from a stack using the specified method.

    Args:
        stack: 3D TensorFlow tensor of shape (Z, Y, X)
        method: Projection method served by ``image_stack_operations.StackProjection``

    Returns:
        3D TensorFlow tensor of shape (1, Y, X)
    """
    return operations.create_projection(OPERATIONS, stack, method)


@tensorflow_func
def tophat(
    image: "tf.Tensor", selem_radius: int = 50, downsample_factor: int = 4
) -> "tf.Tensor":
    """
    Apply white top-hat filter to a 3D image for background removal.

    This applies the filter to each Z-slice independently using TensorFlow's
    native operations.

    Args:
        image: 3D TensorFlow tensor of shape (Z, Y, X)
        selem_radius: Radius of the structuring element disk
        downsample_factor: Factor by which to downsample the image for processing

    Returns:
        Filtered 3D TensorFlow tensor of shape (Z, Y, X)
    """
    operations.require_stack(OPERATIONS, image)

    # Process each Z-slice independently
    result_list = []

    for z in range(image.shape[0]):
        # Store original data type
        input_dtype = image[z].dtype

        # 1) Downsample using TensorFlow's resize function
        # First, add batch and channel dimensions for resize
        img_4d = tf.expand_dims(tf.expand_dims(tf.cast(image[z], tf.float32), 0), -1)

        # Calculate new dimensions
        new_h = tf.cast(tf.shape(image[z])[0] // downsample_factor, tf.int32)
        new_w = tf.cast(tf.shape(image[z])[1] // downsample_factor, tf.int32)

        # Resize using TensorFlow's resize function
        image_small = tf.squeeze(
            tf.image.resize(
                img_4d, [new_h, new_w], method=tf.image.ResizeMethod.BILINEAR
            ),
            axis=[0, -1],
        )

        # 2) Create a circular structuring element
        small_selem_radius = tf.maximum(1, selem_radius // downsample_factor)
        small_grid_size = 2 * small_selem_radius + 1

        # Create grid for structuring element
        y_range = tf.range(
            -small_selem_radius, small_selem_radius + 1, dtype=tf.float32
        )
        x_range = tf.range(
            -small_selem_radius, small_selem_radius + 1, dtype=tf.float32
        )
        small_y_grid, small_x_grid = tf.meshgrid(y_range, x_range)

        # Create circular mask
        small_mask = tf.cast(
            tf.sqrt(tf.square(small_y_grid) + tf.square(small_x_grid))
            <= small_selem_radius,
            tf.float32,
        )

        # 3) Apply white top-hat using TensorFlow's morphological operations
        # White top-hat is opening subtracted from the original image
        # Opening is erosion followed by dilation

        # Implement erosion using TensorFlow's conv2d with custom kernel

        # Pad the image to handle boundary conditions
        pad_size = small_selem_radius
        padded = tf.pad(
            tf.expand_dims(tf.expand_dims(image_small, 0), -1),
            [[0, 0], [pad_size, pad_size], [pad_size, pad_size], [0, 0]],
            mode="SYMMETRIC",
        )

        # For erosion, we need to find the minimum value in the neighborhood
        # We can use a trick: negate the image, apply max pooling, then negate again
        neg_padded = -padded

        # Apply convolution with the kernel
        # We use a large negative value for pixels outside the mask
        mask_expanded = tf.reshape(small_mask, [small_grid_size, small_grid_size, 1, 1])
        mask_complement = 1.0 - mask_expanded
        large_neg = tf.constant(-1e9, dtype=tf.float32)

        # Custom erosion using depthwise_conv2d
        eroded_neg = tf.nn.depthwise_conv2d(
            neg_padded + mask_complement * large_neg,
            tf.tile(mask_expanded, [1, 1, 1, 1]),
            strides=[1, 1, 1, 1],
            padding="VALID",
        )

        # Convert back to positive
        eroded = -eroded_neg

        # Implement dilation using similar approach
        # Pad the eroded image
        padded_eroded = tf.pad(
            eroded,
            [[0, 0], [pad_size, pad_size], [pad_size, pad_size], [0, 0]],
            mode="SYMMETRIC",
        )

        # For dilation, we need to find the maximum value in the neighborhood
        # Apply convolution with the kernel
        opened = tf.nn.depthwise_conv2d(
            padded_eroded,
            tf.tile(mask_expanded, [1, 1, 1, 1]),
            strides=[1, 1, 1, 1],
            padding="VALID",
        )

        # Remove batch and channel dimensions
        opened = tf.squeeze(opened, axis=[0, -1])

        # White top-hat is original minus opening
        tophat_small = image_small - opened

        # 4) Calculate background
        background_small = image_small - tophat_small

        # 5) Upscale background to original size
        background_4d = tf.expand_dims(tf.expand_dims(background_small, 0), -1)
        background_large = tf.squeeze(
            tf.image.resize(
                background_4d,
                tf.shape(image[z])[:2],
                method=tf.image.ResizeMethod.BILINEAR,
            ),
            axis=[0, -1],
        )

        # 6) Subtract background and clip negative values
        slice_result = tf.maximum(tf.cast(image[z], tf.float32) - background_large, 0.0)

        # 7) Convert back to original data type
        result_list.append(tf.cast(slice_result, input_dtype))

    # Stack results back into a 3D tensor
    result = tf.stack(result_list, axis=0)

    return result
