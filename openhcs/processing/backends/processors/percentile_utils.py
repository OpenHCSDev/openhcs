"""
Shared utilities for percentile normalization across all backends.

This module provides common functionality to ensure consistent behavior
between NumPy, CuPy, PyTorch, JAX, TensorFlow, and other implementations.
"""

import numpy as np
from typing import Tuple, Union


def get_dtype_range(dtype) -> Tuple[Union[int, float], Union[int, float]]:
    """
    Get the natural min/max range for a numpy-compatible dtype.

    Args:
        dtype: NumPy dtype or equivalent (works with CuPy, PyTorch, etc.)

    Returns:
        Tuple of (min_value, max_value) for the dtype
    """
    # Convert to numpy dtype for consistent comparison
    if hasattr(dtype, "type"):
        # Handle CuPy/PyTorch dtypes that have .type attribute
        np_dtype = dtype.type
    else:
        # Handle direct numpy dtypes
        np_dtype = dtype

    # Map dtypes to their natural ranges
    if np_dtype == np.uint8:
        return 0, 255
    elif np_dtype == np.uint16:
        return 0, 65535
    elif np_dtype == np.uint32:
        return 0, 4294967295
    elif np_dtype == np.uint64:
        return 0, 18446744073709551615
    elif np_dtype == np.int8:
        return -128, 127
    elif np_dtype == np.int16:
        return -32768, 32767
    elif np_dtype == np.int32:
        return -2147483648, 2147483647
    elif np_dtype == np.int64:
        return -9223372036854775808, 9223372036854775807
    elif np_dtype in (np.float16, np.float32, np.float64):
        return 0.0, 1.0
    else:
        # Fallback for unknown dtypes - assume 16-bit range
        return 0, 65535


def resolve_target_range(
    stack_dtype, target_min=None, target_max=None
) -> Tuple[Union[int, float], Union[int, float]]:
    """
    Resolve target min/max values, auto-detecting from dtype if not specified.

    Args:
        stack_dtype: The dtype of the input stack
        target_min: Explicit target minimum (None for auto-detection)
        target_max: Explicit target maximum (None for auto-detection)

    Returns:
        Tuple of (resolved_min, resolved_max)
    """
    if target_min is None or target_max is None:
        auto_min, auto_max = get_dtype_range(stack_dtype)
        if target_min is None:
            target_min = auto_min
        if target_max is None:
            target_max = auto_max

    return target_min, target_max


def percentile_normalize_core(
    stack,
    low_percentile: float,
    high_percentile: float,
    target_min: Union[int, float],
    target_max: Union[int, float],
    percentile_func,
    clip_func,
    ones_like_func,
    preserve_dtype: bool = True,
):
    """
    Core percentile normalization logic that works with any array backend.

    This function contains the shared algorithm while allowing different backends
    to provide their own array operations (percentile, clip, ones_like).

    Args:
        stack: Input array (NumPy, CuPy, PyTorch, etc.)
        low_percentile: Lower percentile (0-100)
        high_percentile: Upper percentile (0-100)
        target_min: Target minimum value
        target_max: Target maximum value
        percentile_func: Backend-specific percentile function
        clip_func: Backend-specific clip function
        ones_like_func: Backend-specific ones_like function
        preserve_dtype: Whether to preserve input dtype

    Returns:
        Normalized array with same backend as input
    """
    # Calculate global percentiles across the entire stack
    p_low = percentile_func(stack, low_percentile)
    p_high = percentile_func(stack, high_percentile)

    # Avoid division by zero
    if p_high == p_low:
        result = ones_like_func(stack) * target_min
        if preserve_dtype:
            return result.astype(stack.dtype)
        else:
            # Legacy behavior: convert to uint16-equivalent
            return result.astype(
                stack.dtype if hasattr(stack, "dtype") else type(stack)
            )

    # Clip and normalize to target range
    clipped = clip_func(stack, p_low, p_high)
    normalized = (clipped - p_low) * (target_max - target_min) / (
        p_high - p_low
    ) + target_min

    # Always preserve input dtype
    return normalized.astype(stack.dtype)


def slice_percentile_normalize_core(
    image,
    low_percentile: float,
    high_percentile: float,
    target_min: Union[int, float],
    target_max: Union[int, float],
    percentile_func,
    clip_func,
    ones_like_func,
    zeros_like_func,
    preserve_dtype: bool = True,
):
    """
    Core slice-by-slice percentile normalization logic.

    Args:
        image: Input 3D array (Z, Y, X)
        low_percentile: Lower percentile (0-100)
        high_percentile: Upper percentile (0-100)
        target_min: Target minimum value
        target_max: Target maximum value
        percentile_func: Backend-specific percentile function
        clip_func: Backend-specific clip function
        ones_like_func: Backend-specific ones_like function
        zeros_like_func: Backend-specific zeros_like function
        preserve_dtype: Whether to preserve input dtype

    Returns:
        Normalized array with same backend as input
    """
    # Process each Z-slice independently
    # Use float32 for intermediate calculations to avoid precision loss
    result = zeros_like_func(
        image, dtype=np.float32 if hasattr(image, "dtype") else None
    )

    for z in range(image.shape[0]):
        # Get percentile values for this slice
        p_low, p_high = percentile_func(image[z], (low_percentile, high_percentile))

        # Avoid division by zero
        if p_high == p_low:
            result[z] = ones_like_func(image[z]) * target_min
            continue

        # Clip and normalize to target range
        clipped = clip_func(image[z], p_low, p_high)
        normalized = (clipped - p_low) * (target_max - target_min) / (
            p_high - p_low
        ) + target_min
        result[z] = normalized

    # Always preserve input dtype
    return result.astype(image.dtype)
