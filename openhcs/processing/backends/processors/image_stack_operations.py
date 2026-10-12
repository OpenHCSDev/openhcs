"""Image-stack operations written once against arraybridge ``ArrayLibrary``.

Each backend processor module registers these operations under its own
memory type and passes its ``ArrayLibrary`` leaf. A leaf supplies only the
primitives its array library does differently, so a result here equals what
the backend's own library calls produce. Operations whose algorithm genuinely
differs per backend stay in that backend's module.

Functions taking ``xp``-style calls through ``ops.array_module`` are used only
by the NumPy-compatible libraries (NumPy, CuPy).
"""

from __future__ import annotations

from abc import abstractmethod
from collections.abc import Sequence
from typing import Any

import numpy as np
from arraybridge.libraries import ArrayLibrary
from metaclass_registry import AutoRegisterMeta
from metaclass_registry.strategies import EnumKeyedStrategyMixin

from openhcs.processing.backends.processors.method_axes import (
    SpatialBinMethod,
    StackProjectionMethod,
)


def require_stack(ops: ArrayLibrary, array: Any, name: str = "input") -> None:
    """Require one native array of the leaf's framework with three axes."""

    if not ops.accepts(array):
        raise TypeError(
            f"{name} must be a {ops.display_name} array, got {type(array)}. "
            "No automatic conversion is performed."
        )
    if len(array.shape) != 3:
        raise ValueError(f"{name} must be a 3D array, got {len(array.shape)}D")


# Integer dtypes whose composites and equalized stacks torch and TensorFlow
# clamp to the dtype's limits; other dtypes are cast directly.
CLAMPED_INTEGER_DTYPES = frozenset(
    {"uint8", "uint16", "uint32", "int8", "int16", "int32", "int64"}
)


# ----- weight masks -----


def weight_mask_extent(shape: Any) -> tuple[int, int]:
    """Validate a ``(height, width)`` weight-mask shape."""

    if not isinstance(shape, tuple) or len(shape) != 2:
        raise TypeError("shape must be a tuple of (height, width)")
    return shape


def linear_weight_mask(
    ops: ArrayLibrary,
    height: int,
    width: int,
    margin_ratio: float,
    *,
    ramp_endpoint: bool,
) -> Any:
    """Weights ramping linearly from 0 at the edges to 1 inside the margin.

    ``ramp_endpoint`` states whether each edge ramp reaches 1 on its last
    margin pixel (torch and TensorFlow) or stops one step short (NumPy, CuPy,
    JAX).
    """

    def axis_weights(length: int) -> Any:
        margin = int(ops.floor(length * margin_ratio))
        weights = ops.ones(length, np.float32)
        if margin > 0:
            rising = ops.linspace(0, 1, margin, endpoint=ramp_endpoint)
            falling = ops.linspace(1, 0, margin, endpoint=ramp_endpoint)
            weights = ops.assign(weights, slice(None, margin), rising)
            weights = ops.assign(weights, slice(-margin, None), falling)
        return weights

    return ops.outer(axis_weights(height), axis_weights(width))


# ----- masks and projections -----


def apply_mask(ops: ArrayLibrary, image: Any, mask: Any) -> Any:
    """Multiply a stack by a 2-D (per plane) or 3-D mask in float32."""

    require_stack(ops, image)
    if not ops.accepts(mask) or len(mask.shape) not in (2, 3):
        raise TypeError(f"mask must be a 2D or 3D native array, got {type(mask)}")
    expected = tuple(image.shape[1:]) if len(mask.shape) == 2 else tuple(image.shape)
    if tuple(mask.shape) != expected:
        raise ValueError(
            f"{len(mask.shape)}D mask shape {tuple(mask.shape)} doesn't match "
            f"image shape {expected}"
        )
    masked = ops.astype(image, np.float32) * ops.astype(mask, np.float32)
    return ops.astype(masked, image.dtype)


def max_projection(ops: ArrayLibrary, stack: Any) -> Any:
    """Maximum over the leading axis, shaped ``(1, Y, X)``."""

    require_stack(ops, stack)
    return ops.prepend_axis(ops.max(stack, 0))


def mean_projection(ops: ArrayLibrary, stack: Any) -> Any:
    """Mean over the leading axis in the input dtype, shaped ``(1, Y, X)``."""

    require_stack(ops, stack)
    return ops.prepend_axis(ops.astype(ops.mean(stack, 0), stack.dtype))


def min_projection(ops: ArrayLibrary, stack: Any) -> Any:
    """Minimum over the leading axis, shaped ``(1, Y, X)``."""

    require_stack(ops, stack)
    return ops.prepend_axis(ops.min(stack, 0))


class StackProjection(
    EnumKeyedStrategyMixin[StackProjectionMethod], metaclass=AutoRegisterMeta
):
    """One leading-axis projection, keyed by its method value."""

    __enum_member_attr__ = "method"

    @abstractmethod
    def project(self, ops: ArrayLibrary, stack: Any) -> Any:
        """Return the projection shaped ``(1, Y, X)``."""


class MaxStackProjection(StackProjection):
    method = StackProjectionMethod.MAX

    def project(self, ops: ArrayLibrary, stack: Any) -> Any:
        return max_projection(ops, stack)


class MeanStackProjection(StackProjection):
    method = StackProjectionMethod.MEAN

    def project(self, ops: ArrayLibrary, stack: Any) -> Any:
        return mean_projection(ops, stack)


class MinStackProjection(StackProjection):
    method = StackProjectionMethod.MIN

    def project(self, ops: ArrayLibrary, stack: Any) -> Any:
        return min_projection(ops, stack)


def create_projection(ops: ArrayLibrary, stack: Any, method: Any) -> Any:
    """Project a stack with the method's registered projection.

    ``method`` is any enum whose values name ``StackProjection`` members.
    """

    require_stack(ops, stack)
    return StackProjection.for_enum_member(method).project(ops, stack)


# ----- spatial binning (NumPy-compatible libraries) -----


class SpatialBin(EnumKeyedStrategyMixin[SpatialBinMethod], metaclass=AutoRegisterMeta):
    """Reduction applied within each spatial bin."""

    __enum_member_attr__ = "method"

    @abstractmethod
    def reduce(self, ops: ArrayLibrary, array: Any, axis: tuple[int, ...]) -> Any:
        """Reduce the bin axes."""


class MeanSpatialBin(SpatialBin):
    method = SpatialBinMethod.MEAN

    def reduce(self, ops: ArrayLibrary, array: Any, axis: tuple[int, ...]) -> Any:
        return ops.mean(array, axis)


class SumSpatialBin(SpatialBin):
    method = SpatialBinMethod.SUM

    def reduce(self, ops: ArrayLibrary, array: Any, axis: tuple[int, ...]) -> Any:
        return ops.sum(array, axis)


class MaxSpatialBin(SpatialBin):
    method = SpatialBinMethod.MAX

    def reduce(self, ops: ArrayLibrary, array: Any, axis: tuple[int, ...]) -> Any:
        return ops.max(array, axis)


class MinSpatialBin(SpatialBin):
    method = SpatialBinMethod.MIN

    def reduce(self, ops: ArrayLibrary, array: Any, axis: tuple[int, ...]) -> Any:
        return ops.min(array, axis)


def _require_bin_size(bin_size: int) -> None:
    if bin_size <= 0:
        raise ValueError("bin_size must be positive")


def spatial_bin_2d(
    ops: ArrayLibrary, stack: Any, bin_size: int, method: SpatialBinMethod
) -> Any:
    """Bin each plane in ``bin_size`` x ``bin_size`` blocks."""

    require_stack(ops, stack)
    _require_bin_size(bin_size)
    planes, height, width = stack.shape
    new_height, new_width = height // bin_size, width // bin_size
    if new_height == 0 or new_width == 0:
        raise ValueError(
            f"bin_size {bin_size} is too large for image dimensions {height}x{width}"
        )
    cropped = stack[:, : new_height * bin_size, : new_width * bin_size]
    blocks = cropped.reshape(planes, new_height, bin_size, new_width, bin_size)
    binned = SpatialBin.for_enum_member(method).reduce(ops, blocks, (2, 4))
    return ops.astype(binned, stack.dtype)


def spatial_bin_3d(
    ops: ArrayLibrary, stack: Any, bin_size: int, method: SpatialBinMethod
) -> Any:
    """Bin the stack in ``bin_size``-sided cubes."""

    require_stack(ops, stack)
    _require_bin_size(bin_size)
    depth, height, width = stack.shape
    new_depth, new_height, new_width = (
        depth // bin_size,
        height // bin_size,
        width // bin_size,
    )
    if new_depth == 0 or new_height == 0 or new_width == 0:
        raise ValueError(
            f"bin_size {bin_size} is too large for stack dimensions "
            f"{depth}x{height}x{width}"
        )
    cropped = stack[
        : new_depth * bin_size, : new_height * bin_size, : new_width * bin_size
    ]
    blocks = cropped.reshape(
        new_depth, bin_size, new_height, bin_size, new_width, bin_size
    )
    binned = SpatialBin.for_enum_member(method).reduce(ops, blocks, (1, 3, 5))
    return ops.astype(binned, stack.dtype)


# ----- cropping, equalization, normalization (NumPy-compatible libraries) -----


def crop(
    ops: ArrayLibrary,
    image: Any,
    start_x: int,
    start_y: int,
    start_z: int,
    width: int,
    height: int,
    depth: int,
) -> Any:
    """Return the ``(depth, height, width)`` substack at the start coordinates."""

    require_stack(ops, image)
    if width <= 0 or height <= 0 or depth <= 0:
        raise ValueError(
            "Crop dimensions must be positive: "
            f"width={width}, height={height}, depth={depth}"
        )
    if start_x < 0 or start_y < 0 or start_z < 0:
        raise ValueError(
            "Start coordinates must be non-negative: "
            f"start_x={start_x}, start_y={start_y}, start_z={start_z}"
        )
    input_depth, input_height, input_width = image.shape
    end_x, end_y, end_z = start_x + width, start_y + height, start_z + depth
    if end_x > input_width or end_y > input_height or end_z > input_depth:
        raise ValueError(
            "Crop region extends beyond image bounds. "
            f"Image shape: {image.shape}, "
            f"Crop region: ({start_z}:{end_z}, {start_y}:{end_y}, {start_x}:{end_x})"
        )
    return image[start_z:end_z, start_y:end_y, start_x:end_x]


def stack_equalize_histogram(
    ops: ArrayLibrary, stack: Any, bins: int, range_min: float, range_max: float
) -> Any:
    """Equalize with one histogram over the whole stack."""

    require_stack(ops, stack)
    xp = ops.array_module
    input_dtype = stack.dtype
    is_integer = xp.issubdtype(input_dtype, xp.integer)
    hist, bin_edges = xp.histogram(
        stack.flatten(), bins=bins, range=(range_min, range_max)
    )
    cdf = hist.cumsum()
    if cdf[-1] > 0:
        if is_integer:
            cdf = xp.iinfo(input_dtype).max * cdf / cdf[-1]
        else:
            cdf = cdf / cdf[-1]
    equalized = xp.interp(stack.flatten(), bin_edges[:-1], cdf).reshape(stack.shape)
    if is_integer:
        limits = xp.iinfo(input_dtype)
        return xp.clip(equalized, limits.min, limits.max).astype(input_dtype)
    return equalized.astype(input_dtype)


def dtype_target_range(dtype: Any) -> tuple[float, float]:
    """The natural intensity range of ``dtype``: integer limits, or [0, 1]."""

    np_dtype = np.dtype(dtype)
    if np.issubdtype(np_dtype, np.integer):
        limits = np.iinfo(np_dtype)
        return limits.min, limits.max
    if np_dtype in (np.float16, np.float32, np.float64):
        return 0.0, 1.0
    return 0, 65535


def _target_range(
    dtype: Any, target_min: float | None, target_max: float | None
) -> tuple[float, float]:
    natural_min, natural_max = dtype_target_range(dtype)
    return (
        natural_min if target_min is None else target_min,
        natural_max if target_max is None else target_max,
    )


def percentile_normalize_planes(
    ops: ArrayLibrary,
    image: Any,
    low_percentile: float,
    high_percentile: float,
    target_min: float | None,
    target_max: float | None,
) -> Any:
    """Stretch each plane's percentile range to the target range."""

    require_stack(ops, image)
    xp = ops.array_module
    target_min, target_max = _target_range(image.dtype, target_min, target_max)
    result = xp.zeros_like(image, dtype=np.float32)
    for z in range(image.shape[0]):
        p_low, p_high = xp.percentile(image[z], (low_percentile, high_percentile))
        if p_high == p_low:
            result[z] = xp.ones_like(image[z]) * target_min
            continue
        clipped = xp.clip(image[z], p_low, p_high)
        result[z] = (clipped - p_low) * (target_max - target_min) / (
            p_high - p_low
        ) + target_min
    return result.astype(image.dtype)


def percentile_normalize_stack(
    ops: ArrayLibrary,
    stack: Any,
    low_percentile: float,
    high_percentile: float,
    target_min: float | None,
    target_max: float | None,
) -> Any:
    """Stretch the whole stack's percentile range to the target range."""

    require_stack(ops, stack)
    xp = ops.array_module
    target_min, target_max = _target_range(stack.dtype, target_min, target_max)
    p_low = xp.percentile(stack, low_percentile)
    p_high = xp.percentile(stack, high_percentile)
    if p_high == p_low:
        return (xp.ones_like(stack) * target_min).astype(stack.dtype)
    clipped = xp.clip(stack, p_low, p_high)
    normalized = (clipped - p_low) * (target_max - target_min) / (
        p_high - p_low
    ) + target_min
    return normalized.astype(stack.dtype)


# ----- composites -----


def composite_weights(weights: Sequence[float] | None, count: int) -> list[float]:
    """Validate per-plane weights and normalize them to sum to one."""

    if weights is None:
        weights = [1.0 / count] * count
    elif isinstance(weights, (list, tuple)):
        weights = list(weights)
        if len(weights) != count:
            raise ValueError(
                f"Number of weights ({len(weights)}) must match number of slices ({count})"
            )
    else:
        raise TypeError(
            f"weights must be a list of values or None, got {type(weights)}: {weights}"
        )
    total = sum(weights)
    if total == 0:
        raise ValueError("Sum of weights cannot be zero")
    return [weight / total for weight in weights]


def weighted_composite(
    ops: ArrayLibrary, stack: Any, weights: Sequence[float] | None
) -> Any:
    """Float32 weighted sum of the planes, shaped ``(1, Y, X)``, in the input dtype."""

    require_stack(ops, stack)
    count = stack.shape[0]
    plane_weights = ops.astype(
        ops.array_module.asarray(composite_weights(weights, count)), np.float32
    ).reshape(count, 1, 1)
    weighted = ops.astype(stack, np.float32) * plane_weights
    return ops.astype(ops.prepend_axis(ops.sum(weighted, 0)), stack.dtype)
