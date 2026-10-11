"""CuPy processor registrations.

Shared operations are written once in ``image_stack_operations``; this module
registers them for CuPy and holds the CuPy-specific algorithms (sharpening,
top-hat, Sobel kernels).
"""

from __future__ import annotations

from abc import abstractmethod
from typing import List, Optional, Tuple

from arraybridge import MemoryType
from arraybridge.array_operations import ArrayOperations
from metaclass_registry import AutoRegisterMeta

from openhcs.core.artifacts import ArtifactSpec, ImageArtifactType
from openhcs.utils.import_utils import optional_import_placeholder
from openhcs.core.memory import cupy as cupy_func
from openhcs.core.pipeline.function_contracts import artifact_inputs
from metaclass_registry.strategies import EnumKeyedStrategyMixin
from openhcs.processing.backends.processors import image_stack_operations as operations
from openhcs.processing.backends.processors.method_axes import (
    EdgeMagnitudeMethod,
    ScipyBoundaryMode,
    SobelKernelBoundaryMode,
    SpatialBinMethod,
    StackProjectionMethod,
)

cp = optional_import_placeholder("cupy")

OPERATIONS = ArrayOperations.for_memory(MemoryType.CUPY)


@cupy_func
def create_linear_weight_mask(
    height: int, width: int, margin_ratio: float = 0.1
) -> "cp.ndarray":
    """
    Create a 2D weight mask that linearly ramps from 0 at the edges to 1 in the center.

    Args:
        height: Height of the mask
        width: Width of the mask
        margin_ratio: Ratio of the margin to the image size

    Returns:
        2D CuPy weight mask of shape (height, width)
    """
    return operations.linear_weight_mask(
        OPERATIONS, height, width, margin_ratio, ramp_endpoint=False
    )


@cupy_func
def sharpen(
    image: "cp.ndarray", radius: float = 1.0, amount: float = 1.0
) -> "cp.ndarray":
    """
    Sharpen a 3D image using unsharp masking - GPU PARALLELIZED.

    This applies sharpening to each Z-slice independently using vectorized operations
    for maximum GPU utilization. Normalization and rescaling are fully parallelized.

    Args:
        image: 3D CuPy array of shape (Z, Y, X)
        radius: Radius of Gaussian blur
        amount: Sharpening strength

    Returns:
        Sharpened 3D CuPy array of shape (Z, Y, X)
    """
    from cupyx.scipy import ndimage

    operations.require_stack(OPERATIONS, image)

    # Store original dtype
    dtype = image.dtype

    # Convert to float32 for processing
    image_float = image.astype(cp.float32)

    # Vectorized per-slice normalization - GPU PARALLELIZED
    # Get max value per slice: shape (Z, 1, 1) for broadcasting
    max_per_slice = cp.max(image_float, axis=(1, 2), keepdims=True)
    image_norm = image_float / max_per_slice

    # Apply 3D Gaussian blur with sigma_z=0 for slice-wise processing - GPU PARALLELIZED
    # This processes all slices simultaneously while keeping Z-slices independent
    blurred = ndimage.gaussian_filter(image_norm, sigma=(0, radius, radius))

    # Apply unsharp mask: original + amount * (original - blurred) - GPU PARALLELIZED
    sharpened = image_norm + amount * (image_norm - blurred)

    # Clip to valid range - GPU PARALLELIZED
    sharpened = cp.clip(sharpened, 0, 1.0)

    # Vectorized rescaling back to original range - GPU PARALLELIZED
    min_per_slice = cp.min(sharpened, axis=(1, 2), keepdims=True)
    max_per_slice = cp.max(sharpened, axis=(1, 2), keepdims=True)

    # Avoid division by zero using broadcasting
    range_per_slice = max_per_slice - min_per_slice
    # Only rescale slices where max > min
    valid_range = range_per_slice > 0
    sharpened_rescaled = cp.where(
        valid_range,
        (sharpened - min_per_slice) * 65535 / range_per_slice,
        sharpened * 65535,
    )

    # Convert back to original dtype
    return sharpened_rescaled.astype(dtype)


@cupy_func
def percentile_normalize(
    image: "cp.ndarray",
    low_percentile: float = 1.0,
    high_percentile: float = 99.0,
    target_min: float = None,
    target_max: float = None,
    preserve_dtype: bool = True,
) -> "cp.ndarray":
    """
    Normalize a 3D image using percentile-based contrast stretching.

    This applies normalization to each Z-slice independently using slice-by-slice
    processing for algorithmic reasons (each slice needs different percentile values).
    Each slice operation is GPU parallelized across Y,X dimensions.

    Args:
        image: 3D CuPy array of shape (Z, Y, X)
        low_percentile: Lower percentile (0-100)
        high_percentile: Upper percentile (0-100)
        target_min: Target minimum value (auto-detected from dtype if None)
        target_max: Target maximum value (auto-detected from dtype if None)
        preserve_dtype: No effect; the output always has the input dtype.

    Returns:
        Normalized 3D CuPy array of shape (Z, Y, X) with the input dtype
    """
    del preserve_dtype  # the output always has the input dtype
    return operations.percentile_normalize_planes(
        OPERATIONS, image, low_percentile, high_percentile, target_min, target_max
    )


@cupy_func
def stack_percentile_normalize(
    stack: "cp.ndarray",
    low_percentile: float = 1.0,
    high_percentile: float = 99.0,
    target_min: float = None,
    target_max: float = None,
    preserve_dtype: bool = True,
) -> "cp.ndarray":
    """
    Normalize a stack using global percentile-based contrast stretching.

    This ensures consistent normalization across all Z-slices by computing
    global percentiles across the entire stack.

    Args:
        stack: 3D CuPy array of shape (Z, Y, X)
        low_percentile: Lower percentile (0-100)
        high_percentile: Upper percentile (0-100)
        target_min: Target minimum value (auto-detected from dtype if None)
        target_max: Target maximum value (auto-detected from dtype if None)
        preserve_dtype: No effect; the output always has the input dtype.

    Returns:
        Normalized 3D CuPy array of shape (Z, Y, X) with the input dtype
    """
    del preserve_dtype  # the output always has the input dtype
    return operations.percentile_normalize_stack(
        OPERATIONS, stack, low_percentile, high_percentile, target_min, target_max
    )


@cupy_func
def create_composite(
    stack: "cp.ndarray", weights: Optional[List[float]] = None
) -> "cp.ndarray":
    """
    Create a composite image from a 3D stack where each slice is a channel.

    Args:
        stack: 3D CuPy array of shape (N, Y, X) where N is number of channel slices
        weights: List of weights for each slice. If None, equal weights are used.

    Returns:
        Composite 3D CuPy array of shape (1, Y, X)
    """
    return operations.weighted_composite(OPERATIONS, stack, weights)


@artifact_inputs(ArtifactSpec.input("mask", ImageArtifactType, parameter_name="mask"))
@cupy_func
def apply_mask(image: "cp.ndarray", mask: "cp.ndarray") -> "cp.ndarray":
    """
    Apply a mask to a 3D image.

    This applies the mask to each Z-slice independently if mask is 2D,
    or applies the 3D mask directly if mask is 3D.

    Args:
        image: 3D CuPy array of shape (Z, Y, X)
        mask: 3D CuPy array of shape (Z, Y, X) or 2D CuPy array of shape (Y, X)

    Returns:
        Masked 3D CuPy array of shape (Z, Y, X)
    """
    return operations.apply_mask(OPERATIONS, image, mask)


@cupy_func
def create_weight_mask(
    shape: Tuple[int, int], margin_ratio: float = 0.1
) -> "cp.ndarray":
    """
    Create a weight mask for blending images.

    Args:
        shape: Shape of the mask (height, width)
        margin_ratio: Ratio of image size to use as margin

    Returns:
        2D CuPy weight mask of shape (Y, X)
    """
    return create_linear_weight_mask(
        *operations.weight_mask_extent(shape), margin_ratio
    )


@cupy_func
def max_projection(stack: "cp.ndarray") -> "cp.ndarray":
    """
    Create a maximum intensity projection from a Z-stack.

    Args:
        stack: 3D CuPy array of shape (Z, Y, X)

    Returns:
        3D CuPy array of shape (1, Y, X)
    """
    return operations.max_projection(OPERATIONS, stack)


@cupy_func
def mean_projection(stack: "cp.ndarray") -> "cp.ndarray":
    """
    Create a mean intensity projection from a Z-stack.

    Args:
        stack: 3D CuPy array of shape (Z, Y, X)

    Returns:
        3D CuPy array of shape (1, Y, X)
    """
    return operations.mean_projection(OPERATIONS, stack)


@cupy_func
def spatial_bin_2d(
    stack: "cp.ndarray",
    bin_size: int = 2,
    method: SpatialBinMethod = SpatialBinMethod.MEAN,
) -> "cp.ndarray":
    """
    Apply 2D spatial binning to each slice in the stack - GPU accelerated.

    Reduces spatial resolution by combining neighboring pixels in 2D blocks.
    Each slice is processed independently using efficient GPU operations.

    Args:
        stack: 3D CuPy array of shape (Z, Y, X)
        bin_size: Size of the square binning kernel (e.g., 2 = 2x2 binning)
        method: Binning method - "mean", "sum", "max", or "min"

    Returns:
        Binned 3D CuPy array of shape (Z, Y//bin_size, X//bin_size)
    """
    return operations.spatial_bin_2d(OPERATIONS, stack, bin_size, method)


@cupy_func
def spatial_bin_3d(
    stack: "cp.ndarray",
    bin_size: int = 2,
    method: SpatialBinMethod = SpatialBinMethod.MEAN,
) -> "cp.ndarray":
    """
    Apply 3D spatial binning to the entire stack - GPU accelerated.

    Reduces spatial resolution by combining neighboring voxels in 3D blocks
    using efficient GPU operations.

    Args:
        stack: 3D CuPy array of shape (Z, Y, X)
        bin_size: Size of the cubic binning kernel (e.g., 2 = 2x2x2 binning)
        method: Binning method - "mean", "sum", "max", or "min"

    Returns:
        Binned 3D CuPy array of shape (Z//bin_size, Y//bin_size, X//bin_size)
    """
    return operations.spatial_bin_3d(OPERATIONS, stack, bin_size, method)


@cupy_func
def stack_equalize_histogram(
    stack: "cp.ndarray",
    bins: int = 65536,
    range_min: float = 0.0,
    range_max: float = 65535.0,
) -> "cp.ndarray":
    """
    Apply histogram equalization to an entire stack.

    This ensures consistent contrast enhancement across all Z-slices by
    computing a global histogram across the entire stack.

    Args:
        stack: 3D CuPy array of shape (Z, Y, X)
        bins: Number of bins for histogram computation
        range_min: Minimum value for histogram range
        range_max: Maximum value for histogram range

    Returns:
        Equalized 3D CuPy array of shape (Z, Y, X)
    """
    return operations.stack_equalize_histogram(
        OPERATIONS, stack, bins, range_min, range_max
    )


@cupy_func
def create_projection(
    stack: "cp.ndarray",
    method: StackProjectionMethod = StackProjectionMethod.MAX,
) -> "cp.ndarray":
    """
    Create a projection from a stack using the specified method.

    Args:
        stack: 3D CuPy array of shape (Z, Y, X)
        method: Projection method served by ``image_stack_operations.StackProjection``

    Returns:
        3D CuPy array of shape (1, Y, X)
    """
    return operations.create_projection(OPERATIONS, stack, method)


@cupy_func
def crop(
    input_image: "cp.ndarray",
    start_x: int = 0,
    start_y: int = 0,
    start_z: int = 0,
    width: int = 1,
    height: int = 1,
    depth: int = 1,
) -> "cp.ndarray":
    """
    Crop a given substack out of a given image stack.

    Equivalent to pyclesperanto.crop() but using CuPy operations.

    Parameters
    ----------
    input_image: cp.ndarray
        Input 3D image to process of shape (Z, Y, X)
    start_x: int (= 0)
        Starting index coordinate x
    start_y: int (= 0)
        Starting index coordinate y
    start_z: int (= 0)
        Starting index coordinate z
    width: int (= 1)
        Width size of the region to crop
    height: int (= 1)
        Height size of the region to crop
    depth: int (= 1)
        Depth size of the region to crop

    Returns
    -------
    cp.ndarray
        Cropped 3D array of shape (depth, height, width)
    """
    return operations.crop(
        OPERATIONS, input_image, start_x, start_y, start_z, width, height, depth
    )


def _create_disk_cupy(radius: int) -> "cp.ndarray":
    """Create a disk structuring element using CuPy - MATCH NUMPY EXACTLY"""
    y, x = cp.ogrid[-radius : radius + 1, -radius : radius + 1]
    mask = x * x + y * y <= radius * radius
    return mask.astype(cp.uint8)


def _resize_cupy_better_match(
    image: "cp.ndarray",
    output_shape: tuple,
    anti_aliasing: bool = True,
    preserve_range: bool = True,
) -> "cp.ndarray":
    """
    Resize image using CuPy to better match scikit-image's transform.resize behavior.

    Key differences from original:
    1. Better anti-aliasing sigma calculation
    2. Proper preserve_range handling without rescaling
    3. More accurate zoom parameters
    """
    from cupyx.scipy import ndimage as cupy_ndimage

    # Calculate zoom factors
    zoom_factors = [output_shape[i] / image.shape[i] for i in range(len(output_shape))]

    # Convert to float32 for processing
    image_float = image.astype(cp.float32)

    # Apply anti-aliasing if downsampling
    if anti_aliasing and any(z < 1.0 for z in zoom_factors):
        # Use scikit-image's sigma calculation: sigma = (1/zoom - 1) / 2
        # But ensure minimum sigma and handle edge cases
        sigma = []
        for z in zoom_factors:
            if z < 1.0:
                s = (1.0 / z - 1.0) / 2.0
                sigma.append(max(s, 0.5))  # Minimum sigma for stability
            else:
                sigma.append(0.0)

        # Apply Gaussian smoothing before downsampling
        if any(s > 0 for s in sigma):
            image_float = cupy_ndimage.gaussian_filter(image_float, sigma)

    # Perform zoom with bilinear interpolation (order=1)
    resized = cupy_ndimage.zoom(image_float, zoom_factors, order=1)

    # Handle preserve_range properly - don't rescale, just maintain dtype range
    if preserve_range:
        # Clip to valid range for the original dtype
        if image.dtype == cp.uint16:
            resized = cp.clip(resized, 0, 65535)
        elif image.dtype == cp.uint8:
            resized = cp.clip(resized, 0, 255)
        # For other dtypes, keep as-is

    return resized


@cupy_func
def tophat(
    image: "cp.ndarray",
    selem_radius: int = 50,
    downsample_factor: int = 4,
    downsample_anti_aliasing: bool = True,
    upsample_anti_aliasing: bool = False,
) -> "cp.ndarray":
    """
    Apply white top-hat filter to a 3D image for background removal.

    This applies the filter to each Z-slice independently using slice-by-slice
    processing for algorithmic reasons (complex multi-step processing with
    slice-specific intermediate results). Each slice operation is GPU parallelized.

    Args:
        image: 3D CuPy array of shape (Z, Y, X)
        selem_radius: Radius of the structuring element disk
        downsample_factor: Factor by which to downsample the image for processing
        downsample_anti_aliasing: Whether to use anti-aliasing when downsampling
        upsample_anti_aliasing: Whether to use anti-aliasing when upsampling

    Returns:
        Filtered 3D CuPy array of shape (Z, Y, X)
    """
    from cupyx.scipy import ndimage

    operations.require_stack(OPERATIONS, image)

    # Process each Z-slice independently - IMPROVED MATCH TO NUMPY
    # NOTE: For loop is ALGORITHMICALLY NECESSARY here due to complex multi-step
    # processing (downsample, morphology, upsample, subtract) with slice-specific
    # intermediate results. Vectorization would require significant algorithm restructuring.
    result = cp.zeros_like(image)

    for z in range(image.shape[0]):
        # Store original data type - MATCH NUMPY EXACTLY
        input_dtype = image[z].dtype

        # 1) Downsample - IMPROVED MATCH TO NUMPY
        target_shape = (
            image[z].shape[0] // downsample_factor,
            image[z].shape[1] // downsample_factor,
        )
        image_small = _resize_cupy_better_match(
            image[z],
            target_shape,
            anti_aliasing=downsample_anti_aliasing,
            preserve_range=True,
        )

        # 2) Build structuring element for the smaller image - MATCH NUMPY EXACTLY
        selem_small = _create_disk_cupy(selem_radius // downsample_factor)

        # 3) White top-hat on the smaller image - MATCH NUMPY EXACTLY
        tophat_small = ndimage.white_tophat(image_small, structure=selem_small)

        # 4) Upscale background to original size - IMPROVED MATCH TO NUMPY
        background_small = image_small - tophat_small
        background_large = _resize_cupy_better_match(
            background_small,
            image[z].shape,
            anti_aliasing=upsample_anti_aliasing,
            preserve_range=True,
        )

        # 5) Subtract background and clip negative values - MATCH NUMPY EXACTLY
        slice_result = cp.maximum(image[z] - background_large, 0)

        # 6) Convert back to original data type - MATCH NUMPY EXACTLY
        result[z] = slice_result.astype(input_dtype)

    return result


# Lazy initialization of ElementwiseKernel to avoid import errors
_sobel_2d_parallel = None


def _get_sobel_2d_kernel():
    """Get or create the Sobel 2D parallel kernel."""
    global _sobel_2d_parallel
    if _sobel_2d_parallel is None:
        _sobel_2d_parallel = cp.ElementwiseKernel(
            "raw T input, int32 Y, int32 X, int32 mode, T cval",
            "T output",
            """
            // Calculate which slice, row, col this thread handles
            int z = i / (Y * X);
            int y = (i % (Y * X)) / X;
            int x = i % X;

            // Calculate base index for this slice
            int slice_base = z * Y * X;

            // Helper function to get pixel with configurable boundary handling
            auto get_pixel = [&](int py, int px) -> T {
                if (mode == 0) {  // constant
                    if (py < 0 || py >= Y || px < 0 || px >= X) return cval;
                } else if (mode == 1) {  // reflect
                    py = py < 0 ? -py : (py >= Y ? 2*Y - py - 2 : py);
                    px = px < 0 ? -px : (px >= X ? 2*X - px - 2 : px);
                } else if (mode == 2) {  // nearest
                    py = py < 0 ? 0 : (py >= Y ? Y-1 : py);
                    px = px < 0 ? 0 : (px >= X ? X-1 : px);
                } else if (mode == 3) {  // wrap
                    py = py < 0 ? py + Y : (py >= Y ? py - Y : py);
                    px = px < 0 ? px + X : (px >= X ? px - X : px);
                }
                return input[slice_base + py * X + px];
            };

            // Sobel X kernel: [[-1,0,1],[-2,0,2],[-1,0,1]] (within slice only)
            T gx = -get_pixel(y-1, x-1) + get_pixel(y-1, x+1) +
                   -2*get_pixel(y, x-1) + 2*get_pixel(y, x+1) +
                   -get_pixel(y+1, x-1) + get_pixel(y+1, x+1);

            // Sobel Y kernel: [[-1,-2,-1],[0,0,0],[1,2,1]] (within slice only)
            T gy = -get_pixel(y-1, x-1) - 2*get_pixel(y-1, x) - get_pixel(y-1, x+1) +
                    get_pixel(y+1, x-1) + 2*get_pixel(y+1, x) + get_pixel(y+1, x+1);

            // Calculate magnitude
            output = sqrt(gx*gx + gy*gy);
            """,
            "sobel_2d_parallel",
        )
    return _sobel_2d_parallel


@cupy_func
def sobel_2d_vectorized(
    image: "cp.ndarray",
    mode: SobelKernelBoundaryMode = SobelKernelBoundaryMode.REFLECT,
    cval: float = 0.0,
) -> "cp.ndarray":
    """
    Apply 2D Sobel edge detection to all slices simultaneously - TRUE GPU PARALLELIZED.

    Each slice is treated as an independent 2D grayscale image. All pixels across
    all slices are processed in parallel on the GPU with slice independence guaranteed.
    Uses ElementwiseKernel for maximum performance and true parallelization.

    Args:
        image: 3D CuPy array of shape (Z, Y, X)
        mode: Boundary handling mode ('constant', 'reflect', 'nearest', 'wrap')
        cval: Constant value for 'constant' mode

    Returns:
        Edge magnitude as 3D CuPy array of shape (Z, Y, X)
    """
    operations.require_stack(OPERATIONS, image)

    Z, Y, X = image.shape
    input_float = image.astype(cp.float32)
    output = cp.zeros_like(input_float)

    # Launch parallel kernel - each thread processes one pixel
    sobel_kernel = _get_sobel_2d_kernel()
    sobel_kernel(input_float, Y, X, mode.kernel_code, cp.float32(cval), output)

    return output.astype(image.dtype)


@cupy_func
def sobel_3d_voxel(
    image: "cp.ndarray",
    mode: ScipyBoundaryMode = ScipyBoundaryMode.REFLECT,
    cval: float = 0.0,
) -> "cp.ndarray":
    """
    Apply true 3D voxel Sobel edge detection including Z-axis gradients - GPU PARALLELIZED.

    This computes gradients in all three spatial dimensions (X, Y, Z) for true
    volumetric edge detection. Useful for 3D structure analysis where Z-dimension
    has spatial meaning (not just independent slices).

    Args:
        image: 3D CuPy array of shape (Z, Y, X)
        mode: Boundary handling mode ('constant', 'reflect', 'nearest', 'wrap', 'mirror')
        cval: Constant value for 'constant' mode

    Returns:
        3D edge magnitude as 3D CuPy array of shape (Z, Y, X)
    """
    return _sobel_3d_voxel(image, mode=mode.value, cval=cval)


def _sobel_3d_voxel(
    image: "cp.ndarray",
    *,
    mode: str,
    cval: float,
) -> "cp.ndarray":
    """Apply the 3-D Sobel implementation at its library string boundary."""
    from cupyx.scipy import ndimage

    operations.require_stack(OPERATIONS, image)

    # Convert to float32 for processing
    image_float = image.astype(cp.float32)

    # Apply Sobel filters in all three directions - GPU PARALLELIZED
    sobel_x = ndimage.sobel(
        image_float, axis=2, mode=mode, cval=cval
    )  # X-direction gradients
    sobel_y = ndimage.sobel(
        image_float, axis=1, mode=mode, cval=cval
    )  # Y-direction gradients
    sobel_z = ndimage.sobel(
        image_float, axis=0, mode=mode, cval=cval
    )  # Z-direction gradients

    # Calculate 3D magnitude - GPU PARALLELIZED
    magnitude = cp.sqrt(sobel_x**2 + sobel_y**2 + sobel_z**2)

    return magnitude.astype(image.dtype)


@cupy_func
def sobel_components(
    image: "cp.ndarray",
    include_z: bool = False,
    mode: ScipyBoundaryMode = ScipyBoundaryMode.REFLECT,
    cval: float = 0.0,
) -> tuple:
    """
    Return individual Sobel gradient components - GPU PARALLELIZED.

    This provides access to directional gradients for advanced analysis.
    Useful when you need to analyze edge orientation or directional information.

    Args:
        image: 3D CuPy array of shape (Z, Y, X)
        include_z: Whether to include Z-direction gradients (3D analysis)
        mode: Boundary handling mode ('constant', 'reflect', 'nearest', 'wrap', 'mirror')
        cval: Constant value for 'constant' mode

    Returns:
        Tuple of gradient components:
        - If include_z=False: (sobel_x, sobel_y) - 2D gradients per slice
        - If include_z=True: (sobel_x, sobel_y, sobel_z) - 3D gradients
    """
    from cupyx.scipy import ndimage

    operations.require_stack(OPERATIONS, image)

    # Convert to float32 for processing
    image_float = image.astype(cp.float32)

    # Apply Sobel filters - GPU PARALLELIZED
    sobel_x = ndimage.sobel(image_float, axis=2, mode=mode.value, cval=cval).astype(
        image.dtype
    )  # X-direction
    sobel_y = ndimage.sobel(image_float, axis=1, mode=mode.value, cval=cval).astype(
        image.dtype
    )  # Y-direction

    if include_z:
        sobel_z = ndimage.sobel(image_float, axis=0, mode=mode.value, cval=cval).astype(
            image.dtype
        )  # Z-direction
        return sobel_x, sobel_y, sobel_z
    else:
        return sobel_x, sobel_y


class CupyEdgeMagnitudeStrategy(
    EnumKeyedStrategyMixin[EdgeMagnitudeMethod], metaclass=AutoRegisterMeta
):
    __enum_member_attr__ = "method"

    @abstractmethod
    def apply(
        self, image: "cp.ndarray", *, mode: SobelKernelBoundaryMode, cval: float
    ) -> "cp.ndarray":
        raise NotImplementedError


class CupySlice2DEdgeMagnitudeStrategy(CupyEdgeMagnitudeStrategy):
    method = EdgeMagnitudeMethod.SLICE_2D

    def apply(
        self, image: "cp.ndarray", *, mode: SobelKernelBoundaryMode, cval: float
    ) -> "cp.ndarray":
        return sobel_2d_vectorized(image, mode=mode, cval=cval)


class CupyVolume3DEdgeMagnitudeStrategy(CupyEdgeMagnitudeStrategy):
    method = EdgeMagnitudeMethod.VOLUME_3D

    def apply(
        self, image: "cp.ndarray", *, mode: SobelKernelBoundaryMode, cval: float
    ) -> "cp.ndarray":
        return _sobel_3d_voxel(image, mode=mode.value, cval=cval)


@cupy_func
def edge_magnitude(
    image: "cp.ndarray",
    method: EdgeMagnitudeMethod = EdgeMagnitudeMethod.SLICE_2D,
    mode: SobelKernelBoundaryMode = SobelKernelBoundaryMode.REFLECT,
    cval: float = 0.0,
) -> "cp.ndarray":
    """
    Compute edge magnitude using specified method - GPU PARALLELIZED.

    This dispatcher function provides a unified interface for different Sobel
    approaches, following the pattern of create_projection.

    Args:
        image: 3D CuPy array of shape (Z, Y, X)
        method: Edge detection method
            - "2d": 2D Sobel applied to each slice independently (slice-wise)
            - "3d": True 3D voxel Sobel including Z-axis gradients (volumetric)
        mode: Boundary handling mode ('constant', 'reflect', 'nearest', 'wrap', 'mirror')
        cval: Constant value for 'constant' mode

    Returns:
        Edge magnitude as 3D CuPy array of shape (Z, Y, X)
    """
    operations.require_stack(OPERATIONS, image)

    return CupyEdgeMagnitudeStrategy.for_enum_member(method).apply(
        image, mode=mode, cval=cval
    )


@artifact_inputs(
    ArtifactSpec.input(
        "mask",
        ImageArtifactType,
        required=False,
        parameter_name="mask",
    )
)
@cupy_func
def sobel(
    image: "cp.ndarray",
    mask: Optional["cp.ndarray"] = None,
    *,
    axis: Optional[int] = None,
    mode: ScipyBoundaryMode = ScipyBoundaryMode.REFLECT,
    cval: float = 0.0,
) -> "cp.ndarray":
    """
    Find edges in an image using the Sobel filter (CuCIM backend).

    This function wraps CuCIM's sobel filter to provide a manual, pickleable
    sobel function with full OpenHCS features (slice_by_slice, dtype_config, etc.).

    The @cupy_func decorator automatically provides slice_by_slice processing,
    so this function can handle both 2D and 3D inputs depending on the setting.

    Args:
        image: CuPy array (2D when slice_by_slice=True, 3D when slice_by_slice=False)
        mask: Optional mask array to clip the output (values where mask=0 will be set to 0)
        axis: Compute the edge filter along this axis. If not provided, edge magnitude is computed
        mode: Boundary handling mode ('reflect', 'constant', 'nearest', 'wrap')
        cval: Constant value for 'constant' mode

    Returns:
        Edge-filtered CuPy array (same shape and dtype as input)

    Note:
        This is a manual wrapper around CuCIM's sobel function that provides
        the same functionality as auto-discovered functions but is pickleable
        for subprocess execution.

        CuCIM's sobel normalizes integer inputs to [0, 1] range and returns float64.
        This wrapper always preserves the input dtype by forcing dtype conversion.
    """
    from cucim.skimage import filters as cucim_filters

    # Store original dtype
    original_dtype = image.dtype

    # Call CuCIM sobel
    result = cucim_filters.sobel(
        image, mask=mask, axis=axis, mode=mode.value, cval=cval
    )

    # Always preserve input dtype (CuCIM normalizes integer inputs to [0, 1])
    if result.dtype != original_dtype:
        result = MemoryType.CUPY.scale_dtype(result, original_dtype)

    return result
