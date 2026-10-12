"""NumPy processor registrations.

Shared operations are written once in ``image_stack_operations``; this module
registers them for NumPy and holds the operations whose NumPy algorithm
(scikit-image, the numba composite kernel) differs from other backends.
"""

from __future__ import annotations

from enum import Enum
from typing import Annotated, List, Optional, Tuple

from arraybridge import MemoryType
from metaclass_registry import AutoRegisterMeta
import numpy as np
from numba import njit
from skimage import exposure, filters
from skimage import morphology as morph
from skimage import transform as trans

from openhcs.core.artifacts.specs import ArtifactSpec
from openhcs.core.artifacts.kinds import ImageArtifactType
from openhcs.core.memory import numpy as numpy_func
from openhcs.core.pipeline.function_contracts import artifact_inputs
from openhcs.core.processing_preparation import RegisteredNumbaKernelPreparation
from openhcs.processing.backends.processors import image_stack_operations as operations
from openhcs.processing.backends.processors.method_axes import (
    OrthogonalProjectionPlane,
    SpatialBinMethod,
)
from openhcs.core.processing_contracts import (
    Pure2DContract,
    VolumetricToSliceContract,
)

OPERATIONS = MemoryType.NUMPY.library


@numpy_func(contract=Pure2DContract)
def non_local_means_denoise_planes(
    image: np.ndarray,
    *,
    patch_size: int = 7,
    patch_distance: int = 11,
    h: float = 0.1,
    fast_mode: bool = True,
    sigma: float = 0.0,
    preserve_range: bool = False,
) -> np.ndarray:
    """Denoise independent grayscale planes with scikit-image non-local means.

    The declared PURE_2D contract slices the original runtime plane axis and
    restores its metadata and provenance. SITE, channel, and physical Z planes
    are filtered independently: no patches or neighbors cross that axis. Use
    the original ``skimage:restoration.denoise_nl_means`` for volumetric NLM.

    A bare ndarray must already be a 2-D plane. This operation never guesses an
    axis or squeezes a volume. Parameters retain scikit-image's definitions and
    defaults; it adds no normalization or calibration. Independent-plane NLM
    does not establish a memory bound for arbitrarily large planes.

    Args:
        patch_size: Side length of patches compared within each plane.
        patch_distance: Maximum search distance within each plane, in pixels.
        h: Cutoff controlling accepted patch intensity differences.
        fast_mode: Use scikit-image's fast NLM implementation.
        sigma: Known noise standard deviation in the input intensity units.
        preserve_range: Preserve input intensity range instead of scikit-image's
            dtype-dependent conversion to floating-point image range.

    Returns:
        Denoised plane, with the dtype and intensity semantics of scikit-image.
    """
    from skimage.restoration import denoise_nl_means

    if image.ndim != 2:
        raise ValueError(
            "Plane NLM requires a 2-D grayscale plane or a runtime payload "
            f"with a declared plane axis; received shape {image.shape}."
        )
    return denoise_nl_means(
        image,
        patch_size=patch_size,
        patch_distance=patch_distance,
        h=h,
        fast_mode=fast_mode,
        sigma=sigma,
        preserve_range=preserve_range,
        channel_axis=None,
    )


PercentileLowerEndpointInput = Annotated[
    float,
    "Percentile used as the input-range lower endpoint (0 to 100).",
]
PercentileUpperEndpointInput = Annotated[
    float,
    "Percentile used as the input-range upper endpoint (0 to 100).",
]
NormalizationTargetMinimumInput = Annotated[
    float,
    "Output intensity assigned to the normalized range's lower endpoint.",
]
NormalizationTargetMaximumInput = Annotated[
    float,
    "Output intensity assigned to the normalized range's upper endpoint.",
]
SpatialBinMethodInput = Annotated[
    SpatialBinMethod,
    "Reduction operation applied to the pixels or voxels within each spatial bin.",
]


@numpy_func
def create_linear_weight_mask(
    height: int, width: int, margin_ratio: float = 0.1
) -> np.ndarray:
    """
    Create a 2D weight mask that linearly ramps from 0 at the edges to 1 in the center.

    Args:
        height: Height of the mask
        width: Width of the mask
        margin_ratio: Ratio of the margin to the image size

    Returns:
        2D weight mask of shape (height, width)
    """
    return operations.linear_weight_mask(
        OPERATIONS, height, width, margin_ratio, ramp_endpoint=False
    )


@numpy_func
def sharpen(image: np.ndarray, radius: float = 1.0, amount: float = 1.0) -> np.ndarray:
    """
    Sharpen a 3D image using unsharp masking.

    This applies sharpening to each Z-slice independently.

    Args:
        radius: Radius of Gaussian blur
        amount: Sharpening strength

    Returns:
        Sharpened 3D NumPy array of shape (Z, Y, X)
    """
    operations.require_stack(OPERATIONS, image)

    # Store original dtype
    dtype = image.dtype

    # Process each Z-slice independently
    result = np.zeros_like(image, dtype=np.float32)

    for z in range(image.shape[0]):
        # Convert to float for processing
        slice_float = image[z].astype(np.float32) / np.max(image[z])

        # Create blurred version for unsharp mask
        blurred = filters.gaussian(slice_float, sigma=radius)

        # Apply unsharp mask: original + amount * (original - blurred)
        sharpened = slice_float + amount * (slice_float - blurred)

        # Clip to valid range
        sharpened = np.clip(sharpened, 0, 1.0)

        # Scale back to original range
        sharpened = exposure.rescale_intensity(
            sharpened, in_range="image", out_range=(0, 65535)
        )
        result[z] = sharpened

    # Convert back to original dtype
    return result.astype(dtype)


@numpy_func
def percentile_normalize(
    image: np.ndarray,
    low_percentile: PercentileLowerEndpointInput = 1.0,
    high_percentile: PercentileUpperEndpointInput = 99.0,
    target_min: NormalizationTargetMinimumInput = 0.0,
    target_max: NormalizationTargetMaximumInput = 65535.0,
) -> np.ndarray:
    """
    Normalize each plane independently using percentile-based contrast stretching.

    The first transported array axis is the declared plane axis, which may be
    Z, channel, time, or another ``variable_components`` axis. Each plane gets
    its own percentile endpoints.

    Use when:
        Per-plane contrast must be made comparable for visualization or a
        downstream segmentation operation.
    Avoid when:
        Absolute intensity or intensity differences between planes are the
        measurement of interest; independent scaling removes those differences.
    Validate:
        Inspect representative raw/normalized pairs for clipping, amplified
        noise, and loss of dim structures before using the result downstream.

    Returns:
        Normalized 3D NumPy array of shape (N, Y, X).
    """
    return operations.percentile_normalize_planes(
        OPERATIONS, image, low_percentile, high_percentile, target_min, target_max
    )


@numpy_func
def percentile_normalize_plane(
    image: np.ndarray,
    plane_index: int = 0,
    low_percentile: PercentileLowerEndpointInput = 1.0,
    high_percentile: PercentileUpperEndpointInput = 99.0,
    target_min: NormalizationTargetMinimumInput = 0.0,
    target_max: NormalizationTargetMaximumInput = 65535.0,
) -> np.ndarray:
    """Normalize one declared leading-axis plane and preserve every other plane.

    Use this when one process channel needs contrast normalization but another
    plane in the same transported stack supplies reference semantics such as a
    nuclear stain, calibration image, or mask. The returned array is a copy;
    every unselected plane remains byte-for-byte identical to the input.

    Validate:
        Compare the selected plane before and after normalization, and prove
        array equality for every unselected reference plane.

    Args:
        plane_index: Leading-axis plane to normalize; zero selects the first plane.
    """

    operations.require_stack(OPERATIONS, image)
    if not 0 <= plane_index < image.shape[0]:
        raise ValueError("plane_index is outside the input stack")

    normalized = np.asarray(image).copy()
    normalized[plane_index : plane_index + 1] = percentile_normalize(
        image[plane_index : plane_index + 1],
        low_percentile=low_percentile,
        high_percentile=high_percentile,
        target_min=target_min,
        target_max=target_max,
    )
    return normalized


@numpy_func
def stack_percentile_normalize(
    stack: np.ndarray,
    low_percentile: PercentileLowerEndpointInput = 1.0,
    high_percentile: PercentileUpperEndpointInput = 99.0,
    target_min: NormalizationTargetMinimumInput = 0.0,
    target_max: NormalizationTargetMaximumInput = 65535.0,
) -> np.ndarray:
    """
    Normalize a stack using global percentile-based contrast stretching.

    One percentile pair is computed over every plane on the declared leading
    array axis, so relative intensities between unclipped pixels are preserved
    within this input stack. That axis may represent Z, channel, time, or another
    ``variable_components`` selection.

    Use when:
        A shared robust display or segmentation scale is needed across the
        planes assembled for one invocation.
    Avoid when:
        Independently fitted stacks must retain absolute intensity differences
        across wells, sites, or experimental conditions. Global percentile
        scaling still clips endpoint values and changes quantitative intensity.
    Validate:
        Compare raw and normalized plane histograms, the fraction clipped at
        each endpoint, and representative dim and bright structures.

    Returns:
        Normalized 3D NumPy array of shape (N, Y, X).
    """
    return operations.percentile_normalize_stack(
        OPERATIONS, stack, low_percentile, high_percentile, target_min, target_max
    )


@njit(cache=True)
def _weighted_projection_numba(values, indices, weights, output, cast):
    for coordinate in np.ndindex(output.shape):
        total = cast(0)
        for index in range(len(indices)):
            product = cast(values[(indices[index],) + coordinate]) * weights[index]
            total = cast(total + product)
        output[coordinate] = total


def _indexed_weighted_projection(
    values: np.ndarray,
    indices: np.ndarray,
    weights: np.ndarray,
    *,
    axis: int,
    preserve_numpy_sum_order: bool = False,
) -> np.ndarray:
    """Reduce selected channels without materializing their weighted image cube.

    Weights declare arithmetic precision. Float32 rounds each source value
    before multiplication, as create_composite historically does. Float64
    matches ColorToGray's explicit multiply/add recipe. The original NumPy
    reduction remains authoritative for its fast-axis pairwise ordering and
    numeric domains unsupported by the real-valued kernel.
    """
    members = np.moveaxis(values, axis, 0)
    if len(indices) != len(weights):
        raise ValueError("Selected channels and weights must have equal lengths")
    count = members.shape[0]
    if np.any(indices < -count) or np.any(indices >= count):
        raise IndexError("Selected channel index is outside the image domain")
    selected = np.where(indices < 0, indices + count, indices).astype(np.int64)
    dtype = weights.dtype
    # Registry preparation covers this entire accelerated signature domain.
    # Other numeric domains retain the original recipe without cold JIT work.
    supported = values.dtype in (np.dtype(np.float32), np.dtype(np.float64))
    supported = supported and values.ndim in (3, 4)
    output_size = int(np.prod(members.shape[1:], dtype=np.int64))
    # Composite's historical cast/multiply uses NumPy's K-order allocation;
    # only its ordinary C-order, non-fast-axis reduction is a sequential sum.
    pairwise = output_size == 1 or (
        preserve_numpy_sum_order and not values.flags.c_contiguous
    )
    if (
        not supported or pairwise
        or dtype not in (np.dtype(np.float32), np.dtype(np.float64))
    ):
        if preserve_numpy_sum_order:
            converted = members.astype(dtype)
            factors = weights.reshape((len(weights),) + (1,) * (members.ndim - 1))
            selected_members = (
                converted if np.array_equal(selected, np.arange(count))
                else converted[selected]
            )
            return np.sum(selected_members * factors, axis=0)
        if output_size == 1:
            factors = weights.reshape((len(weights),) + (1,) * (members.ndim - 1))
            return np.sum(members[selected] * factors, axis=0)
        result = np.zeros(members.shape[1:], dtype=np.result_type(values.dtype, dtype))
        product = np.empty_like(result)
        for channel, weight in zip(selected, weights, strict=True):
            np.multiply(members[channel], weight, dtype=result.dtype, out=product)
            np.add(result, product, out=result)
        return result
    result = np.empty(members.shape[1:], dtype=dtype)
    _weighted_projection_numba(members, selected, weights, result, dtype.type)
    return result


class NumpyWeightedProjectionKernelPreparation(
    RegisteredNumbaKernelPreparation, metaclass=AutoRegisterMeta
):
    """Prepare shared numerical projection signatures during registry warmup."""

    def execute(self) -> None:
        indices = np.arange(3, dtype=np.int64)
        for dtype in (np.float32, np.float64):
            weights = np.full(3, 1 / 3, dtype=dtype)
            for source_dtype in (np.float32, np.float64):
                for shape in ((3, 2, 2), (3, 2, 2, 2)):
                    values = np.ones(shape, dtype=source_dtype)
                    strided = np.moveaxis(
                        np.moveaxis(values, 0, -1).copy(), -1, 0,
                    )
                    for members in (values, np.asfortranarray(values), strided):
                        for writable in (True, False):
                            members.flags.writeable = writable
                            _indexed_weighted_projection(members, indices, weights, axis=0)


@numpy_func(contract=VolumetricToSliceContract)
def create_composite(
    stack: np.ndarray, weights: Optional[List[float]] = None
) -> np.ndarray:
    """
    Create a composite image from a 3D stack where each slice is a channel.

    Args:
        stack: 3D NumPy array of shape (N, Y, X) where N is number of channel slices
        weights: List of weights for each slice. If None, equal weights are used.

    Returns:
        Composite 2D NumPy array of shape (Y, X). OpenHCS contract execution
        restores the singleton runtime stack axis.
    """
    operations.require_stack(OPERATIONS, stack)
    n_slices = stack.shape[0]
    normalized_weights = operations.composite_weights(weights, n_slices)

    # Convert weights to NumPy array for efficient computation
    # CRITICAL: Use float32 for weights to preserve fractional values, not stack.dtype
    weights_array = np.array(normalized_weights, dtype=np.float32)

    composite_slice = _indexed_weighted_projection(
        stack, np.arange(n_slices, dtype=np.int64), weights_array,
        axis=0, preserve_numpy_sum_order=True,
    )

    # Convert back to original dtype
    composite_slice = composite_slice.astype(stack.dtype)

    return composite_slice


@artifact_inputs(ArtifactSpec.input("mask", ImageArtifactType, parameter_name="mask"))
@numpy_func
def apply_mask(image: np.ndarray, mask: np.ndarray) -> np.ndarray:
    """
    Apply a mask to a 3D image.

    This applies the mask to each Z-slice independently if mask is 2D,
    or applies the 3D mask directly if mask is 3D.

    Args:
        mask: 3D NumPy array of shape (Z, Y, X) or 2D NumPy array of shape (Y, X)

    Returns:
        Masked 3D NumPy array of shape (Z, Y, X)
    """
    return operations.apply_mask(OPERATIONS, image, mask)


@numpy_func
def create_weight_mask(shape: Tuple[int, int], margin_ratio: float = 0.1) -> np.ndarray:
    """
    Create a weight mask for blending images.

    Args:
        shape: Shape of the mask (height, width)
        margin_ratio: Ratio of image size to use as margin

    Returns:
        2D NumPy weight mask of shape (Y, X)
    """
    return create_linear_weight_mask(*operations.weight_mask_extent(shape), margin_ratio)


@numpy_func
def max_projection(stack: np.ndarray) -> np.ndarray:
    """
    Create a maximum intensity projection from a Z-stack.

    Returns:
        3D NumPy array of shape (1, Y, X)
    """
    return operations.max_projection(OPERATIONS, stack)


@numpy_func
def mean_projection(stack: np.ndarray) -> np.ndarray:
    """
    Create a mean intensity projection from a Z-stack.

    Returns:
        3D NumPy array of shape (1, Y, X)
    """
    return operations.mean_projection(OPERATIONS, stack)


class NumpyStackProjectionMethod(Enum):
    """NumPy ``create_projection`` choices; values name ``StackProjection`` members.

    Kept as its own class because saved pipelines import it from this module.
    """

    MAX = "max_projection"
    MEAN = "mean_projection"
    MIN = "min_projection"


@numpy_func
def create_orthogonal_projections(
    stack: np.ndarray,
    projections: Tuple[OrthogonalProjectionPlane, ...] = (
        OrthogonalProjectionPlane.XY,
        OrthogonalProjectionPlane.XZ,
        OrthogonalProjectionPlane.YZ,
    ),
) -> dict:
    """
    Create orthogonal max projections from a Z-stack.

    Args:
        projections: Tuple of projection types to create. Options: "xy", "xz", "yz"

    Returns:
        Dict of 2D NumPy arrays, keyed by projection type:
        - "xy": (Y, X) - max along Z axis (top-down view)
        - "xz": (Z, X) - max along Y axis (side view)
        - "yz": (Z, Y) - max along X axis (side view)

    Invariants:
        - Pure function: same input → same output
        - No external dependencies beyond numpy
        - Returns data, never performs I/O
        - Testable in isolation
    """
    operations.require_stack(OPERATIONS, stack)

    result = {}
    if OrthogonalProjectionPlane.XY in projections:
        result[OrthogonalProjectionPlane.XY.value] = stack.max(axis=0)
    if OrthogonalProjectionPlane.XZ in projections:
        result[OrthogonalProjectionPlane.XZ.value] = stack.max(axis=1)
    if OrthogonalProjectionPlane.YZ in projections:
        result[OrthogonalProjectionPlane.YZ.value] = stack.max(axis=2)
    return result


@numpy_func
def gaussian_blur(stack: np.ndarray, sigma: float = 1.0) -> np.ndarray:
    """
    Apply Gaussian blur to reduce noise in image stack.

    Args:
        sigma: Standard deviation for Gaussian kernel (higher = more blur)

    Returns:
        Blurred 3D NumPy array of shape (Z, Y, X)
    """
    operations.require_stack(OPERATIONS, stack)

    # Apply Gaussian blur slice-by-slice
    blurred = np.zeros_like(stack, dtype=np.float64)
    for z in range(stack.shape[0]):
        blurred[z] = filters.gaussian(stack[z], sigma=sigma, preserve_range=True)

    return blurred.astype(stack.dtype)


@numpy_func
def spatial_bin_2d(
    stack: np.ndarray,
    bin_size: int = 2,
    method: SpatialBinMethodInput = SpatialBinMethod.MEAN,
) -> np.ndarray:
    """
    Apply 2D spatial binning to each slice in the stack.

    Reduces spatial resolution by combining neighboring pixels in 2D blocks.
    Each slice is processed independently.

    Args:
        bin_size: Size of the square binning kernel (e.g., 2 = 2x2 binning)

    Returns:
        Binned 3D NumPy array of shape (Z, Y//bin_size, X//bin_size)
    """
    return operations.spatial_bin_2d(OPERATIONS, stack, bin_size, method)


@numpy_func
def spatial_bin_3d(
    stack: np.ndarray,
    bin_size: int = 2,
    method: SpatialBinMethodInput = SpatialBinMethod.MEAN,
) -> np.ndarray:
    """
    Apply 3D spatial binning to the entire stack.

    Reduces spatial resolution by combining neighboring voxels in 3D blocks.

    Args:
        bin_size: Size of the cubic binning kernel (e.g., 2 = 2x2x2 binning)

    Returns:
        Binned 3D NumPy array of shape (Z//bin_size, Y//bin_size, X//bin_size)
    """
    return operations.spatial_bin_3d(OPERATIONS, stack, bin_size, method)


@numpy_func
def stack_equalize_histogram(
    stack: np.ndarray,
    bins: int = 65536,
    range_min: float = 0.0,
    range_max: float = 65535.0,
) -> np.ndarray:
    """
    Apply histogram equalization to an entire stack.

    This ensures consistent contrast enhancement across all Z-slices by
    computing a global histogram across the entire stack.

    Args:
        bins: Number of bins for histogram computation
        range_min: Minimum value for histogram range
        range_max: Maximum value for histogram range

    Returns:
        Equalized 3D NumPy array of shape (Z, Y, X)
    """
    return operations.stack_equalize_histogram(
        OPERATIONS, stack, bins, range_min, range_max
    )


@numpy_func(contract=VolumetricToSliceContract)
def create_projection(
    stack: np.ndarray,
    method: NumpyStackProjectionMethod = NumpyStackProjectionMethod.MAX,
) -> np.ndarray:
    """
    Create a projection from a stack using the specified method.

    Args:
        method: Projection method served by ``image_stack_operations.StackProjection``.

    Returns:
        2D NumPy array of shape (Y, X)
    """
    return operations.create_projection(OPERATIONS, np.asarray(stack), method)[0]


@numpy_func
def crop(
    input_image: np.ndarray,
    start_x: int = 0,
    start_y: int = 0,
    start_z: int = 0,
    width: int = 1,
    height: int = 1,
    depth: int = 1,
) -> np.ndarray:
    """
    Crop a given substack out of a given image stack.

    Equivalent to pyclesperanto.crop() but using NumPy operations.

    Parameters
    ----------
    input_image: np.ndarray
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
    np.ndarray
        Cropped 3D array of shape (depth, height, width)
    """
    return operations.crop(
        OPERATIONS, input_image, start_x, start_y, start_z, width, height, depth
    )


@numpy_func
def tophat(
    image: np.ndarray,
    selem_radius: int = 50,
    downsample_factor: int = 4,
    downsample_anti_aliasing: bool = True,
    upsample_order: int = 0,
) -> np.ndarray:
    """
    Apply white top-hat background subtraction to each image plane.

    Each plane on the declared leading array axis is processed independently.
    The structuring-element radius sets the foreground/background size boundary
    in full-resolution pixels; downsampling approximates that operation faster.

    Use when:
        Bright foreground structures are smaller than the chosen radius and
        sit on uneven, slowly varying background.
    Avoid when:
        Desired structures approach or exceed the radius, background contains
        sharp spatial changes, or corrected pixels will be treated as
        unaltered quantitative intensity measurements.
    Validate:
        Inspect raw/corrected overlays across plate positions for halos, erased
        broad structures, residual background, and changed object intensities.

    Args:
        selem_radius: Approximate foreground/background size boundary in
            full-resolution pixels.
        downsample_factor: Spatial reduction factor used while estimating the
            background; larger values are faster but less spatially precise.
        downsample_anti_aliasing: Apply anti-aliasing before the reduced-scale
            background estimate.
        upsample_order: Interpolation order for restoring the estimated
            background (0=nearest, 1=linear, and so on).

    Returns:
        Background-subtracted 3D NumPy array of shape (N, Y, X).
    """
    operations.require_stack(OPERATIONS, image)

    # Process each Z-slice independently
    result = np.zeros_like(image)

    for z in range(image.shape[0]):
        # Store original data type
        input_dtype = image[z].dtype

        # 1) Downsample
        image_small = trans.resize(
            image[z],
            (
                image[z].shape[0] // downsample_factor,
                image[z].shape[1] // downsample_factor,
            ),
            anti_aliasing=downsample_anti_aliasing,
            preserve_range=True,
        )

        # 2) Build structuring element for the smaller image
        selem_small = morph.disk(selem_radius // downsample_factor)

        # 3) White top-hat on the smaller image
        tophat_small = morph.white_tophat(image_small, selem_small)

        # 4) Upscale background to original size
        background_small = image_small - tophat_small
        background_large = trans.resize(
            background_small, image[z].shape, order=upsample_order, preserve_range=True
        )

        # 5) Subtract background and clip negative values
        slice_result = np.maximum(image[z] - background_large, 0)

        # 6) Convert back to original data type
        result[z] = slice_result.astype(input_dtype)

    return result
