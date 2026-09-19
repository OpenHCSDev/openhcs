"""CellProfiler-compatible edge enhancement backend semantics."""

from __future__ import annotations
from openhcs.interop.cellprofiler.settings_binder import SettingToKeywordBinding
from openhcs.interop.cellprofiler.module_declarations import (
    CellProfilerModule,
)
from openhcs.core.artifacts import ImageArtifactType


class EnhanceEdgesModule(CellProfilerModule):
    module_name = "EnhanceEdges"
    function_name = "enhance_edges"
    validated = True
    confidence = 1.0
    input_image_setting = "Select the input image"
    output_image_setting = "Name the output image"
    setting_bindings: ClassVar[tuple[SettingToKeywordBinding, ...]] = (
        SettingToKeywordBinding.input(input_image_setting, ImageArtifactType),
        SettingToKeywordBinding.output(output_image_setting, ImageArtifactType),
        SettingToKeywordBinding(
            "Automatically calculate the threshold?", "automatic_threshold"
        ),
        SettingToKeywordBinding("Absolute threshold", "manual_threshold"),
        SettingToKeywordBinding(
            "Threshold adjustment factor", "threshold_adjustment_factor"
        ),
        SettingToKeywordBinding("Select an edge-finding method", "method"),
        SettingToKeywordBinding("Select edge direction to enhance", "direction"),
        SettingToKeywordBinding(
            "Calculate Gaussian's sigma automatically?", "automatic_gaussian"
        ),
        SettingToKeywordBinding("Gaussian's sigma value", "sigma"),
        SettingToKeywordBinding(
            "Calculate value for low threshold automatically?",
            "automatic_low_threshold",
        ),
        SettingToKeywordBinding("Low threshold value", "low_threshold"),
    )


from abc import ABC, abstractmethod
from dataclasses import dataclass, replace
from enum import Enum
from typing import ClassVar
import warnings
import numpy as np
from metaclass_registry import AutoRegisterMeta
from numba import njit
from openhcs.core.memory.decorators import numpy as numpy_decorator
from openhcs.core.public_api import public_names_from_objects
from openhcs.core.runtime_image_values import (
    image_payload_data,
    image_payload_mask,
    image_payload_metadata,
    with_image_payload_data,
)
from openhcs.interop.cellprofiler.settings_binder import coerce_cellprofiler_enum
from openhcs.processing.backends.cellprofiler._backend import (
    BackendProviderInput,
    DEFAULT_CELLPROFILER_BACKEND_SELECTION,
    CellProfilerBackendProvider,
    CellProfilerBackendAuthority,
)
from openhcs.processing.backends.cellprofiler.image_geometry import (
    CellProfilerPlaneGeometry,
)
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract


class EdgeMethod(Enum):
    SOBEL = "sobel"
    LOG = "log"
    PREWITT = "prewitt"
    CANNY = "canny"
    ROBERTS = "roberts"
    KIRSCH = "kirsch"

    @property
    def default_backend_provider(self) -> CellProfilerBackendProvider:
        if self is EdgeMethod.SOBEL:
            return CellProfilerBackendProvider.NUMBA
        return CellProfilerBackendProvider.NATIVE


class EdgeDirection(Enum):
    ALL = ("all", True, True)
    HORIZONTAL = ("horizontal", True, False)
    VERTICAL = ("vertical", False, True)

    def __init__(
        self,
        label: str,
        includes_horizontal_response: bool,
        includes_vertical_response: bool,
    ) -> None:
        self._value_ = label
        self._includes_horizontal_response = includes_horizontal_response
        self._includes_vertical_response = includes_vertical_response

    @property
    def includes_horizontal_response(self) -> bool:
        return self._includes_horizontal_response

    @property
    def includes_vertical_response(self) -> bool:
        return self._includes_vertical_response


@dataclass(frozen=True, slots=True)
class EdgeEnhancementStrategyKey:
    backend_provider: CellProfilerBackendProvider
    method: EdgeMethod
    direction: EdgeDirection

    @property
    def label(self) -> str:
        return (
            f"{self.backend_provider.value}:{self.method.value}:{self.direction.value}"
        )


@dataclass(frozen=True, slots=True)
class EdgeEnhancementRequest:
    image: np.ndarray
    mask: np.ndarray
    backend_provider: CellProfilerBackendProvider
    method: EdgeMethod
    direction: EdgeDirection
    automatic_threshold: bool
    automatic_low_threshold: bool
    sigma: float
    low_threshold: float
    manual_threshold: float
    threshold_adjustment_factor: float

    @classmethod
    def build(
        cls,
        *,
        image: np.ndarray,
        mask: np.ndarray,
        method: EdgeMethod,
        direction: EdgeDirection,
        backend_provider: BackendProviderInput = DEFAULT_CELLPROFILER_BACKEND_SELECTION,
        automatic_threshold: bool,
        automatic_low_threshold: bool,
        sigma: float,
        low_threshold: float,
        manual_threshold: float,
        threshold_adjustment_factor: float,
    ) -> "EdgeEnhancementRequest":
        resolved_provider = CellProfilerBackendAuthority.provider_selection(
            backend_provider
        ).provider_or(method.default_backend_provider)
        return cls(
            image=image,
            mask=mask,
            backend_provider=resolved_provider,
            method=method,
            direction=direction,
            automatic_threshold=automatic_threshold,
            automatic_low_threshold=automatic_low_threshold,
            sigma=sigma,
            low_threshold=low_threshold,
            manual_threshold=manual_threshold,
            threshold_adjustment_factor=threshold_adjustment_factor,
        )

    @property
    def strategy_key(self) -> EdgeEnhancementStrategyKey:
        return EdgeEnhancementStrategyKey(
            self.backend_provider, self.method, self.direction
        )

    @property
    def fallback_strategy_key(self) -> EdgeEnhancementStrategyKey:
        return EdgeEnhancementStrategyKey(
            self.backend_provider, self.method, EdgeDirection.ALL
        )


class EdgeEnhancementStrategy(ABC, metaclass=AutoRegisterMeta):
    """Nominal dispatch point for one backend/method/direction edge algorithm."""

    __registry_key__ = "strategy_label"
    __skip_if_no_key__ = True
    strategy_label: ClassVar[str | None] = None
    strategy_key: ClassVar[EdgeEnhancementStrategyKey | None] = None

    @classmethod
    def for_request(cls, request: EdgeEnhancementRequest) -> "EdgeEnhancementStrategy":
        strategy_type = cls.__registry__.get(request.strategy_key.label)
        if strategy_type is None:
            strategy_type = cls.__registry__.get(request.fallback_strategy_key.label)
        if strategy_type is None:
            raise NotImplementedError(
                f"No CellProfiler edge enhancement backend is registered for provider {request.backend_provider.value!r}, method {request.method.value!r}, direction {request.direction.value!r}."
            )
        return strategy_type()

    @abstractmethod
    def enhance(self, request: EdgeEnhancementRequest) -> np.ndarray:
        """Return edge-enhanced pixels for this strategy."""


class EdgeEnhancementStrategyLeaf(EdgeEnhancementStrategy):
    """Declarative base for concrete edge enhancement leaves."""

    backend_provider: ClassVar[CellProfilerBackendProvider | None] = None
    method: ClassVar[EdgeMethod | None] = None
    direction: ClassVar[EdgeDirection | None] = None

    def __init_subclass__(cls, **kwargs: object) -> None:
        super().__init_subclass__(**kwargs)
        if cls.backend_provider is None or cls.method is None or cls.direction is None:
            return
        cls.strategy_key = EdgeEnhancementStrategyKey(
            cls.backend_provider, cls.method, cls.direction
        )
        cls.strategy_label = cls.strategy_key.label


class NumbaSobelStrategy(EdgeEnhancementStrategyLeaf):
    """Shared Numba Sobel implementation for direction-specific leaves."""

    backend_provider = CellProfilerBackendProvider.NUMBA
    method = EdgeMethod.SOBEL

    def enhance(self, request: EdgeEnhancementRequest) -> np.ndarray:
        return _sobel_numba_kernel(
            np.ascontiguousarray(request.image, dtype=np.float32),
            np.ascontiguousarray(request.mask, dtype=np.bool_),
            request.direction.includes_horizontal_response,
            request.direction.includes_vertical_response,
        )


class NumbaSobelAllStrategy(NumbaSobelStrategy):
    direction = EdgeDirection.ALL


class NumbaSobelHorizontalStrategy(NumbaSobelStrategy):
    direction = EdgeDirection.HORIZONTAL


class NumbaSobelVerticalStrategy(NumbaSobelStrategy):
    direction = EdgeDirection.VERTICAL


class NumpySobelAllStrategy(EdgeEnhancementStrategyLeaf):
    backend_provider = CellProfilerBackendProvider.NATIVE
    method = EdgeMethod.SOBEL
    direction = EdgeDirection.ALL

    def enhance(self, request: EdgeEnhancementRequest) -> np.ndarray:
        return _native_directional_edge(request, operator="sobel")


class NumpySobelHorizontalStrategy(EdgeEnhancementStrategyLeaf):
    backend_provider = CellProfilerBackendProvider.NATIVE
    method = EdgeMethod.SOBEL
    direction = EdgeDirection.HORIZONTAL

    def enhance(self, request: EdgeEnhancementRequest) -> np.ndarray:
        return _native_directional_edge(request, operator="sobel")


class NumpySobelVerticalStrategy(EdgeEnhancementStrategyLeaf):
    backend_provider = CellProfilerBackendProvider.NATIVE
    method = EdgeMethod.SOBEL
    direction = EdgeDirection.VERTICAL

    def enhance(self, request: EdgeEnhancementRequest) -> np.ndarray:
        return _native_directional_edge(request, operator="sobel")


class NumpyPrewittAllStrategy(EdgeEnhancementStrategyLeaf):
    backend_provider = CellProfilerBackendProvider.NATIVE
    method = EdgeMethod.PREWITT
    direction = EdgeDirection.ALL

    def enhance(self, request: EdgeEnhancementRequest) -> np.ndarray:
        return _native_directional_edge(request, operator="prewitt")


class NumpyPrewittHorizontalStrategy(EdgeEnhancementStrategyLeaf):
    backend_provider = CellProfilerBackendProvider.NATIVE
    method = EdgeMethod.PREWITT
    direction = EdgeDirection.HORIZONTAL

    def enhance(self, request: EdgeEnhancementRequest) -> np.ndarray:
        return _native_directional_edge(request, operator="prewitt")


class NumpyPrewittVerticalStrategy(EdgeEnhancementStrategyLeaf):
    backend_provider = CellProfilerBackendProvider.NATIVE
    method = EdgeMethod.PREWITT
    direction = EdgeDirection.VERTICAL

    def enhance(self, request: EdgeEnhancementRequest) -> np.ndarray:
        return _native_directional_edge(request, operator="prewitt")


class NumpyLaplacianOfGaussianStrategy(EdgeEnhancementStrategyLeaf):
    backend_provider = CellProfilerBackendProvider.NATIVE
    method = EdgeMethod.LOG
    direction = EdgeDirection.ALL

    def enhance(self, request: EdgeEnhancementRequest) -> np.ndarray:
        size = int(request.sigma * 4) + 1
        return _native_laplacian_of_gaussian(
            request.image, request.mask, size, request.sigma
        )


class NumpyCannyStrategy(EdgeEnhancementStrategyLeaf):
    backend_provider = CellProfilerBackendProvider.NATIVE
    method = EdgeMethod.CANNY
    direction = EdgeDirection.ALL

    def enhance(self, request: EdgeEnhancementRequest) -> np.ndarray:
        low_threshold = request.low_threshold
        high_threshold = request.manual_threshold
        if request.automatic_threshold or request.automatic_low_threshold:
            sobel_request = replace(
                request,
                mask=np.ones(request.image.shape, dtype=bool),
                method=EdgeMethod.SOBEL,
                direction=EdgeDirection.ALL,
            )
            sobel_image = _native_directional_edge(sobel_request, operator="sobel")
            low, high = _native_otsu3(sobel_image[request.mask])
            if request.automatic_threshold:
                high_threshold = high * request.threshold_adjustment_factor
            if request.automatic_low_threshold:
                low_threshold = low * request.threshold_adjustment_factor
        if high_threshold < low_threshold:
            high_threshold = low_threshold
        from skimage.feature import canny

        return canny(
            request.image,
            sigma=request.sigma,
            low_threshold=low_threshold,
            high_threshold=high_threshold,
            mask=request.mask,
            mode="constant",
            cval=0.0,
        )


class NumpyRobertsStrategy(EdgeEnhancementStrategyLeaf):
    backend_provider = CellProfilerBackendProvider.NATIVE
    method = EdgeMethod.ROBERTS
    direction = EdgeDirection.ALL

    def enhance(self, request: EdgeEnhancementRequest) -> np.ndarray:
        return _native_roberts(request.image, request.mask)


class NumpyKirschStrategy(EdgeEnhancementStrategyLeaf):
    backend_provider = CellProfilerBackendProvider.NATIVE
    method = EdgeMethod.KIRSCH
    direction = EdgeDirection.ALL

    def enhance(self, request: EdgeEnhancementRequest) -> np.ndarray:
        return _native_kirsch(request.image)


def _native_directional_edge(
    request: EdgeEnhancementRequest,
    *,
    operator: str,
) -> np.ndarray:
    from skimage import filters

    if operator == "sobel":
        horizontal_filter = filters.sobel_h
        vertical_filter = filters.sobel_v
    else:
        horizontal_filter = filters.prewitt_h
        vertical_filter = filters.prewitt_v
    horizontal = np.abs(horizontal_filter(request.image, mask=request.mask))
    if request.direction is EdgeDirection.HORIZONTAL:
        return horizontal
    vertical = np.abs(vertical_filter(request.image, mask=request.mask))
    if request.direction is EdgeDirection.VERTICAL:
        return vertical
    return np.sqrt(horizontal**2 + vertical**2)


def _native_laplacian_of_gaussian(
    image: np.ndarray,
    mask: np.ndarray,
    size: int,
    sigma: float,
) -> np.ndarray:
    from scipy.ndimage import convolve

    half_size = size // 2
    row, column = np.mgrid[
        -half_size : half_size + 1,
        -half_size : half_size + 1,
    ].astype(float) / float(sigma)
    distance = (row**2 + column**2) / 2
    gaussian = np.exp(-distance)
    gaussian /= np.sum(gaussian)
    kernel = (distance - 1) * gaussian
    kernel -= np.mean(kernel)
    masked_image = image.copy()
    masked_image[~mask] = 0
    output = convolve(masked_image, kernel, mode="constant", cval=0)
    correction = convolve((~mask).astype(float), kernel, mode="constant", cval=1)
    output += correction * image
    output[~mask] = image[~mask]
    return output


def _running_variance(values: np.ndarray) -> np.ndarray:
    means = values.cumsum() / np.arange(1, len(values) + 1)
    accumulated = ((values[1:] - means[:-1]) * (values[1:] - means[1:])).cumsum()
    return np.hstack(([0], accumulated / np.arange(1, len(values))))


def _native_otsu3(values: np.ndarray, bins: int = 128) -> tuple[float, float]:
    data = np.asarray(values).ravel()
    data = np.sort(data[~np.isnan(data)])
    if data.size == 0:
        return 0.0, 0.0
    variance = _running_variance(data)
    reverse_variance = np.flipud(_running_variance(np.flipud(data)))
    bins = min(bins, len(data))
    bin_length = len(data) // bins
    thresholds = data[0 : len(data) : bin_length]
    indexes = np.arange(0, len(data), bin_length)
    low_score = variance[::bin_length] * indexes
    high_score = reverse_variance[::bin_length] * (len(data) - indexes)
    cumulative = data.cumsum()
    cumulative_squared = (data**2).cumsum()
    first, second = np.mgrid[0 : len(low_score), 0 : len(high_score)] * bin_length
    width = (second - first).astype(float)
    with np.errstate(divide="ignore", invalid="ignore"):
        mean = (cumulative[second] - cumulative[first]) / width
        mean_squared = (cumulative_squared[second] - cumulative_squared[first]) / width
    middle_score = width * (mean_squared - mean**2)
    middle_score[first >= second] = np.inf
    score = (
        low_score[first * bins // len(data)]
        + middle_score
        + high_score[second * bins // len(data)]
    )
    best = np.argwhere(score == np.min(score))[0]
    return float(thresholds[best[0]]), float(thresholds[best[1]])


def _native_roberts(image: np.ndarray, mask: np.ndarray) -> np.ndarray:
    from scipy.ndimage import binary_erosion, generate_binary_structure

    result = np.zeros(image.shape)
    valid = binary_erosion(mask, generate_binary_structure(2, 2), border_value=0)
    center = image[valid]
    lower_right = image[1:, 1:][valid[:-1, :-1]]
    upper_right = image[:-1, 1:][valid[1:, :-1]]
    diagonal = center - upper_right
    anti_diagonal = center - lower_right
    result[valid] = np.sqrt(diagonal**2 + anti_diagonal**2)
    return result


def _native_kirsch(image: np.ndarray) -> np.ndarray:
    from scipy.ndimage import convolve

    compass = [5, -3, -3, -3, -3, -3, 5, 5]
    result = np.zeros(image.shape)
    kernel = np.zeros((3, 3), dtype=image.dtype)
    indexes = np.array([[0, 1, 2], [7, -1, 3], [6, 5, 4]])
    perimeter = indexes >= 0
    for _ in range(8):
        kernel[perimeter] = np.asarray(compass)[indexes[perimeter]]
        result = np.maximum(result, convolve(image, kernel))
        compass = compass[-1:] + compass[:-1]
    return result


@numpy_decorator(contract=ProcessingContract.PURE_2D)
def enhance_edges(
    image: np.ndarray,
    method: EdgeMethod = EdgeMethod.SOBEL,
    direction: EdgeDirection = EdgeDirection.ALL,
    edge_backend_provider: BackendProviderInput = DEFAULT_CELLPROFILER_BACKEND_SELECTION,
    automatic_threshold: bool = True,
    automatic_gaussian: bool = True,
    sigma: float = 10.0,
    manual_threshold: float = 0.2,
    threshold_adjustment_factor: float = 1.0,
    automatic_low_threshold: bool = True,
    low_threshold: float = 0.1,
) -> np.ndarray:
    """Enhance edges using CellProfiler-compatible edge detection semantics."""
    if not 0 <= low_threshold <= 1:
        warnings.warn(
            f"low_threshold value of {low_threshold} is outside of the [0-1] range.",
            stacklevel=2,
        )
    pixel_data = np.asarray(image_payload_data(image), dtype=np.float32)
    payload_mask = image_payload_mask(image)
    operation_mask = (
        np.ones(pixel_data.shape[:2], dtype=bool)
        if payload_mask is None
        else CellProfilerPlaneGeometry.from_image_plane(image).binary_mask(
            np.asarray(payload_mask)
        )
    )
    request = EdgeEnhancementRequest.build(
        image=pixel_data,
        mask=operation_mask,
        method=method,
        direction=direction,
        backend_provider=edge_backend_provider,
        automatic_threshold=automatic_threshold,
        automatic_low_threshold=automatic_low_threshold,
        sigma=(
            sigma
            if not automatic_gaussian
            else 1.0 if method is EdgeMethod.CANNY else 2.0
        ),
        low_threshold=low_threshold,
        manual_threshold=manual_threshold,
        threshold_adjustment_factor=threshold_adjustment_factor,
    )
    output = (
        EdgeEnhancementStrategy.for_request(request).enhance(request).astype(np.float32)
    )
    return with_image_payload_data(
        image,
        output,
        mask=operation_mask if payload_mask is not None else None,
        metadata=image_payload_metadata(image).without_unit_interval_intensity_scale(),
    )


@njit(cache=True)
def _sobel_numba_kernel(
    image: np.ndarray,
    mask: np.ndarray,
    include_horizontal: bool,
    include_vertical: bool,
) -> np.ndarray:
    height, width = image.shape
    output = np.zeros((height, width), dtype=np.float32)
    if height < 3 or width < 3:
        return output
    for row in range(1, height - 1):
        for col in range(1, width - 1):
            if not _full_sobel_neighborhood_is_valid(mask, row, col):
                continue
            horizontal = abs(
                (
                    image[row - 1, col - 1]
                    + 2.0 * image[row - 1, col]
                    + image[row - 1, col + 1]
                    - image[row + 1, col - 1]
                    - 2.0 * image[row + 1, col]
                    - image[row + 1, col + 1]
                )
                * 0.25
            )
            vertical = abs(
                (
                    image[row - 1, col - 1]
                    + 2.0 * image[row, col - 1]
                    + image[row + 1, col - 1]
                    - image[row - 1, col + 1]
                    - 2.0 * image[row, col + 1]
                    - image[row + 1, col + 1]
                )
                * 0.25
            )
            if include_horizontal and include_vertical:
                output[row, col] = np.sqrt(
                    horizontal * horizontal + vertical * vertical
                )
            elif include_horizontal:
                output[row, col] = horizontal
            elif include_vertical:
                output[row, col] = vertical
    return output


@njit(cache=True)
def _full_sobel_neighborhood_is_valid(mask: np.ndarray, row: int, col: int) -> bool:
    for mask_row in range(row - 1, row + 2):
        for mask_col in range(col - 1, col + 2):
            if not mask[mask_row, mask_col]:
                return False
    return True


__all__ = public_names_from_objects(
    EdgeDirection,
    EdgeEnhancementRequest,
    EdgeEnhancementStrategy,
    EdgeEnhancementStrategyKey,
    EdgeMethod,
    enhance_edges,
)
