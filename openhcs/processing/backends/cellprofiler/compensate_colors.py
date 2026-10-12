"""CellProfiler plugin CompensateColors.

Upstream: CellProfiler-plugins ``active_plugins/compensatecolors.py``.
"""

from __future__ import annotations

import warnings
from abc import ABC, abstractmethod
from collections.abc import Mapping
from dataclasses import dataclass
from typing import TYPE_CHECKING, ClassVar

import numpy as np

from openhcs.core.aligned_image_payload import (
    AlignedImageStack,
    pack_aligned_image_outputs,
)
from openhcs.core.artifacts.kinds import ImageArtifactType, ObjectLabelsArtifactType
from openhcs.core.artifacts.relations import (
    ArtifactSpecRelation,
    GroupLineageSourceRelation,
)
from openhcs.core.artifacts.specs import ArtifactSpecCollection
from openhcs.core.memory.decorators import numpy
from openhcs.core.pipeline.function_contracts import (
    composed_image_payload,
    special_inputs,
)
from openhcs.core.processing_contracts import FlexibleContract
from openhcs.core.runtime_image_values import ImagePayload
from openhcs.core.runtime_object_labels import (
    ObjectLabelValue,
    object_label_dense_array,
)
from openhcs.core.runtime_plane_projection import RuntimeSliceInvariantValue
from openhcs.interop.cellprofiler.module_artifact_declarations import (
    ObjectArtifactInputModule,
)
from openhcs.interop.cellprofiler.module_settings import BoundModuleSettings
from openhcs.interop.cellprofiler.parser import ModuleSetting
from openhcs.interop.cellprofiler.runtime.object_input_policies import (
    SingleObjectLabelInputPolicy,
)
from openhcs.interop.cellprofiler.setting_names import (
    required_setting_value,
    setting_names,
    setting_values,
)
from openhcs.interop.cellprofiler.settings_binder import (
    SettingToKeywordBinding,
    parse_cellprofiler_bool,
    parse_cellprofiler_float,
    parse_cellprofiler_int,
)

if TYPE_CHECKING:
    from openhcs.core.function_patterns import FunctionInvocationKey
    from openhcs.interop.cellprofiler.parser import ModuleBlock
    from openhcs.interop.cellprofiler.settings_binder import (
        CellProfilerSettingValue,
        SettingsBinder,
    )

_PLUGIN_FAILS = "the CellProfiler plugin fails"
_SIXTEEN_BIT = 65535

_WHERE_SETTING = "Select where to perform color compensation"
_WITHIN_OBJECTS = "Within objects"
_ENTIRE_IMAGE = "Across entire image"
_OBJECTS_SETTING = "Select an object to perform compensation within"
_RESCALE_AFTER_MASKING_SETTING = (
    "Should images be rescaled 0-1 before compensating but after masking to objects?"
)
_MATCHING_SETTING = "Should histogram matching be performed between the image groups?"
_TEMPLATE_CLASS_SETTING = (
    "What compensation class should serve as the template histogram?"
)


def _refuse(reason: str) -> ValueError:
    return ValueError(f"CompensateColors cannot run: {reason}; {_PLUGIN_FAILS} here.")


def _stretched(
    pixels: np.ndarray, low: float, high: float, new_low: float, new_high: float
) -> np.ndarray:
    """Map ``low..high`` linearly onto ``new_low..new_high``, clipping outside.

    scikit-image 0.18's ``rescale_intensity``: the arithmetic is done in the
    type of ``pixels`` and the result is double precision. Later versions keep
    single precision, which changes the 16-bit rounding that follows.
    """
    low, high = float(low), float(high)
    clipped = np.clip(pixels, low, high)
    if low == high:
        return np.clip(clipped, new_low, new_high).astype(np.float64)
    return np.asarray(
        (clipped - low) / (high - low) * (new_high - new_low) + new_low,
        dtype=np.float64,
    )


def _matched_to(pixels: np.ndarray, template: np.ndarray) -> np.ndarray:
    """Give ``pixels`` the cumulative histogram of ``template``.

    scikit-image 0.18's ``match_histograms``, whose result is double precision
    whatever the input.
    """
    _, positions, counts = np.unique(
        pixels, return_inverse=True, return_counts=True
    )
    template_values, template_counts = np.unique(template, return_counts=True)
    quantiles = np.cumsum(counts) / pixels.size
    template_quantiles = np.cumsum(template_counts) / template.size
    return np.interp(quantiles, template_quantiles, template_values)[positions]


class _Region(ABC):
    """Where the compensation is computed."""

    @abstractmethod
    def object_mask(self, needed_for: str) -> np.ndarray:
        """1 inside the objects and 0 outside, flattened."""

    @abstractmethod
    def masked(self, pixels: np.ndarray, image_count: int) -> np.ndarray:
        """A class's pixels (``image_count`` images, flattened) within the region."""


class _EntireImage(_Region):
    def object_mask(self, needed_for: str) -> np.ndarray:
        raise _refuse(f"{needed_for} needs objects to compensate within")

    def masked(self, pixels: np.ndarray, image_count: int) -> np.ndarray:
        return pixels


@dataclass(frozen=True, slots=True)
class _WithinObjects(_Region):
    mask: np.ndarray

    def object_mask(self, needed_for: str) -> np.ndarray:
        return self.mask

    def masked(self, pixels: np.ndarray, image_count: int) -> np.ndarray:
        inside = pixels * np.tile(self.mask, image_count)
        # Outside the objects, and where a pixel is 0, the value is 1.
        return np.where(inside == 0, 1, inside)


class RescaleAfterMasking(RuntimeSliceInvariantValue, ABC):
    """Whether intensities are stretched once pixels outside the objects are set aside."""

    choice: ClassVar[str]
    """The wording of this choice in CellProfiler."""

    @abstractmethod
    def image(self, pixels: np.ndarray, region: _Region) -> np.ndarray:
        """One image before it is rounded to 16-bit values."""

    @abstractmethod
    def class_pixels(self, pixels: np.ndarray) -> np.ndarray:
        """The masked 16-bit values of all images of one class."""


@dataclass(frozen=True, slots=True)
class NoRescaleAfterMasking(RescaleAfterMasking):
    """Intensities are left as they are."""

    choice: ClassVar[str] = "No"

    def image(self, pixels: np.ndarray, region: _Region) -> np.ndarray:
        return pixels

    def class_pixels(self, pixels: np.ndarray) -> np.ndarray:
        return pixels


@dataclass(frozen=True, slots=True)
class RescaleEachImage(RescaleAfterMasking):
    """Each image's values inside the objects are stretched to the full range.

    Needs objects to compensate within.
    """

    choice: ClassVar[str] = "Yes, per image"

    def image(self, pixels: np.ndarray, region: _Region) -> np.ndarray:
        shape = pixels.shape
        inside = pixels.reshape(-1) * region.object_mask("rescaling each image")
        present = inside[inside != 0]
        if not present.size:
            raise _refuse("an image is 0 everywhere inside the objects")
        return _stretched(
            inside, present.min(), present.max(), 1.0 / _SIXTEEN_BIT, 1.0
        ).reshape(shape)

    def class_pixels(self, pixels: np.ndarray) -> np.ndarray:
        return pixels


@dataclass(frozen=True, slots=True)
class RescaleEachClass(RescaleAfterMasking):
    """The values of all images of a class are stretched together to the full range.

    The range stretched is that of the 16-bit values above 1.
    """

    choice: ClassVar[str] = "Yes, per group"

    def image(self, pixels: np.ndarray, region: _Region) -> np.ndarray:
        return pixels

    def class_pixels(self, pixels: np.ndarray) -> np.ndarray:
        present = pixels[pixels > 1]
        if not present.size:
            raise _refuse("a class has no 16-bit value above 1 to rescale")
        return _stretched(pixels, present.min(), present.max(), 1, _SIXTEEN_BIT)


_RESCALES_AFTER_MASKING: tuple[type[RescaleAfterMasking], ...] = (
    NoRescaleAfterMasking,
    RescaleEachImage,
    RescaleEachClass,
)


class ClassHistogramMatching(RuntimeSliceInvariantValue, ABC):
    """Whether the classes are given the intensity histogram of one of them."""

    choice: ClassVar[str]
    """The wording of this choice in CellProfiler."""

    @abstractmethod
    def template_class_number(self) -> int:
        """The class number written to CellProfiler's template setting."""

    @abstractmethod
    def template(
        self, class_pixels: Mapping[int, np.ndarray], region: _Region
    ) -> np.ndarray:
        """The values whose histogram is matched, from the classes' 16-bit values."""

    @abstractmethod
    def before_masking(
        self, number: int, pixels: np.ndarray, template: np.ndarray
    ) -> np.ndarray:
        """The 16-bit values of class ``number`` before the region masks them."""

    @abstractmethod
    def after_masking(
        self, number: int, pixels: np.ndarray, template: np.ndarray
    ) -> np.ndarray:
        """The 16-bit values of class ``number`` once masked and rescaled."""


@dataclass(frozen=True, slots=True)
class NoClassHistogramMatching(ClassHistogramMatching):
    """Each class keeps its own histogram."""

    choice: ClassVar[str] = "No"

    def template_class_number(self) -> int:
        # The plugin's value of the setting it does not show.
        return 1

    def template(
        self, class_pixels: Mapping[int, np.ndarray], region: _Region
    ) -> np.ndarray:
        return np.empty(0)

    def before_masking(
        self, number: int, pixels: np.ndarray, template: np.ndarray
    ) -> np.ndarray:
        return pixels

    def after_masking(
        self, number: int, pixels: np.ndarray, template: np.ndarray
    ) -> np.ndarray:
        return pixels


@dataclass(frozen=True, slots=True)
class _TemplateClassMatching(ClassHistogramMatching, ABC):
    """Every other class is given the histogram of ``template_class``."""

    template_class: int = 1
    """Number of the class whose histogram the other classes are given."""

    def template_class_number(self) -> int:
        return self.template_class

    def _template_class_pixels(
        self, class_pixels: Mapping[int, np.ndarray]
    ) -> np.ndarray:
        if self.template_class not in class_pixels:
            raise _refuse(
                f"no image belongs to the template class {self.template_class}"
            )
        return class_pixels[self.template_class]

    def _matched(
        self, number: int, pixels: np.ndarray, template: np.ndarray
    ) -> np.ndarray:
        if number == self.template_class:
            return pixels
        return _matched_to(pixels, template)


@dataclass(frozen=True, slots=True)
class MatchBeforeMasking(_TemplateClassMatching):
    """The classes are matched on whole images, before objects mask them.

    The template is the template class as it is before masking and rescaling.
    """

    choice: ClassVar[str] = "Yes, pre-masking or on unmasked images"

    def template(
        self, class_pixels: Mapping[int, np.ndarray], region: _Region
    ) -> np.ndarray:
        return self._template_class_pixels(class_pixels)

    def before_masking(
        self, number: int, pixels: np.ndarray, template: np.ndarray
    ) -> np.ndarray:
        return self._matched(number, pixels, template)

    def after_masking(
        self, number: int, pixels: np.ndarray, template: np.ndarray
    ) -> np.ndarray:
        return pixels


@dataclass(frozen=True, slots=True)
class MatchAfterMasking(_TemplateClassMatching):
    """The classes are matched on their values inside the objects.

    Needs objects to compensate within. The template is the masked template
    class, not rescaled even where the classes are.
    """

    choice: ClassVar[str] = "Yes, post-masking to objects"

    def template(
        self, class_pixels: Mapping[int, np.ndarray], region: _Region
    ) -> np.ndarray:
        pixels = self._template_class_pixels(class_pixels)
        mask = region.object_mask("histogram matching after masking")
        inside = np.tile(mask, pixels.size // mask.size) * pixels
        return np.where(inside == 0, 1, inside)

    def before_masking(
        self, number: int, pixels: np.ndarray, template: np.ndarray
    ) -> np.ndarray:
        return pixels

    def after_masking(
        self, number: int, pixels: np.ndarray, template: np.ndarray
    ) -> np.ndarray:
        return self._matched(number, pixels, template)


_CLASS_HISTOGRAM_MATCHINGS: tuple[type[_TemplateClassMatching], ...] = (
    MatchBeforeMasking,
    MatchAfterMasking,
)


def _bright_spots(pixels: np.ndarray, sigma: int) -> np.ndarray:
    """The negated Laplacian of Gaussian of the 16-bit image, negatives set to 0."""
    from scipy.ndimage import gaussian_laplace
    from skimage.util import img_as_uint

    try:
        sixteen_bit = img_as_uint(pixels)
    except ValueError as error:
        raise _refuse(
            "the Laplacian of Gaussian filter takes intensities from -1 to 1"
        ) from error
    filtered = -1 * gaussian_laplace(sixteen_bit.astype(float), sigma)
    return np.clip(filtered, 0, _SIXTEEN_BIT) / _SIXTEEN_BIT


def _percentile(values: np.ndarray, percent: float) -> np.float64:
    """The percentile between the two nearest values, as NumPy 1.24 computes it.

    Their difference is taken in the precision of ``values`` and the result is
    double precision; NumPy 2 returns single precision for single precision.
    """
    ordered = np.sort(values, axis=None)
    quantile = np.float64(percent) / 100
    position = ordered.size * quantile + (1 + quantile * -1) - 1
    below = int(np.floor(position))
    lower, upper = ordered[below], ordered[min(below + 1, ordered.size - 1)]
    share = np.float64(position - below)
    if share >= 0.5:
        return np.float64(upper - (upper - lower) * (1 - share))
    return np.float64(lower + (upper - lower) * share)


def _class_divisors(
    planes: tuple[np.ndarray, ...],
    members: Mapping[int, list[int]],
    percent: float,
) -> dict[int, float]:
    """Each class's percentile intensity relative to the smallest of them."""
    levels = {
        number: _percentile(
            np.concatenate([planes[index] for index in indexes]), percent
        )
        for number, indexes in members.items()
    }
    lowest = np.min(list(levels.values()))
    return {number: level / lowest for number, level in levels.items()}


def _unmixed(class_pixels: list[np.ndarray]) -> np.ndarray:
    """Whole 16-bit values of each class with the other classes' share removed."""
    values = np.array(class_pixels)
    by_pixel = values.T
    brightest = by_pixel.argmax(axis=1)
    with warnings.catch_warnings():
        # A class that is nowhere the brightest has no median: see the caller.
        warnings.simplefilter("ignore", RuntimeWarning)
        mixing = np.array(
            [
                np.median(by_pixel[brightest == index], axis=0)
                for index in range(len(class_pixels))
            ]
        ).T
    with np.errstate(divide="ignore", invalid="ignore"):
        mixing = mixing / mixing.sum(axis=0)
        try:
            unmixing = np.linalg.inv(mixing)
        except np.linalg.LinAlgError as error:
            raise _refuse("the classes cannot be told apart") from error
        unmixed = unmixing.dot(values)
    # Not-a-number and infinite values become the most negative whole number
    # (what the plugin's cast gives on x86), which is 0 once clipped.
    return np.where(np.isfinite(unmixed), unmixed, -1).astype(np.int64)


@composed_image_payload
@numpy(contract=FlexibleContract)
@special_inputs("labels")
def compensate_colors(
    image: np.ndarray,
    compensation_classes: tuple[int, ...],
    labels: ObjectLabelValue | None = None,
    within_objects: bool = False,
    rescale_inputs: bool = False,
    rescale_after_masking: RescaleAfterMasking = NoRescaleAfterMasking(),
    histogram_matching: ClassHistogramMatching = NoClassHistogramMatching(),
    rescale_outputs: bool = False,
    divide_by_class_percentile: bool = False,
    class_percentile: float = 99.0,
    tophat_filter: bool = False,
    tophat_radius: int = 3,
    laplacian_of_gaussian_filter: bool = False,
    laplacian_of_gaussian_sigma: int = 1,
    difference_of_gaussians_filter: bool = False,
    difference_of_gaussians_low_sigma: int = 3,
    difference_of_gaussians_high_sigma: int = 5,
) -> ImagePayload | AlignedImageStack:
    """Remove each channel's bleed-through from the images of the other channels.

    For sequencing by synthesis: every image belongs to a class (one class per
    base or dye, with one image per cycle). The pixels where a class is the
    brightest give its typical share in every class; the inverse of these
    shares turns the measured intensities into unmixed ones. One output image
    is made per input image, in the order of the input images.

    The plugin's behaviour is kept, including:

    - Intensities are worked on as 16-bit values (times 65535, rounded) and the
      unmixed values are cut to whole numbers before they are divided by 65535
      and clipped to 0..1.
    - A class's share is the median over the pixels where it is brightest;
      where classes tie, the lowest class number counts as brightest.
    - Within objects every pixel outside them, and every pixel that is 0, is 1
      (of 65535) in all classes. These pixels count for the lowest class
      number, so where objects cover the smaller part of the image that
      class's shares are all equal.
    - Where a class is nowhere the brightest, or the brightest pixels of a
      class have a median of 0 in all classes (the Laplacian of Gaussian filter
      across an entire image, where most pixels become 0), all output images
      are 0.
    - Filters run in the order top-hat, Laplacian of Gaussian, difference of
      Gaussians, each on the result of the one before. The percentile that
      classes are divided by is taken from the unfiltered images.
    - Fails, and is refused here: classes with different numbers of images;
      images of different sizes or volumes; rescaling each image or matching
      histograms after masking without objects; a template class no image
      belongs to; nothing to rescale inside the objects; a low sigma above the
      high sigma; classes that cannot be told apart.

    One difference: the plugin keeps one image per output name, the last it
    makes, so with a name used twice (its default name ``None`` among them) it
    leaves fewer images than it was given. Here every input image needs an
    output name of its own.

    Reproduced from older libraries, whose results differ from the installed
    ones in precision: scikit-image 0.18's intensity rescaling and histogram
    matching, and NumPy 1.24's percentile.

    Args:
        compensation_classes: Class number of each input image, in the order
            of the images. Every class needs the same number of images.
        labels: Objects to compensate within, when ``within_objects`` is set.
        within_objects: Use only the pixels inside the objects; without it the
            entire image is used.
        rescale_inputs: Stretch each (filtered) image to the full range first.
        rescale_after_masking: Stretch intensities once pixels outside the
            objects are set aside: ``NoRescaleAfterMasking``,
            ``RescaleEachImage`` or ``RescaleEachClass``.
        histogram_matching: Give all classes the histogram of one class:
            ``NoClassHistogramMatching``, ``MatchBeforeMasking`` or
            ``MatchAfterMasking``.
        rescale_outputs: Stretch each compensated image to the full range.
        divide_by_class_percentile: Divide each class's images by the class's
            ``class_percentile`` intensity relative to the lowest such
            intensity of all classes.
        class_percentile: Percentile (0.1 to 100) used for that division.
        tophat_filter: Apply a white top-hat filter to each image first.
        tophat_radius: Radius in pixels of the top-hat filter's disk.
        laplacian_of_gaussian_filter: Replace each image by its negated
            Laplacian of Gaussian, which is bright at spots.
        laplacian_of_gaussian_sigma: Sigma in pixels of that filter.
        difference_of_gaussians_filter: Replace each image by the difference
            of two Gaussian blurs of it.
        difference_of_gaussians_low_sigma: Sigma in pixels of the narrow blur.
        difference_of_gaussians_high_sigma: Sigma in pixels of the wide blur
            that is subtracted.
    """
    from scipy.ndimage import gaussian_filter, white_tophat
    from skimage.morphology import disk

    stacked = np.asarray(image)
    planes = (
        (stacked,)
        if len(compensation_classes) == 1
        else tuple(stacked[index] for index in range(stacked.shape[0]))
    )
    if len(planes) != len(compensation_classes):
        raise ValueError(
            f"CompensateColors got {len(planes)} image(s) for "
            f"{len(compensation_classes)} class number(s)."
        )
    shape = planes[0].shape
    if len(shape) != 2:
        raise _refuse("it works on single planes, not on volumes")
    if any(plane.shape != shape for plane in planes):
        raise _refuse("the images differ in size")
    members: dict[int, list[int]] = {}
    for index, number in enumerate(compensation_classes):
        members.setdefault(number, []).append(index)
    if len({len(indexes) for indexes in members.values()}) != 1:
        raise _refuse("the classes have different numbers of images")
    if (
        difference_of_gaussians_filter
        and difference_of_gaussians_high_sigma < difference_of_gaussians_low_sigma
    ):
        raise _refuse("the difference of Gaussians' high sigma is below its low sigma")

    region: _Region
    if within_objects:
        if labels is None:
            raise _refuse("no objects are named to compensate within")
        region = _WithinObjects(
            np.where(object_label_dense_array(labels, dtype=np.int32) > 0, 1, 0)
            .astype(np.int64)
            .reshape(-1)
        )
    else:
        region = _EntireImage()

    with np.errstate(divide="ignore", invalid="ignore"):
        divisors: Mapping[int, float] = (
            _class_divisors(planes, members, class_percentile)
            if divide_by_class_percentile
            else dict.fromkeys(members, 1.0)
        )
        sixteen_bit: list[np.ndarray] = []
        for plane, number in zip(planes, compensation_classes):
            pixels = plane
            if tophat_filter:
                pixels = white_tophat(pixels, footprint=disk(tophat_radius))
            if laplacian_of_gaussian_filter:
                pixels = _bright_spots(pixels, laplacian_of_gaussian_sigma)
            if difference_of_gaussians_filter:
                pixels = gaussian_filter(
                    pixels, difference_of_gaussians_low_sigma, mode="nearest"
                ) - gaussian_filter(
                    pixels, difference_of_gaussians_high_sigma, mode="nearest"
                )
            # The division keeps the image's precision, as it did in the
            # plugin's NumPy, whatever the precision of the divisor.
            pixels = pixels / pixels.dtype.type(divisors[number])
            if rescale_inputs:
                pixels = _stretched(
                    pixels, pixels.min(), pixels.max(), 1.0 / _SIXTEEN_BIT, 1.0
                )
            pixels = rescale_after_masking.image(pixels, region)
            sixteen_bit.append(np.round(pixels * _SIXTEEN_BIT).reshape(-1))

        class_numbers = sorted(members)
        class_pixels = {
            number: np.concatenate([sixteen_bit[index] for index in members[number]])
            for number in class_numbers
        }
        template = histogram_matching.template(class_pixels, region)
        prepared: list[np.ndarray] = []
        for number in class_numbers:
            values = histogram_matching.before_masking(
                number, class_pixels[number], template
            )
            values = region.masked(values, len(members[number]))
            values = rescale_after_masking.class_pixels(values)
            prepared.append(histogram_matching.after_masking(number, values, template))
        unmixed = _unmixed(prepared)

    compensated: dict[int, np.ndarray] = {}
    for values, number in zip(unmixed, class_numbers):
        class_images = values.reshape(len(members[number]), *shape) / float(_SIXTEEN_BIT)
        for index, pixels in zip(members[number], class_images):
            pixels = np.clip(pixels, 0, 1)
            if rescale_outputs:
                pixels = _stretched(pixels, pixels.min(), pixels.max(), 0.0, 1.0)
            compensated[index] = pixels.astype(np.float32)
    return pack_aligned_image_outputs(
        tuple(compensated[index] for index in range(len(planes)))
    )


@dataclass(frozen=True, slots=True)
class _WithinObjectsBinding(SettingToKeywordBinding):
    """CellProfiler's choice of where to compensate, as whether objects are used."""

    def bind(
        self,
        module: ModuleBlock,
        kwargs: dict[str, CellProfilerSettingValue],
        binder: SettingsBinder,
    ) -> None:
        del binder
        kwargs[self.require_parameter_name()] = _compensates_within_objects(module)

    def records_from_kwargs(
        self, kwargs: Mapping[str, object]
    ) -> tuple[ModuleSetting, ...]:
        name = self.require_parameter_name()
        if name not in kwargs:
            return ()
        return (
            ModuleSetting(
                setting_names(self.setting_name)[0],
                _WITHIN_OBJECTS if kwargs[name] else _ENTIRE_IMAGE,
            ),
        )


def _compensates_within_objects(module: ModuleBlock) -> bool:
    where = required_setting_value(module, _WHERE_SETTING)
    if where not in (_WITHIN_OBJECTS, _ENTIRE_IMAGE):
        raise ValueError(
            f"CompensateColors({module.module_num}) compensates {_ENTIRE_IMAGE!r} "
            f"or {_WITHIN_OBJECTS!r}, got {where!r}."
        )
    return where == _WITHIN_OBJECTS


def _chosen(module: ModuleBlock, setting: str, kinds: tuple[type, ...]) -> type:
    choice = required_setting_value(module, setting)
    for kind in kinds:
        if kind.choice == choice:
            return kind
    raise ValueError(
        f"CompensateColors({module.module_num}) setting {setting!r} is one of "
        f"{[kind.choice for kind in kinds]}, got {choice!r}."
    )


@dataclass(frozen=True, slots=True)
class _RescaleAfterMaskingBinding(SettingToKeywordBinding):
    def bind(
        self,
        module: ModuleBlock,
        kwargs: dict[str, CellProfilerSettingValue],
        binder: SettingsBinder,
    ) -> None:
        del binder
        kwargs[self.require_parameter_name()] = _chosen(
            module, _RESCALE_AFTER_MASKING_SETTING, _RESCALES_AFTER_MASKING
        )()

    def records_from_kwargs(
        self, kwargs: Mapping[str, object]
    ) -> tuple[ModuleSetting, ...]:
        rescale = kwargs.get(self.require_parameter_name())
        if not isinstance(rescale, RescaleAfterMasking):
            return ()
        return (ModuleSetting(_RESCALE_AFTER_MASKING_SETTING, rescale.choice),)


@dataclass(frozen=True, slots=True)
class _ClassHistogramMatchingBinding(SettingToKeywordBinding):
    """The matching chosen by a block, with the template class it names."""

    def bind(
        self,
        module: ModuleBlock,
        kwargs: dict[str, CellProfilerSettingValue],
        binder: SettingsBinder,
    ) -> None:
        del binder
        kind = _chosen(
            module,
            _MATCHING_SETTING,
            (NoClassHistogramMatching, *_CLASS_HISTOGRAM_MATCHINGS),
        )
        kwargs[self.require_parameter_name()] = (
            kind(
                parse_cellprofiler_int(
                    required_setting_value(module, _TEMPLATE_CLASS_SETTING)
                )
            )
            if issubclass(kind, _TemplateClassMatching)
            else kind()
        )

    def records_from_kwargs(
        self, kwargs: Mapping[str, object]
    ) -> tuple[ModuleSetting, ...]:
        matching = kwargs.get(self.require_parameter_name())
        if not isinstance(matching, ClassHistogramMatching):
            return ()
        return (
            ModuleSetting(_MATCHING_SETTING, matching.choice),
            ModuleSetting(
                _TEMPLATE_CLASS_SETTING, str(matching.template_class_number())
            ),
        )


class CompensateColorsModule(SingleObjectLabelInputPolicy, ObjectArtifactInputModule):
    module_name = "CompensateColors"
    function_name = "compensate_colors"
    validated = True
    label_kwarg = "labels"

    # Two rows: the number of image groups, then the number of object rows.
    hidden_count_setting = "Hidden"
    input_image_setting = "Select an image to measure"
    class_setting = "What compensation class does this image belong to?"
    output_image_setting = "Select an output image name"
    input_image_binding = SettingToKeywordBinding.input(
        input_image_setting, ImageArtifactType, repeated=True
    )
    output_image_binding = SettingToKeywordBinding.output(
        output_image_setting, ImageArtifactType, repeated=True
    )
    # The plugin compensates within the first objects a block names.
    objects_binding = SettingToKeywordBinding.input(
        _OBJECTS_SETTING, ObjectLabelsArtifactType, runtime_parameter_name="labels"
    )
    setting_bindings: ClassVar[tuple[SettingToKeywordBinding, ...]] = (
        input_image_binding,
        SettingToKeywordBinding(
            class_setting, "compensation_classes", parse_cellprofiler_int, repeated=True
        ),
        output_image_binding,
        _WithinObjectsBinding(_WHERE_SETTING, "within_objects"),
        objects_binding,
        SettingToKeywordBinding(
            "Should individual images be rescaled 0-1 before compensating "
            "pre-masking or on unmasked images?",
            "rescale_inputs",
            parse_cellprofiler_bool,
        ),
        _RescaleAfterMaskingBinding(
            _RESCALE_AFTER_MASKING_SETTING, "rescale_after_masking"
        ),
        _ClassHistogramMatchingBinding(_MATCHING_SETTING, "histogram_matching"),
        SettingToKeywordBinding(
            "Should images be rescaled 0-1 after compensating?",
            "rescale_outputs",
            parse_cellprofiler_bool,
        ),
        SettingToKeywordBinding(
            "Should the images be divided by a scalar based on group percentiles",
            "divide_by_class_percentile",
            parse_cellprofiler_bool,
        ),
        SettingToKeywordBinding(
            "What percentile should be used for multiplication",
            "class_percentile",
            parse_cellprofiler_float,
        ),
        SettingToKeywordBinding(
            "Should the images have a tophat filter applied before correction?",
            "tophat_filter",
            parse_cellprofiler_bool,
        ),
        SettingToKeywordBinding(
            "What size radius should be used for the tophat filter?",
            "tophat_radius",
            parse_cellprofiler_int,
        ),
        SettingToKeywordBinding(
            "Should the images have a Laplacian of Gaussian filter applied "
            "before correction?",
            "laplacian_of_gaussian_filter",
            parse_cellprofiler_bool,
        ),
        SettingToKeywordBinding(
            "What size radius should be used for the LoG filter?",
            "laplacian_of_gaussian_sigma",
            parse_cellprofiler_int,
        ),
        SettingToKeywordBinding(
            "Should the images have a Difference of Gaussians filter applied "
            "before correction?",
            "difference_of_gaussians_filter",
            parse_cellprofiler_bool,
        ),
        SettingToKeywordBinding(
            "What size sigma should be used for the DoG low sigma?",
            "difference_of_gaussians_low_sigma",
            parse_cellprofiler_int,
        ),
        SettingToKeywordBinding(
            # The plugin's wording; this is the high sigma.
            "What size radius should be used for the DoG low sigma?",
            "difference_of_gaussians_high_sigma",
            parse_cellprofiler_int,
        ),
    )

    @classmethod
    def postprocess_bound_settings(
        cls, module: ModuleBlock, bound: BoundModuleSettings
    ) -> BoundModuleSettings:
        image_names = setting_values(module, cls.input_image_setting)
        class_numbers = setting_values(module, cls.class_setting)
        output_names = setting_values(module, cls.output_image_setting)
        if not image_names or not (
            len(image_names) == len(class_numbers) == len(output_names)
        ):
            raise ValueError(
                f"CompensateColors({module.module_num}) needs a class and an output "
                f"name for each image, got {image_names!r}, {class_numbers!r} and "
                f"{output_names!r}."
            )
        named_outputs = cls.artifact_names_for_binding(module, cls.output_image_binding)
        if len(named_outputs) != len(image_names) or len(set(named_outputs)) != len(
            named_outputs
        ):
            # The function returns one image per input image. The plugin keeps
            # one image per name, the last it makes, so names used twice (its
            # default, "None", among them) leave it with fewer.
            raise ValueError(
                f"CompensateColors({module.module_num}) needs a different output "
                f"image name for each input image, got {output_names!r}."
            )
        if _compensates_within_objects(module) and not setting_values(
            module, _OBJECTS_SETTING
        ):
            raise _refuse("no objects are named to compensate within")
        counts = setting_values(module, cls.hidden_count_setting)
        if counts and int(counts[0]) != len(image_names):
            raise ValueError(
                f"CompensateColors({module.module_num}) declares {counts[0]} image "
                f"group(s) but has {len(image_names)}."
            )
        return bound.with_kwargs(
            {
                "compensation_classes": tuple(
                    parse_cellprofiler_int(number) for number in class_numbers
                ),
            }
        ).with_consumed_settings(
            cls.hidden_count_setting,
            cls.input_image_setting,
            cls.class_setting,
            cls.output_image_setting,
            _TEMPLATE_CLASS_SETTING,
        )

    @classmethod
    def active_artifact_bindings(
        cls,
        module: ModuleBlock | None = None,
        *,
        invocation_key: FunctionInvocationKey | None = None,
    ) -> tuple[SettingToKeywordBinding, ...]:
        """Objects are an input only when the block compensates within them."""
        bindings = super().active_artifact_bindings(
            module, invocation_key=invocation_key
        )
        if module is None or _compensates_within_objects(module):
            return bindings
        return tuple(
            binding for binding in bindings if binding is not cls.objects_binding
        )

    @classmethod
    def artifact_names_for_binding(
        cls, module: ModuleBlock, binding: SettingToKeywordBinding
    ) -> tuple[str, ...]:
        names = super().artifact_names_for_binding(module, binding)
        if binding is cls.objects_binding:
            return names[:1]
        return names

    @classmethod
    def artifact_output_relations(
        cls,
        module: ModuleBlock,
        *,
        invocation_key: FunctionInvocationKey,
        step_context: object,
        binding: SettingToKeywordBinding,
        name: str,
        artifact_inputs: ArtifactSpecCollection,
        output_position: int,
    ) -> tuple[ArtifactSpecRelation, ...]:
        """Every output depends on all input images; the first gives its scope."""
        del module, invocation_key, step_context, binding, name, output_position
        image_inputs = artifact_inputs.for_artifact_type(ImageArtifactType).specs
        if not image_inputs:
            raise ValueError("CompensateColors requires at least one image input.")
        return (GroupLineageSourceRelation(source=image_inputs[0].ref()),)
