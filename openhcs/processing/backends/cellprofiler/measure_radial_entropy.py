"""CellProfiler plugin MeasureRadialEntropy.

Upstream: CellProfiler-plugins
``unmaintained_plugins/CellProfiler4_autoconverted/measureradialentropy.py``.
CellProfiler 4.2.8.1 cannot load that file under its upstream name: its class
is called ``MeasurementTemplate`` and CellProfiler only takes the class whose
lower-cased name is the file name ("Could not find
cellprofiler_core.module.Module class"). Copied unchanged to
``measurementtemplate.py`` it loads and registers as ``MeasureRadialEntropy``;
that copy made the reference outputs this module is tested against.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Mapping
from dataclasses import dataclass
from typing import TYPE_CHECKING, ClassVar

import numpy as np
from scipy.special import entr

from openhcs.core.artifacts.kinds import ImageArtifactType, ObjectLabelsArtifactType
from openhcs.core.measurement_row_materialization import MeasurementSparseColumnarRows
from openhcs.core.memory.decorators import numpy
from openhcs.core.pipeline.function_contracts import (
    runtime_bound_parameters,
    special_inputs,
)
from openhcs.core.processing_contracts import Pure2DContract
from openhcs.core.runtime_batch_contracts import SliceIndexRuntimeParameter
from openhcs.core.runtime_image_values import ImagePayload
from openhcs.core.runtime_measurements import MeasurementRowAxisField
from openhcs.core.runtime_object_labels import (
    ObjectLabelValue,
    object_label_dense_array,
)
from openhcs.core.runtime_plane_projection import RuntimeSliceInvariantValue
from openhcs.core.runtime_tabular_values import FieldSpec
from openhcs.core.source_spatial_domain import VolumeSourceSpatialDomain
from openhcs.interop.cellprofiler.module_artifact_declarations import (
    ObjectArtifactInputModule,
    ObjectMeasurementArtifactOutputModule,
)
from openhcs.interop.cellprofiler.parser import ModuleSetting
from openhcs.interop.cellprofiler.runtime.measurement_recording import (
    NoObjectNameMeasurementRecordMixin,
)
from openhcs.interop.cellprofiler.runtime.measurement_rows import (
    ModuleOwnedResultMeasurementRows,
)
from openhcs.interop.cellprofiler.runtime.object_input_policies import (
    LabelsObjectInputPolicy,
)
from openhcs.interop.cellprofiler.setting_names import required_setting_value
from openhcs.interop.cellprofiler.settings_binder import SettingToKeywordBinding

if TYPE_CHECKING:
    from openhcs.interop.cellprofiler.parser import ModuleBlock
    from openhcs.interop.cellprofiler.runtime.output_record_request import (
        CellProfilerOutputRecordRequest,
    )
    from openhcs.interop.cellprofiler.settings_binder import (
        CellProfilerSettingValue,
        SettingsBinder,
    )

_PLUGIN_FAILS = "the CellProfiler plugin fails"
_OBJECT_NAME = MeasurementRowAxisField.OBJECT_NAME.value
_OBJECT_LABEL = MeasurementRowAxisField.OBJECT_LABEL.value
_SLICE_INDEX = MeasurementRowAxisField.SLICE_INDEX.value
_CATEGORY = "Entropy"
_METRIC_SETTING = "Which intensity measurement should be used?"
_DEFAULT_BINS = 6


def _refuse(reason: str) -> ValueError:
    return ValueError(
        f"MeasureRadialEntropy cannot run: {reason}; {_PLUGIN_FAILS} here."
    )


class WedgeIntensity(RuntimeSliceInvariantValue, ABC):
    """The one number that stands for the pixels of a wedge."""

    choice: ClassVar[str]
    """The wording of this choice in CellProfiler, also part of the measurement names."""

    @abstractmethod
    def of(self, pixels: np.ndarray) -> float:
        """The wedge's value from its pixels, taken in the pixels' own number type."""


@dataclass(frozen=True, slots=True)
class MeanIntensity(WedgeIntensity):
    """A wedge counts with the mean of its pixels."""

    choice: ClassVar[str] = "Mean"

    def of(self, pixels: np.ndarray) -> float:
        return float(np.mean(pixels))


@dataclass(frozen=True, slots=True)
class MedianIntensity(WedgeIntensity):
    """A wedge counts with the median of its pixels."""

    choice: ClassVar[str] = "Median"

    def of(self, pixels: np.ndarray) -> float:
        return float(np.median(pixels))


@dataclass(frozen=True, slots=True)
class IntegratedIntensity(WedgeIntensity):
    """A wedge counts with the sum of its pixels."""

    choice: ClassVar[str] = "Integrated"

    def of(self, pixels: np.ndarray) -> float:
        return float(np.sum(pixels))


_WEDGE_INTENSITIES: tuple[type[WedgeIntensity], ...] = (
    MeanIntensity,
    MedianIntensity,
    IntegratedIntensity,
)


def _entropy_feature(metric: WedgeIntensity, bins: int) -> str:
    """Name of an object's entropy, without CellProfiler's category and image."""
    return f"{metric.choice}_{bins}"


def _wedge_feature(metric: WedgeIntensity, bins: int, position: int) -> str:
    """Name of the ``position``-th wedge value (from 1), likewise."""
    return f"{metric.choice}_Bin{position}_of_{bins}"


def _wedge_values(
    pixels: np.ndarray,
    inside: np.ndarray,
    centre: tuple[float, float],
    metric: WedgeIntensity,
    bins: int,
) -> list[float]:
    """One value per wedge, in the order the plugin lists them.

    Wedges come in the order their first pixel is met reading the image row by
    row; wedges without a pixel follow as NaN, by number.
    """
    rows, columns = np.nonzero(inside)
    numbers = np.ceil(
        (np.pi + np.arctan2(rows - centre[0], columns - centre[1]))
        * (bins / (2 * np.pi))
    ).astype(np.int64)
    values = pixels[rows, columns]
    met, first_met = np.unique(numbers, return_index=True)
    measured = [
        metric.of(values[numbers == number]) for number in met[np.argsort(first_met)]
    ]
    empty = [number for number in range(1, bins + 1) if number not in met]
    return [*measured, *([float("nan")] * len(empty))]


def _entropy(values: np.ndarray) -> float:
    """Shannon entropy of the values' shares of their sum, NaN values left out."""
    counted = values[~np.isnan(values)]
    with np.errstate(invalid="ignore", divide="ignore"):
        return float(np.sum(entr(1.0 * counted / np.sum(counted))))


@numpy(contract=Pure2DContract)
@special_inputs("labels")
@runtime_bound_parameters(SliceIndexRuntimeParameter)
def measure_radial_entropy(
    image: ImagePayload,
    labels: ObjectLabelValue,
    metric: WedgeIntensity = MeanIntensity(),
    bins: int = _DEFAULT_BINS,
    slice_index: int = 0,
) -> tuple[ImagePayload, MeasurementSparseColumnarRows]:
    """Measure how unevenly an image's intensity is spread around each object.

    Each object is cut into ``bins`` pie-shaped wedges around its centroid.
    Every wedge gets one value from its pixels (``metric``), and the object's
    measurement is the Shannon entropy (natural logarithm) of the wedge values'
    shares of their sum: ``log(bins)`` when all wedges are alike, lower the more
    the intensity sits in few wedges.

    Per object, with ``<Metric>`` being ``Mean``, ``Median`` or ``Integrated``:
    ``<Metric>_<bins>`` (the entropy) and ``<Metric>_Bin<k>_of_<bins>`` for k
    from 1 to ``bins`` (wedge values). A CellProfiler pipeline records them as
    ``Entropy_<Image>_<Metric>_<bins>`` and
    ``Entropy_<Image>_<Metric>_Bin<k>_of_<bins>`` of the objects.

    The plugin's behaviour is kept, including:

    - ``Bin<k>`` is not the k-th wedge by angle. The wedge values are listed in
      the order the wedges' first pixels are met reading the image row by row;
      wedges without a pixel follow as NaN. A small object therefore has its
      values first and NaN after them.
    - Wedges without a pixel are left out of the entropy.
    - A pixel directly left of the centroid can fall into a wedge beyond the
      numbered ones, which gives the object one value more. All values enter
      the entropy; only the first ``bins`` are reported.
    - Pixels with intensity -1 are taken to lie outside their object.
    - Wedge values are computed in the image's number type (32-bit means and
      sums for a 32-bit image); a yes/no image counts as 0 and 1.
    - Wedge values that sum to 0 give NaN, a negative share gives minus
      infinity.
    - The plugin fails, and this function refuses: no objects; object numbers
      with gaps (the plugin then pairs objects with other objects' centroids
      and runs out of centroids); objects with different numbers of wedge
      values (see above); an image and objects of different sizes; a volume.

    Args:
        labels: The objects to measure.
        metric: How a wedge's pixels become its value: ``MeanIntensity``,
            ``MedianIntensity`` or ``IntegratedIntensity`` (their sum).
        bins: Number of wedges. CellProfiler allows 3 to 60.
    """
    if bins < 1:
        raise ValueError(f"MeasureRadialEntropy needs at least one wedge, got {bins}.")
    pixels = np.asarray(image.data)
    if pixels.dtype.kind != "f":
        # CellProfiler hands the plugin a yes/no image as 64-bit numbers.
        pixels = pixels.astype(np.float64)
    label_plane = object_label_dense_array(labels, dtype=np.int32)
    if pixels.ndim != 2 or isinstance(
        image.metadata.source_spatial_domain, VolumeSourceSpatialDomain
    ):
        raise _refuse("it works on single planes, not on volumes")
    if label_plane.shape != pixels.shape:
        raise _refuse("the image and the objects differ in size")
    object_count = int(label_plane.max(initial=0))
    if object_count == 0:
        raise _refuse("there are no objects")
    # The plugin has one centroid per object present, in object-number order,
    # and takes the n-th of them for object number n.
    centroids = [
        np.argwhere(label_plane == number).mean(axis=0)
        for number in np.unique(label_plane[label_plane > 0])
    ]
    outside = np.full(pixels.shape, -1).astype(pixels.dtype)
    per_object: list[np.ndarray] = []
    for number in range(1, object_count + 1):
        of_object = label_plane == number
        kept = outside.copy()
        kept[of_object] = pixels[of_object]
        inside = kept != np.float64(-1)
        if not inside.any():
            per_object.append(np.full(bins, np.nan))
            continue
        if number > len(centroids):
            raise _refuse("the objects are not numbered 1 to their count")
        centre_row, centre_column = centroids[number - 1]
        per_object.append(
            np.array(
                _wedge_values(kept, inside, (centre_row, centre_column), metric, bins),
                dtype=float,
            )
        )
    if len({len(values) for values in per_object}) > 1:
        raise _refuse(
            "a pixel directly left of an object's centroid gives that object one "
            "wedge value more than the others have"
        )
    names = (
        _entropy_feature(metric, bins),
        *(_wedge_feature(metric, bins, position) for position in range(1, bins + 1)),
    )
    rows = [
        {
            _OBJECT_LABEL: number,
            _SLICE_INDEX: slice_index,
            **dict(zip(names, (_entropy(values), *map(float, values[:bins])))),
        }
        for number, values in enumerate(per_object, start=1)
    ]
    return (
        image,
        MeasurementSparseColumnarRows.from_rows(
            rows,
            fields=(
                FieldSpec(_SLICE_INDEX, int, required=False),
                FieldSpec(_OBJECT_LABEL, int, required=False),
                *(FieldSpec(name, float, required=False) for name in names),
            ),
        ),
    )


def _parse_bins(text: str) -> int:
    """CellProfiler's reading of the bin count.

    A count that is no whole number from 3 to 60 leaves the setting at the
    plugin's default.
    """
    try:
        bins = int(text)
    except ValueError:
        return _DEFAULT_BINS
    return bins if 3 <= bins <= 60 else _DEFAULT_BINS


@dataclass(frozen=True, slots=True)
class _WedgeIntensityBinding(SettingToKeywordBinding):
    def bind(
        self,
        module: ModuleBlock,
        kwargs: dict[str, CellProfilerSettingValue],
        binder: SettingsBinder,
    ) -> None:
        del binder
        choice = required_setting_value(module, self.setting_name)
        for kind in _WEDGE_INTENSITIES:
            if kind.choice == choice:
                kwargs[self.require_parameter_name()] = kind()
                return
        raise ValueError(
            f"MeasureRadialEntropy({module.module_num}) setting "
            f"{_METRIC_SETTING!r} is one of "
            f"{[kind.choice for kind in _WEDGE_INTENSITIES]}, got {choice!r}."
        )

    def records_from_kwargs(
        self, kwargs: Mapping[str, object]
    ) -> tuple[ModuleSetting, ...]:
        metric = kwargs.get(self.require_parameter_name())
        if not isinstance(metric, WedgeIntensity):
            return ()
        return (ModuleSetting(_METRIC_SETTING, metric.choice),)


class MeasureRadialEntropyModule(
    NoObjectNameMeasurementRecordMixin,
    LabelsObjectInputPolicy,
    ObjectArtifactInputModule,
    ObjectMeasurementArtifactOutputModule,
):
    module_name = "MeasureRadialEntropy"
    function_name = "measure_radial_entropy"
    validated = True
    measurement_category_prefixes = (("entropy",),)
    setting_bindings: ClassVar[tuple[SettingToKeywordBinding, ...]] = (
        SettingToKeywordBinding.input("Select an image to measure", ImageArtifactType),
        SettingToKeywordBinding.input(
            "Select objects to measure",
            ObjectLabelsArtifactType,
            runtime_parameter_name="labels",
        ),
        _WedgeIntensityBinding(_METRIC_SETTING, "metric"),
        SettingToKeywordBinding("Input number of bins", "bins", _parse_bins),
    )

    @dataclass(frozen=True, slots=True)
    class MeasurementRows(ModuleOwnedResultMeasurementRows):
        """The function's rows under CellProfiler's names.

        CellProfiler names each measurement after the image it was made on and
        files it under the objects' name; the block knows both, the function
        neither.
        """

        image_name: str
        object_name: str

        @classmethod
        def for_request(
            cls,
            module_type: type[object],
            request: CellProfilerOutputRecordRequest,
        ) -> MeasureRadialEntropyModule.MeasurementRows:
            inputs = request.callable_contract.artifact_inputs.specs
            (image_name,) = (
                spec.name for spec in inputs if spec.artifact_type is ImageArtifactType
            )
            (object_name,) = (
                spec.name
                for spec in inputs
                if spec.artifact_type is ObjectLabelsArtifactType
            )
            return cls(
                request.output_value,
                module_type=module_type,
                image_name=image_name,
                object_name=object_name,
            )

        def rows(self) -> MeasurementSparseColumnarRows:
            measured = self.source_rows()
            axes = (_SLICE_INDEX, _OBJECT_LABEL)
            named = {
                field.name: (
                    field.name
                    if field.name in axes
                    else f"{_CATEGORY}_{self.image_name}_{field.name}"
                )
                for field in measured.fields
            }
            return MeasurementSparseColumnarRows.from_rows(
                [
                    {
                        _OBJECT_NAME: self.object_name,
                        **{named[name]: value for name, value in row.items()},
                    }
                    for row in measured.iter_row_mappings()
                ],
                fields=(
                    FieldSpec(_OBJECT_NAME, str, required=False),
                    *(
                        FieldSpec(named[field.name], field.dtype, required=False)
                        for field in measured.fields
                    ),
                ),
            )
