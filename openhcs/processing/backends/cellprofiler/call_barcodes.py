"""CellProfiler plugin CallBarcodes.

Upstream: CellProfiler-plugins ``active_plugins/callbarcodes.py``.
"""

from __future__ import annotations

import csv
import inspect
import re
from abc import ABC, abstractmethod
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, ClassVar

import numpy as np

from openhcs.core.aligned_image_payload import (
    AlignedImageStack,
    pack_aligned_image_outputs,
)
from openhcs.core.artifacts.kinds import ImageArtifactType, ObjectLabelsArtifactType
from openhcs.core.artifacts.plans import ArtifactOutputPlan
from openhcs.core.callable_contract import KeywordRuntimeParameter
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
from openhcs.core.steps.function_runtime import RuntimeCallableArgument
from openhcs.core.vfs_protocol import PlateInputFile
from openhcs.interop.cellprofiler.cellprofiler_literals import (
    decode_cellprofiler_setting_literal,
)
from openhcs.interop.cellprofiler.module_artifact_declarations import (
    ObjectArtifactInputModule,
    ObjectMeasurementArtifactOutputModule,
    PriorMeasurementArtifactInputModule,
)
from openhcs.interop.cellprofiler.module_settings import BoundModuleSettings
from openhcs.interop.cellprofiler.parser import ModuleSetting
from openhcs.interop.cellprofiler.runtime.artifact_binding import (
    RuntimeInputBindingRequest,
)
from openhcs.interop.cellprofiler.runtime.measurement_recording import (
    NoObjectNameMeasurementRecordMixin,
)
from openhcs.interop.cellprofiler.runtime.object_input_policies import (
    LabelsObjectInputPolicy,
)
from openhcs.interop.cellprofiler.runtime.object_measurement_vectors import (
    CellProfilerObjectMeasurementVectorBinding,
)
from openhcs.interop.cellprofiler.runtime.primary_image_input_policies import (
    ObjectLabelDrivenPrimaryImageInputPolicy,
)
from openhcs.interop.cellprofiler.setting_names import (
    SettingNameFamily,
    block_setting_value_by_prefix,
    optional_setting_value,
    repeating_setting_blocks,
    required_setting_value,
    setting_names,
)
from openhcs.interop.cellprofiler.settings_binder import (
    MeasurementFeatureSettingBinding,
    SettingToKeywordBinding,
    SourceFileSettingBinding,
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

_BASES = "ACGT"
_PLUGIN_FAILS = "the CellProfiler plugin fails"


def _refuse(reason: str) -> ValueError:
    return ValueError(f"CallBarcodes cannot run: {reason}; {_PLUGIN_FAILS} here.")


class BaseCalling(RuntimeSliceInvariantValue, ABC):
    """How one base per sequencing cycle is read from an object's measurements."""

    @abstractmethod
    def feature_names(self, cycles: int) -> tuple[str, ...]:
        """Measurements of the objects this calling reads, in the order it takes them."""

    @abstractmethod
    def barcodes(
        self, values: tuple[np.ndarray, ...], cycles: int, object_name: str
    ) -> tuple[list[str], np.ndarray | None]:
        """Barcode per object, and its quality score where the calling has one.

        ``values`` holds one array (a value per object) per name of
        ``feature_names(cycles)``, in that order.
        """

    @abstractmethod
    def setting_rows(self) -> tuple[tuple[str, str], ...]:
        """The CellProfiler setting rows (name, value) that describe this calling."""


@dataclass(frozen=True, slots=True)
class BrightestBase(BaseCalling):
    """Each cycle has one measurement per base; the largest names the base.

    CellProfiler's "One Hot Exponentially Multiplexed" encoding.
    """

    cycle_1_feature: str
    """One of the four measurements of the first cycle, such as
    ``Intensity_MaxIntensity_CorrCycle01_A``. The others are derived by
    replacing its cycle number and its base letter."""

    def feature_names(self, cycles: int) -> tuple[str, ...]:
        _, _, after_cycle = self.cycle_1_feature.partition("Cycle")
        number = re.search("[0-9]{1,2}", after_cycle)
        base = re.search("[A-Z]", after_cycle)
        if number is None or base is None or base.group() not in _BASES:
            raise _refuse(
                f"measurement {self.cycle_1_feature!r} does not name a cycle number "
                "and one of the bases A, C, G, T after the word 'Cycle'"
            )
        start = len(self.cycle_1_feature) - len(after_cycle)
        width = len(number.group())
        names = []
        for cycle in range(1, cycles + 1):
            characters = list(self.cycle_1_feature)
            for letter in _BASES:
                characters[start + base.start()] = letter
                named = "".join(characters)
                names.append(
                    named[: start + number.start()]
                    + str(cycle).zfill(width)
                    + named[start + number.end() :]
                )
        return tuple(names)

    def barcodes(
        self, values: tuple[np.ndarray, ...], cycles: int, object_name: str
    ) -> tuple[list[str], np.ndarray | None]:
        del object_name
        names = self.feature_names(cycles)
        object_count = len(values[0]) if values else 0
        called = [""] * object_count
        scores = np.zeros((cycles, object_count))
        for cycle in range(cycles):
            # CellProfiler lists an object's measurements by name, and the first
            # of several equal maxima is the base called.
            of_cycle = sorted(
                range(cycle * len(_BASES), (cycle + 1) * len(_BASES)),
                key=names.__getitem__,
            )
            intensities = np.transpose(
                np.array([np.asarray(values[index], dtype=float) for index in of_cycle])
            ).reshape(object_count, len(of_cycle))
            brightest = np.argmax(intensities, axis=1)
            with np.errstate(invalid="ignore", divide="ignore"):
                scores[cycle] = np.max(intensities, axis=1) / np.sum(
                    intensities, axis=1
                )
            for position, index in enumerate(brightest):
                called[position] += _BASES[of_cycle[index] % len(_BASES)]
        return called, scores.mean(axis=0)

    def setting_rows(self) -> tuple[tuple[str, str], ...]:
        return (
            (_ENCODING_SETTING, _BRIGHTEST_BASE_ENCODING),
            (_CYCLE_1_FEATURE_SETTING, self.cycle_1_feature),
        )


@dataclass(frozen=True, slots=True)
class BaseMeasurement(RuntimeSliceInvariantValue):
    """One measurement that speaks for or against a base."""

    base: str
    """The base, one of A, C, G, T."""

    cycle_1_feature: str
    """The measurement of the first cycle; its name must hold ``Cycle`` followed
    by the cycle number."""

    positive_means_base: bool = True
    """Whether a value at or above the threshold supports the base (otherwise it
    rules the base out)."""

    def feature_names(self, cycles: int) -> tuple[str, ...]:
        named_cycle = re.search("Cycle.*[0-9]{1,2}", self.cycle_1_feature)
        if named_cycle is None:
            raise _refuse(
                f"measurement {self.cycle_1_feature!r} does not name a cycle number "
                "after the word 'Cycle'"
            )
        return tuple(
            self.cycle_1_feature.replace(
                named_cycle.group(),
                re.sub(
                    "Cycle[0-9]{1,2}",
                    f"Cycle{cycle:02d}" if cycle < 10 else f"Cycle{cycle}",
                    named_cycle.group(),
                ),
            )
            for cycle in range(1, cycles + 1)
        )


@dataclass(frozen=True, slots=True)
class BasesOverThreshold(BaseCalling):
    """A base is called in a cycle when it alone passes its measurements' tests.

    CellProfiler's "Exponentially Multiplexed" encoding. A cycle in which no
    base or more than one base passes is called ``X``.
    """

    measurements: tuple[BaseMeasurement, ...]
    """The tests of each base; a base passes when all of its tests do."""

    minimum_positive_value: float = 1.0
    """A measurement at or above this value is positive."""

    def feature_names(self, cycles: int) -> tuple[str, ...]:
        return tuple(
            name
            for measurement in self.measurements
            for name in measurement.feature_names(cycles)
        )

    def barcodes(
        self, values: tuple[np.ndarray, ...], cycles: int, object_name: str
    ) -> tuple[list[str], np.ndarray | None]:
        if object_name != "Foci":
            raise _refuse(
                "with this encoding the plugin only finds the measurements of "
                f"objects named 'Foci', not {object_name!r}"
            )
        object_count = len(values[0]) if values else 0
        called = [""] * object_count
        for cycle in range(cycles):
            passes = np.ones((object_count, len(_BASES)))
            for index, measurement in enumerate(self.measurements):
                positive = (
                    np.asarray(values[index * cycles + cycle], dtype=float)
                    >= self.minimum_positive_value
                )
                passes[:, _BASES.index(measurement.base)] *= (
                    positive if measurement.positive_means_base else ~positive
                )
            for position, of_object in enumerate(passes):
                called[position] += (
                    _BASES[int(of_object.argmax())] if of_object.sum() == 1 else "X"
                )
        return called, None

    def setting_rows(self) -> tuple[tuple[str, str], ...]:
        rows = [(_ENCODING_SETTING, "Exponentially Multiplexed (SBS/ISS only)")]
        for measurement in self.measurements:
            base = measurement.base
            rows += [
                (_BASE_SETTING, base),
                (
                    f"{_BASE_FEATURE_SETTING_START} first measurement indicating "
                    f"that {base} is encoded",
                    measurement.cycle_1_feature,
                ),
                (
                    f"{_BASE_POSITIVE_SETTING_START} called {base}?",
                    "Yes" if measurement.positive_means_base else "No",
                ),
            ]
        return (*rows, (_MINIMUM_SETTING, repr(self.minimum_positive_value)))


@dataclass(frozen=True, slots=True)
class BarcodeLibrary:
    """Known barcodes with their position in the library file and their gene."""

    entries: dict[str, tuple[int, str]]

    @classmethod
    def read(
        cls,
        path: Path,
        *,
        barcode_column: str,
        gene_column: str,
        empty_vector_barcode: str | None,
    ) -> BarcodeLibrary:
        entries: dict[str, tuple[int, str]] = {}
        position = 1
        with open(path) as library_file:
            for row in csv.DictReader(library_file):
                for column in (barcode_column, gene_column):
                    if column not in row:
                        raise ValueError(
                            f"Barcode library {path} has no column {column!r}."
                        )
                if row[barcode_column]:
                    # A repeated barcode keeps its first place in the search
                    # order and takes the later row's position and gene.
                    entries[row[barcode_column]] = (position, row[gene_column])
                    position += 1
        if empty_vector_barcode is not None:
            entries[empty_vector_barcode] = (position, "EmptyVector")
        return cls(entries)

    def closest(self, called: str) -> tuple[float, str]:
        """Share of matching bases and the library barcode that best matches."""
        by_start = {barcode[: len(called)]: barcode for barcode in self.entries}
        if called in by_start:
            return 1.0, by_start[called]
        by_score: dict[float, str] = {}
        for start, barcode in by_start.items():
            if len(start) < len(called):
                raise _refuse(
                    f"library barcode {barcode!r} is shorter than the "
                    f"{len(called)} cycles called"
                )
            # Of several barcodes with the same score the last one is kept.
            by_score[
                sum(1 for a, b in zip(called, start) if a == b) / float(len(called))
            ] = barcode
        if not by_score:
            raise _refuse("the barcode library is empty")
        best = max(by_score)
        return best, by_score[best]


_ENCODING_SETTING = "What kind of encoding is used here?"
_BRIGHTEST_BASE_ENCODING = "One Hot Exponentially Multiplexed (ie 4-color SBS/ISS)"
_CYCLES_SETTING = "Number of cycles"
_CYCLE_1_FEATURE_SETTING = "Select one of the measures from Cycle 1 to use for calling"
_BASE_SETTING = "Base we are currently calling"
_BASE_FEATURE_SETTING_START = "Select the"
_BASE_POSITIVE_SETTING_START = "Does a positive value here mean the base SHOULD be"
_MINIMUM_SETTING = "Minimum value to be considered positive in a channel"
_MATCH_LIBRARY_SETTING = "Do you want to match to an external library of barcodes?"
_LIBRARY_FOLDER_SETTING = "Input data file location"
_HAS_EMPTY_VECTOR_SETTING = (
    "Do you have an empty vector barcode you would like to add to the barcode list?"
)


def _calling_of(module: ModuleBlock) -> BaseCalling:
    encoding = optional_setting_value(module, _ENCODING_SETTING)
    # Pipelines saved before the plugin had a second encoding carry no choice.
    if encoding is None or encoding == _BRIGHTEST_BASE_ENCODING:
        return BrightestBase(required_setting_value(module, _CYCLE_1_FEATURE_SETTING))
    minimum = optional_setting_value(module, _MINIMUM_SETTING)
    return BasesOverThreshold(
        tuple(
            BaseMeasurement(
                base=block[0].value.strip(),
                cycle_1_feature=block_setting_value_by_prefix(
                    block, _BASE_FEATURE_SETTING_START
                ).strip(),
                positive_means_base=parse_cellprofiler_bool(
                    block_setting_value_by_prefix(block, _BASE_POSITIVE_SETTING_START)
                ),
            )
            for block in repeating_setting_blocks(
                tuple(
                    setting
                    for setting in module.iter_settings()
                    if setting.name != _MINIMUM_SETTING
                ),
                start_name=_BASE_SETTING,
            )
        ),
        # The plugin's value for pipelines saved before it had the setting.
        minimum_positive_value=1.0 if minimum is None else parse_cellprofiler_float(minimum),
    )


def _matches_library(module: ModuleBlock) -> bool:
    # Pipelines saved before the plugin had the choice always match.
    choice = optional_setting_value(module, _MATCH_LIBRARY_SETTING)
    return choice is None or parse_cellprofiler_bool(choice)


@dataclass(frozen=True, slots=True)
class _BaseCallingBinding(MeasurementFeatureSettingBinding):
    """The calling a block describes; its measurements are the block's prior inputs."""

    def feature_names(self, module: ModuleBlock) -> tuple[str, ...]:
        return _calling_of(module).feature_names(
            parse_cellprofiler_int(required_setting_value(module, _CYCLES_SETTING))
        )

    def bind(
        self,
        module: ModuleBlock,
        kwargs: dict[str, CellProfilerSettingValue],
        binder: SettingsBinder,
    ) -> None:
        del binder
        kwargs[self.require_parameter_name()] = _calling_of(module)

    def records_from_kwargs(
        self, kwargs: Mapping[str, object]
    ) -> tuple[ModuleSetting, ...]:
        calling = kwargs.get(self.require_parameter_name())
        if not isinstance(calling, BaseCalling):
            return ()
        return tuple(ModuleSetting(name, value) for name, value in calling.setting_rows())


@dataclass(frozen=True, slots=True)
class _BarcodeLibraryBinding(SourceFileSettingBinding):
    """The library file named by CellProfiler's folder and file-name settings."""

    def bind(
        self,
        module: ModuleBlock,
        kwargs: dict[str, CellProfilerSettingValue],
        binder: SettingsBinder,
    ) -> None:
        if not _matches_library(module):
            return
        name = decode_cellprofiler_setting_literal(
            required_setting_value(module, self.setting_name)
        ).strip()
        choice, _, folder = decode_cellprofiler_setting_literal(
            module.get_setting(_LIBRARY_FOLDER_SETTING)
        ).partition("|")
        choice, folder = choice.strip(), folder.strip()
        if choice in ("Default Input Folder", ""):
            # CellProfiler's default input folder is where the pipeline's files are.
            location = name
        elif choice in ("Default Input Folder sub-folder", "Elsewhere..."):
            separator = "\\" if "\\" in folder and "/" not in folder else "/"
            location = folder.rstrip("/\\") + separator + name if folder else name
        else:
            raise ValueError(
                f"CallBarcodes cannot read its barcode library from {choice!r}; "
                "name a folder of input files."
            )
        kwargs[self.require_parameter_name()] = binder.resolve_source_file(location)

    def records_from_kwargs(
        self, kwargs: Mapping[str, object]
    ) -> tuple[ModuleSetting, ...]:
        library = kwargs.get(self.require_parameter_name())
        if library is None:
            return (ModuleSetting(_MATCH_LIBRARY_SETTING, "No"),)
        return (
            ModuleSetting(_MATCH_LIBRARY_SETTING, "Yes"),
            ModuleSetting(setting_names(self.setting_name)[0], str(library)),
        )


class _ObjectNameRuntimeParameter(KeywordRuntimeParameter):
    """Name of the objects whose barcodes are called."""

    parameter_name = "object_name"
    annotation_type = str
    parameter_default = ""


class _MeasurementValuesRuntimeParameter(KeywordRuntimeParameter):
    """The measurements the calling reads, one array of object values per name."""

    parameter_name = "measurement_values"
    annotation_type = tuple[np.ndarray, ...]
    parameter_default = ()


class CallBarcodesInputPolicy(
    ObjectLabelDrivenPrimaryImageInputPolicy,
    LabelsObjectInputPolicy,
):
    """Bind the objects, their name and the measurements their calling reads."""

    @classmethod
    def bind_runtime_inputs(
        cls,
        request: RuntimeInputBindingRequest,
    ) -> dict[str, RuntimeCallableArgument]:
        bound = super().bind_runtime_inputs(request)
        object_spec = request.object_inputs[0]
        labels = request.label_payload_for(object_spec)
        parameters = inspect.signature(call_barcodes).parameters
        calling = request.kwargs["calling"]
        cycles = request.kwargs.get("cycles", parameters["cycles"].default)
        return {
            **bound,
            _ObjectNameRuntimeParameter.require_parameter_name(): object_spec.name,
            _MeasurementValuesRuntimeParameter.require_parameter_name(): tuple(
                CellProfilerObjectMeasurementVectorBinding.for_object(
                    request,
                    object_ref=object_spec,
                    feature_name=feature_name,
                    labels=labels,
                )
                .vector()
                .runtime_value
                for feature_name in calling.feature_names(cycles)
            ),
        }


class CallBarcodesModule(
    NoObjectNameMeasurementRecordMixin,
    CallBarcodesInputPolicy,
    ObjectArtifactInputModule,
    PriorMeasurementArtifactInputModule,
    ObjectMeasurementArtifactOutputModule,
):
    module_name = "CallBarcodes"
    function_name = "call_barcodes"
    validated = True
    measurement_category_prefixes = (("barcode",),)
    input_objects_binding = SettingToKeywordBinding.input(
        "Input object name", ObjectLabelsArtifactType, runtime_parameter_name="labels"
    )
    calling_binding = _BaseCallingBinding(_CYCLE_1_FEATURE_SETTING, "calling")
    library_binding = _BarcodeLibraryBinding("Name of the file", "barcode_library")
    # The second wording of each pair is the one earlier plugin versions saved.
    retain_call_image_setting = SettingNameFamily(
        "Retain an image of the barcodes color coded by match?",
        aliases=("Retain an image of the barcodes color coded by call?",),
    )
    retain_score_image_setting = SettingNameFamily(
        "Retain an image of the barcodes color coded by score match?"
    )
    call_image_binding = SettingToKeywordBinding.output(
        "Enter the called barcode image name", ImageArtifactType
    )
    score_image_binding = SettingToKeywordBinding.output(
        "Enter the barcode score image name", ImageArtifactType
    )
    setting_bindings: ClassVar[tuple[SettingToKeywordBinding, ...]] = (
        SettingToKeywordBinding(_CYCLES_SETTING, "cycles", parse_cellprofiler_int),
        input_objects_binding,
        calling_binding,
        library_binding,
        SettingToKeywordBinding(
            SettingNameFamily(
                "Select the column containing barcodes to match against",
                aliases=("Select the column of barcodes to match against",),
            ),
            "barcode_column",
            str,
        ),
        SettingToKeywordBinding(
            SettingNameFamily(
                "Select the column containing gene/transcript barcode names",
                aliases=("Select the column with gene/transcript barcode names",),
            ),
            "gene_column",
            str,
        ),
        SettingToKeywordBinding(
            retain_call_image_setting, "retain_call_image", parse_cellprofiler_bool
        ),
        call_image_binding,
        SettingToKeywordBinding(
            retain_score_image_setting, "retain_score_image", parse_cellprofiler_bool
        ),
        score_image_binding,
        SettingToKeywordBinding(
            "What is the empty vector sequence?", "empty_vector_barcode", str
        ),
    )

    @classmethod
    def postprocess_bound_settings(
        cls, module: ModuleBlock, bound: BoundModuleSettings
    ) -> BoundModuleSettings:
        kwargs = dict(bound.kwargs)
        has_empty_vector = optional_setting_value(module, _HAS_EMPTY_VECTOR_SETTING)
        if has_empty_vector is None or not parse_cellprofiler_bool(has_empty_vector):
            kwargs["empty_vector_barcode"] = None
        if not _matches_library(module):
            # Without a library the plugin shows none of these and makes no image.
            kwargs["retain_call_image"] = False
            kwargs["retain_score_image"] = False
            kwargs["empty_vector_barcode"] = None
            kwargs.pop("barcode_column", None)
            kwargs.pop("gene_column", None)
        # Read by the calling and library bindings above. Each base's rows are
        # worded per base ("Select the first measurement indicating that A is
        # encoded"), so they are consumed by whatever name the block gives them.
        base_rows = tuple(
            setting.name
            for block in repeating_setting_blocks(
                tuple(
                    setting
                    for setting in module.iter_settings()
                    if setting.name != _MINIMUM_SETTING
                ),
                start_name=_BASE_SETTING,
            )
            for setting in block
        )
        return bound.with_replaced_kwargs(kwargs).with_consumed_settings(
            _ENCODING_SETTING,
            _MINIMUM_SETTING,
            _MATCH_LIBRARY_SETTING,
            _LIBRARY_FOLDER_SETTING,
            _HAS_EMPTY_VECTOR_SETTING,
            *base_rows,
        )

    @classmethod
    def active_artifact_bindings(
        cls,
        module: ModuleBlock | None = None,
        *,
        invocation_key: FunctionInvocationKey | None = None,
    ) -> tuple[SettingToKeywordBinding, ...]:
        """An image is an output only when the block retains it."""
        bindings = super().active_artifact_bindings(
            module, invocation_key=invocation_key
        )
        if module is None:
            return bindings
        retained = {
            cls.call_image_binding: cls.retain_call_image_setting,
            cls.score_image_binding: cls.retain_score_image_setting,
        }
        return tuple(
            binding
            for binding in bindings
            if binding not in retained
            or (
                _matches_library(module)
                and (value := optional_setting_value(module, retained[binding]))
                is not None
                and parse_cellprofiler_bool(value)
            )
        )


def _row_field(name: str) -> FieldSpec:
    return FieldSpec(name, _MEASUREMENT_TYPES[name], required=False)


_OBJECT_NAME = MeasurementRowAxisField.OBJECT_NAME.value
_OBJECT_LABEL = MeasurementRowAxisField.OBJECT_LABEL.value
_SLICE_INDEX = MeasurementRowAxisField.SLICE_INDEX.value
_CALLED = "Barcode_BarcodeCalled"
_MATCHED_BARCODE = "Barcode_MatchedTo_Barcode"
_MATCHED_ID = "Barcode_MatchedTo_ID"
_MATCHED_GENE = "Barcode_MatchedTo_GeneCode"
_MATCHED_SCORE = "Barcode_MatchedTo_Score"
_MEAN_QUALITY = "Barcode_MeanQualityScore"
_MEAN_SCORE = "Barcode_MeanBarcodeScore"
_MEASUREMENT_TYPES: dict[str, type] = {
    _SLICE_INDEX: int,
    _OBJECT_NAME: str,
    _OBJECT_LABEL: int,
    _CALLED: str,
    _MATCHED_BARCODE: str,
    _MATCHED_ID: int,
    _MATCHED_GENE: str,
    _MATCHED_SCORE: float,
    _MEAN_QUALITY: float,
    _MEAN_SCORE: float,
}


@numpy(contract=Pure2DContract)
@special_inputs("labels")
@runtime_bound_parameters(
    _ObjectNameRuntimeParameter,
    _MeasurementValuesRuntimeParameter,
    SliceIndexRuntimeParameter,
)
def call_barcodes(
    image: ImagePayload,
    labels: ObjectLabelValue,
    calling: BaseCalling,
    object_name: str = "",
    measurement_values: tuple[np.ndarray, ...] = (),
    cycles: int = 8,
    barcode_library: PlateInputFile | None = None,
    barcode_column: str = "",
    gene_column: str = "",
    empty_vector_barcode: str | None = None,
    retain_call_image: bool = False,
    retain_score_image: bool = False,
    slice_index: int = 0,
) -> tuple[ImagePayload | AlignedImageStack, MeasurementSparseColumnarRows]:
    """Read each object's barcode from its per-cycle measurements and look it up.

    For sequencing by synthesis: one base is called per cycle, the bases of all
    cycles form the object's barcode, and the barcode is matched to a library
    of known barcodes read from a CSV file.

    Measurements written, with CellProfiler's names. Per object:
    ``Barcode_BarcodeCalled``; with ``BrightestBase`` calling
    ``Barcode_MeanQualityScore`` (mean over cycles of the brightest value's
    share of the cycle's sum); with a library ``Barcode_MatchedTo_Barcode``,
    ``Barcode_MatchedTo_ID`` (the barcode's position among the library rows
    that have a barcode, from 1), ``Barcode_MatchedTo_GeneCode`` and
    ``Barcode_MatchedTo_Score`` (share of matching bases). Per image:
    ``Barcode_MeanQualityScore`` and, with a library,
    ``Barcode_MeanBarcodeScore``.

    The plugin's behaviour is kept, including:

    - Library barcodes are cut to the number of cycles. Of several barcodes
      with the same start the last one is matched, of several equally close
      barcodes the last one, and a barcode listed twice has the later row's
      position and gene.
    - A cycle without signal scores NaN, which makes the object's and the
      image's mean quality NaN; its base is called ``A``.
    - Images hold whole numbers as unsigned 16-bit, not intensities from 0 to
      1: the matched position, and 65535 times the match score rounded down.
    - Objects are taken to be numbered 1 to N in measurement order.
    - Without objects the images are zero, the image means are 0 and no object
      measurement is written (the plugin writes empty columns); the plugin's
      zero images take CellProfiler's label storage type, here they are
      unsigned 16-bit like the others.
    - ``BasesOverThreshold`` calling fails in the plugin unless the objects
      are named ``Foci``, and so does a library barcode shorter than the
      number of cycles when no barcode matches exactly; both are refused.

    One difference: with ``BrightestBase`` calling the plugin takes every
    measurement of the objects whose name contains the text before ``Cycle``;
    here the four measurements per cycle are the first cycle's with the cycle
    number and the base letter (A, C, G, T) replaced.

    Args:
        labels: The objects (such as sequencing foci) whose barcodes are called.
        calling: How a base is read in each cycle: ``BrightestBase`` from the
            largest of four measurements, ``BasesOverThreshold`` from
            thresholded measurements.
        cycles: Number of sequencing cycles, the length of a called barcode.
        barcode_library: CSV file of known barcodes. Without it barcodes are
            called but not matched and no image is made.
        barcode_column: Column of the library holding the barcodes.
        gene_column: Column of the library holding each barcode's gene or
            transcript name.
        empty_vector_barcode: Barcode of the empty vector, added to the library
            under the gene name ``EmptyVector``.
        retain_call_image: Make an image in which each object has its matched
            barcode's position in the library.
        retain_score_image: Make an image in which each object has its match
            score.
    """
    called, quality = calling.barcodes(measurement_values, cycles, object_name)
    object_numbers = range(1, len(called) + 1)
    object_rows: list[dict[str, object]] = [
        {
            _OBJECT_NAME: object_name,
            _OBJECT_LABEL: number,
            _SLICE_INDEX: slice_index,
            _CALLED: barcode,
        }
        for number, barcode in zip(object_numbers, called)
    ]
    image_row: dict[str, object] = {_SLICE_INDEX: slice_index}
    if quality is not None:
        for row, score in zip(object_rows, quality):
            row[_MEAN_QUALITY] = float(score)
        image_row[_MEAN_QUALITY] = float(np.mean(quality)) if called else 0.0

    retained: list[ImagePayload] = []
    if barcode_library is not None:
        label_plane = object_label_dense_array(labels, dtype=np.int32)
        call_pixels = label_plane.astype(np.int64)
        score_pixels = label_plane.astype(np.float64)
        scores = []
        if called:
            library = BarcodeLibrary.read(
                barcode_library,
                barcode_column=barcode_column,
                gene_column=gene_column,
                empty_vector_barcode=empty_vector_barcode,
            )
            for number, barcode, row in zip(object_numbers, called, object_rows):
                score, matched = library.closest(barcode)
                position, gene = library.entries[matched]
                scores.append(score)
                row[_MATCHED_BARCODE] = matched
                row[_MATCHED_ID] = position
                row[_MATCHED_GENE] = gene
                row[_MATCHED_SCORE] = float(score)
                call_pixels[label_plane == number] = position
                score_pixels[label_plane == number] = 65535 * score
        else:
            call_pixels[:] = 0
            score_pixels[:] = 0
        image_row[_MEAN_SCORE] = float(np.mean(scores)) if called else 0.0
        if retain_call_image:
            retained.append(image.with_pixels(call_pixels.astype(np.uint16)))
        if retain_score_image:
            retained.append(image.with_pixels(score_pixels.astype(np.uint16)))

    rows = [*object_rows, *([image_row] if len(image_row) > 1 else [])]
    names = dict.fromkeys(name for row in rows for name in row)
    return (
        pack_aligned_image_outputs(tuple(retained)) if retained else image,
        MeasurementSparseColumnarRows.from_rows(
            rows, fields=tuple(_row_field(name) for name in names)
        ),
    )
