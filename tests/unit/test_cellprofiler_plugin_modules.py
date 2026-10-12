"""CellProfiler plugin modules reproduce the plugins themselves.

``tests/fixtures/cellprofiler_plugins`` holds a pipeline of plugin blocks
(``cases.cppipe``; a block's first note is its case name) and what the real
plugins, run by CellProfiler 4.2.8.1, added to their workspace for each block:
images, object sets and measurements (``reference.npz``; versions, plugin commit
and the blocks the plugin itself fails on are in ``reference.json``).
``make_reference.py`` there regenerates both. The same blocks are bound and
executed here.
"""

from __future__ import annotations

import ast
import inspect
import json
import shutil
from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import numpy as np
import pytest

from openhcs.core.aligned_image_payload import AlignedImageStack
from openhcs.core.artifacts.kinds import ImageArtifactType, ObjectLabelsArtifactType
from openhcs.core.artifacts.plans import ArtifactInputPlan, ArtifactOutputPlan
from openhcs.core.artifacts.specs import ArtifactSpec, ArtifactSpecCollection
from openhcs.core.callable_contract import CallableContract
from openhcs.core.config import StepSourceBindingsConfig
from openhcs.core.function_patterns import normalize_function_pattern
from openhcs.core.image_payload_execution_mode import NaturalExecution
from openhcs.core.runtime_image_values import ImagePayload, ImagePayloadMetadata
from openhcs.core.runtime_measurements import (
    MeasurementRowAxisField,
    MeasurementRowValueField,
)
from openhcs.core.runtime_object_labels import (
    ObjectLabelPayload,
    ObjectLabelValue,
    ObjectLabelVariantData,
    object_label_dense_array,
)
from openhcs.core.runtime_plane_projection import NoPlaneAxis, RuntimeSlicePlaneAxis
from openhcs.core.runtime_relationships import DirectedObjectRelationshipPayload
from openhcs.core.runtime_tabular_values import ColumnarRows
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_spatial_domain import (
    SourceSpatialDomain,
    VolumeSourceSpatialDomain,
)
from openhcs.domains.microscopy.axes import Microscopy
from openhcs.interop.cellprofiler.measurement_lookup import ObjectCountFeatureName
from openhcs.interop.cellprofiler.module_artifact_declarations import (
    ObjectArtifactOutputModule,
    PriorMeasurementArtifactInputModule,
)
from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.interop.cellprofiler.parser import CPPipeParser, ModuleBlock
from openhcs.interop.cellprofiler.pipeline_import import import_cellprofiler_pipeline
from openhcs.interop.cellprofiler.runtime.adapter import CellProfilerRuntimeAdapter
from openhcs.interop.cellprofiler.runtime.function_contract_execution import (
    CellProfilerFunctionContractExecutor,
)
from openhcs.interop.cellprofiler.settings_binder import SettingsBinder
from openhcs.processing.backends.cellprofiler.call_barcodes import BrightestBase
from openhcs.processing.backends.cellprofiler.compensate_colors import (
    MatchAfterMasking,
)
from openhcs.processing.backends.cellprofiler.measure_radial_entropy import (
    IntegratedIntensity,
)

_FIXTURES = Path(__file__).parents[1] / "fixtures" / "cellprofiler_plugins"
_REFERENCE = np.load(_FIXTURES / "reference.npz")
_REFERENCE_FACTS = json.loads((_FIXTURES / "reference.json").read_text())
_PLUGIN_RAISED = _REFERENCE_FACTS["plugin_raised"]
# scikit-image 0.26 against CellProfiler's 0.18.3: global equalization differs by
# up to 4.2e-7 (float32 rounding); every other case is bit-identical.
_TOLERANCE = 1e-6
# Where the plugin's image type is an accident of CellProfiler's storage: its
# images of no objects are its label array, which CellProfiler keeps as int8.
_IMAGE_TYPE_NOT_COMPARED = {"BarcodesOfNoObjects"}
_OBJECT_NAME = MeasurementRowAxisField.OBJECT_NAME.value
_OBJECT_LABEL = MeasurementRowAxisField.OBJECT_LABEL.value
_SLICE_INDEX = MeasurementRowAxisField.SLICE_INDEX.value
_FEATURE_NAME = MeasurementRowAxisField.FEATURE_NAME.value
_RESULT_VALUE = MeasurementRowValueField.RESULT_VALUE.value
# CellProfiler gives every object set a column of its objects' own numbers. Here
# that number is the object label each measurement row carries, not a feature.
_OBJECT_NUMBER_FEATURE = "Number_Object_Number"

_CASES = {
    ast.literal_eval(block.metadata["notes"])[0]: block
    for block in CPPipeParser().parse(_FIXTURES / "cases.cppipe")
}


def _artifact_names(
    block: ModuleBlock,
    plan_type: type[ArtifactInputPlan | ArtifactOutputPlan],
    artifact_type: type = ImageArtifactType,
) -> dict[str | None, tuple[str, ...]]:
    """Names a block declares of one kind, keyed by the function parameter they feed."""
    module_type = CellProfilerModule.require_module(block.name)
    declared: dict[str | None, tuple[str, ...]] = {}
    for binding in module_type.artifact_bindings_for(block, plan_type=plan_type):
        if binding.require_artifact_type() is artifact_type:
            declared[binding.runtime_parameter_name] = (
                *declared.get(binding.runtime_parameter_name, ()),
                *module_type.artifact_names_for_binding(block, binding),
            )
    return declared


def _image(pixels: np.ndarray, *, volume: bool, stacked: bool = False) -> ImagePayload:
    return ImagePayloadMetadata(
        source_voxel_spacing=SourceVoxelSpacing(
            values_zyx=_REFERENCE_FACTS["voxel_spacing_zyx_of_volumes"] if volume else ()
        ),
        source_spatial_domain=(
            VolumeSourceSpatialDomain() if volume else SourceSpatialDomain()
        ),
        plane_axis=RuntimeSlicePlaneAxis if stacked else NoPlaneAxis,
    ).payload_with(pixels, None)


def _run(block: ModuleBlock, image: ImagePayload) -> object:
    """Bind the block's settings and run its function the way the runtime does.

    This stands in for the runtime's input binding: named images and objects
    come from the reference inputs, and a function that reads prior measurements
    of its objects gets ``object_name`` and one ``measurement_values`` array per
    measurement its module declares. A module with a function for volumes runs
    that one on a volume.
    """
    module_type = CellProfilerModule.require_module(block.name)
    volume = isinstance(image.metadata.source_spatial_domain, VolumeSourceSpatialDomain)
    function = module_type.resolve_function(
        block,
        contract=CallableContract.from_callable(module_type.require_callable()),
        source_bindings=StepSourceBindingsConfig(
            source_stack_components=(Microscopy.ZIndex,) if volume else ()
        ),
    )
    contract = replace(
        CallableContract.from_callable(function).with_prepared_signature(),
        runtime_adapter=CellProfilerRuntimeAdapter.runtime_adapter_spec(),
    )
    named_at_compile_time = module_type.compile_time_parameter_names(contract)
    kwargs = {
        name: value
        for name, value in module_type.bind_settings(
            block, binder=SettingsBinder(source_root=_FIXTURES)
        ).kwargs.items()
        if name not in named_at_compile_time
    }
    for parameter, names in _artifact_names(block, ArtifactInputPlan).items():
        if parameter is not None and names:
            (name,) = names
            kwargs[parameter] = _REFERENCE[f"input/image/{name}"]
    object_names = _artifact_names(block, ArtifactInputPlan, ObjectLabelsArtifactType)
    for parameter, names in object_names.items():
        (name,) = names
        kwargs[parameter] = ObjectLabelPayload(
            variant_data=ObjectLabelVariantData(
                labels=_REFERENCE[f"input/objects/{name}"]
            )
        )
    if issubclass(module_type, PriorMeasurementArtifactInputModule):
        ((object_name,),) = object_names.values()
        kwargs["object_name"] = object_name
        kwargs["measurement_values"] = tuple(
            _REFERENCE[f"input/measurement/{object_name}/{feature}"]
            for feature in module_type.prior_measurement_feature_names(block)
        )
    assert set(kwargs) <= set(inspect.signature(function).parameters)
    return CellProfilerFunctionContractExecutor().execute(
        contract,
        contract.resolve_canonical_raw_callable(),
        image,
        kwargs,
        execution_mode=contract.runtime_image_execution_mode or NaturalExecution,
    )


def _main_image(block: ModuleBlock) -> np.ndarray:
    """The block's unnamed input image; a blank plane where it has objects only.

    Several unnamed input images are stacked in the order the block names them.
    """
    names = _artifact_names(block, ArtifactInputPlan).get(None)
    if names:
        images = [_REFERENCE[f"input/image/{name}"] for name in names]
        return images[0] if len(images) == 1 else np.stack(images)
    ((name,), *_) = _artifact_names(
        block, ArtifactInputPlan, ObjectLabelsArtifactType
    ).values()
    return np.zeros(_REFERENCE[f"input/objects/{name}"].shape, dtype=np.float32)


def _main_images_are_volumes(block: ModuleBlock) -> bool:
    """Whether the unnamed input images, or else the objects, are volumes."""
    names = _artifact_names(block, ArtifactInputPlan).get(None, ())
    if not names:
        return _main_image(block).ndim == 3
    return any(_REFERENCE[f"input/image/{name}"].ndim == 3 for name in names)


def _measurements(rows: ColumnarRows) -> dict[str, np.ndarray]:
    """Measurement rows as CellProfiler stores them: ``<object>/<feature>`` arrays.

    Rows naming an object give one value per object in label order; rows naming
    none are the image's measurements.
    """
    axes = (_OBJECT_NAME, _OBJECT_LABEL, _SLICE_INDEX)
    per_object: dict[str, dict[int, object]] = {}
    stored: dict[str, np.ndarray] = {}
    for row in rows.row_mappings():
        present = {
            name: value
            for name, value in row.items()
            if value is not getattr(rows, "missing_cell", None)
        }
        for feature, value in present.items():
            if feature in axes:
                continue
            if _OBJECT_NAME in present:
                per_object.setdefault(f"{present[_OBJECT_NAME]}/{feature}", {})[
                    present[_OBJECT_LABEL]
                ] = value
            else:
                assert f"Image/{feature}" not in stored
                stored[f"Image/{feature}"] = np.asarray(value)
    for key, by_label in per_object.items():
        assert sorted(by_label) == list(range(1, len(by_label) + 1))
        stored[key] = np.asarray([by_label[label] for label in sorted(by_label)])
    return stored


def _by_object_label(values: dict[int, object]) -> np.ndarray:
    """One value per object in label order; the labels must be 1 to their count."""
    assert sorted(values) == list(range(1, len(values) + 1))
    return np.asarray([values[label] for label in sorted(values)])


def _measured_when_recorded(
    module_type: type[ObjectArtifactOutputModule], name: str, labels: ObjectLabelValue
) -> dict[str, np.ndarray]:
    """The count and locations a module's family measures of an object set.

    The runtime measures them from the labels a function returned when it
    records them (``ObjectArtifactOutputModule.measurement_record_rows``); the
    function itself returns none. This makes the same rows for one object set.
    """
    location_rows = module_type.object_location_measurement_row_type()(
        labels, object_name=name
    )
    count = sum(len(ids) for _plane, ids in location_rows.label_plane_domains())
    stored = {
        f"Image/{ObjectCountFeatureName.feature(name).name}": np.asarray(float(count))
    }
    by_feature: dict[str, dict[int, object]] = {}
    for row in location_rows.rows().row_mappings():
        by_feature.setdefault(row[_FEATURE_NAME], {})[row[_OBJECT_LABEL]] = row[
            _RESULT_VALUE
        ]
    for feature, values in by_feature.items():
        stored[f"{name}/{feature}"] = _by_object_label(values)
    return stored


def _parents_and_children(
    relationship: DirectedObjectRelationshipPayload,
    parent_name: str,
    parent_labels: np.ndarray,
    child_name: str,
) -> dict[str, np.ndarray]:
    """A returned parent-child relationship as CellProfiler's two columns.

    Each child's parent, and each parent's number of children (0 where none).
    """
    stored: dict[str, np.ndarray] = {}
    if relationship.target_ids:
        stored[f"{child_name}/Parent_{parent_name}"] = _by_object_label(
            dict(zip(relationship.target_ids, relationship.source_ids))
        )
    if parent_labels.max(initial=0):
        stored[f"{parent_name}/Children_{child_name}_Count"] = np.bincount(
            relationship.source_ids, minlength=int(parent_labels.max()) + 1
        )[1:]
    return stored


def _rows_as_recorded(block: ModuleBlock, rows: ColumnarRows) -> ColumnarRows:
    """A function's rows under the names its module records them with.

    A module may rename its function's rows when they are recorded
    (``measurement_row_projection_types``), from what the record request says
    about the block: here its input images and objects. This stands in for the
    request with the inputs the block declares.
    """
    module_type = CellProfilerModule.require_module(block.name)
    request = SimpleNamespace(
        callable_contract=SimpleNamespace(
            artifact_inputs=ArtifactSpecCollection(
                ArtifactSpec(name, artifact_type, parameter_name=parameter)
                for artifact_type in (ImageArtifactType, ObjectLabelsArtifactType)
                for parameter, names in _artifact_names(
                    block, ArtifactInputPlan, artifact_type
                ).items()
                for name in names
            )
        )
    )
    for projection_type in module_type.measurement_row_projection_types():
        request.output_value = rows
        rows = projection_type.for_request(module_type, request).rows()
    return rows


def _outputs(block: ModuleBlock, result: object) -> dict[str, np.ndarray]:
    """What a block's function returned, keyed like the reference's case entries.

    For a module of the family that measures the objects it makes, the family's
    measurements of the returned objects are included.
    """
    module_type = CellProfilerModule.require_module(block.name)
    image_names = _artifact_names(block, ArtifactOutputPlan).get(None, ())
    object_names = _artifact_names(
        block, ArtifactOutputPlan, ObjectLabelsArtifactType
    ).get(None, ())
    main, *others = result if isinstance(result, tuple) else (result,)
    stored: dict[str, np.ndarray] = {}
    if image_names:
        images = main.slices if isinstance(main, AlignedImageStack) else (main,)
        assert len(images) == len(image_names)
        for name, image in zip(image_names, images):
            stored[f"image/{name}"] = np.asarray(image.data)
    object_sets = [value for value in others if isinstance(value, ObjectLabelValue)]
    assert len(object_sets) == len(object_names)
    for name, labels in zip(object_names, object_sets):
        stored[f"objects/{name}"] = object_label_dense_array(labels, dtype=np.int32)
        if issubclass(module_type, ObjectArtifactOutputModule):
            for key, values in _measured_when_recorded(
                module_type, name, labels
            ).items():
                stored[f"measurement/{key}"] = values
    for relationship in others:
        if isinstance(relationship, DirectedObjectRelationshipPayload):
            ((parent_name,),) = _artifact_names(
                block, ArtifactInputPlan, ObjectLabelsArtifactType
            ).values()
            (child_name,) = object_names
            for key, values in _parents_and_children(
                relationship,
                parent_name,
                _REFERENCE[f"input/objects/{parent_name}"],
                child_name,
            ).items():
                stored[f"measurement/{key}"] = values
    for rows in (value for value in others if isinstance(value, ColumnarRows)):
        for key, values in _measurements(_rows_as_recorded(block, rows)).items():
            stored[f"measurement/{key}"] = values
    return stored


def _execute(block: ModuleBlock, image: ImagePayload) -> np.ndarray:
    """The pixels of a block with one output image."""
    ((name,),) = _artifact_names(block, ArtifactOutputPlan).values()
    return _outputs(block, _run(block, image))[f"image/{name}"]


@pytest.mark.parametrize("case", sorted(_CASES))
def test_outputs_equal_what_the_plugin_stored(case: str) -> None:
    block = _CASES[case]
    image = _image(_main_image(block), volume=_main_images_are_volumes(block))

    if case in _PLUGIN_RAISED:
        with pytest.raises(ValueError, match="the CellProfiler plugin fails"):
            _run(block, image)
        return

    # The plugin writes an empty column per object measurement when there are
    # no objects; here no object rows exist then.
    expected = {
        key.removeprefix(f"{case}/"): _REFERENCE[key]
        for key in _REFERENCE.files
        if key.startswith(f"{case}/")
        and _REFERENCE[key].shape != (0,)
        and not key.endswith(f"/{_OBJECT_NUMBER_FEATURE}")
    }
    actual = _outputs(block, _run(block, image))
    assert sorted(actual) == sorted(expected)
    for key, stored in expected.items():
        if key.startswith("image/") and case not in _IMAGE_TYPE_NOT_COMPARED:
            assert actual[key].dtype == stored.dtype
        if stored.dtype.kind in "US":
            np.testing.assert_array_equal(actual[key], stored)
        else:
            np.testing.assert_allclose(
                actual[key], stored, rtol=0, atol=_TOLERANCE, err_msg=key
            )


@pytest.mark.parametrize(
    "output_name",
    ("EqualizedPlaneWithinMask", "RescaledPlaneDistance", "PlaneMatchedToReference"),
)
def test_each_image_of_a_stack_is_processed_on_its_own(output_name: str) -> None:
    block = _CASES[output_name]
    pixels = _main_image(block)
    other = np.ascontiguousarray(pixels[::-1, ::-1])

    stacked = _execute(
        block, _image(np.stack((pixels, other)), volume=False, stacked=True)
    )

    np.testing.assert_array_equal(
        stacked,
        np.stack(
            [_execute(block, _image(one, volume=False)) for one in (pixels, other)]
        ),
    )


@pytest.mark.parametrize(
    ("case", "inputs", "outputs"),
    (
        ("EqualizedPlane", {None: ("Plane",), "mask_image": ()}, ("EqualizedPlane",)),
        (
            "EqualizedPlaneWithinMask",
            {None: ("Plane",), "mask_image": ("MaskPlane",)},
            ("EqualizedPlaneWithinMask",),
        ),
        ("PlaneDistance", {None: ("BinaryPlane",)}, ("PlaneDistance",)),
        (
            "PlaneMatchedToReference",
            {None: ("Plane",), "reference": ("ReferencePlane",)},
            ("PlaneMatchedToReference",),
        ),
        # CellProfiler's blank value names no image.
        (
            "VolumeMatchedToFrame",
            {None: ("Volume",), "reference": ()},
            ("VolumeMatchedToFrame",),
        ),
        # An image is an output only when the block retains it.
        (
            "BarcodesMatchedToLibrary",
            {"labels": ("Foci",)},
            ("BarcodeCalls", "BarcodeScores"),
        ),
        ("BarcodesWithEmptyVector", {"labels": ("Foci",)}, ("BarcodeCalls",)),
        ("BarcodesCalledByThreshold", {"labels": ("Foci",)}, ("BarcodeScores",)),
        # Without a library the plugin makes no image, whatever the block retains.
        ("BarcodesWithoutLibrary", {"labels": ("Foci",)}, ()),
        # Objects are an input only where the block compensates within them.
        (
            "CompensatedThreeClasses",
            {None: ("Cycle01_A", "Cycle01_C", "Plane")},
            ("FirstClass", "LastClass", "MiddleClass"),
        ),
        (
            "CompensatedSpotsWithinFoci",
            {
                None: ("Cycle01_A", "Cycle02_A", "Cycle01_C", "Cycle02_C"),
                "labels": ("Foci",),
            },
            tuple(
                f"CompensatedSpotsWithinFoci_{name}"
                for name in ("Cycle01_A", "Cycle02_A", "Cycle01_C", "Cycle02_C")
            ),
        ),
        # The plugin uses the first of the object sets a block names.
        (
            "CompensatedWithinFirstOfTwoObjectSets",
            {None: ("Cycle01_A", "Cycle01_C"), "labels": ("Cells",)},
            tuple(
                f"CompensatedWithinFirstOfTwoObjectSets_{name}"
                for name in ("Cycle01_A", "Cycle01_C")
            ),
        ),
        ("DeclumpedByShape", {"labels": ("Clumps",)}, ("DeclumpedByShape",)),
        # The reference image is an input only where the block floods it.
        (
            "DeclumpedByIntensity",
            {"reference": ("Plane",), "labels": ("Clumps",)},
            ("DeclumpedByIntensity",),
        ),
        ("RadialEntropyOfMeans", {None: ("Plane",), "labels": ("Clumps",)}, ()),
    ),
)
def test_block_declares_its_input_and_output_images_and_objects(
    case: str,
    inputs: dict[str | None, tuple[str, ...]],
    outputs: tuple[str, ...],
) -> None:
    block = _CASES[case]

    assert {
        **_artifact_names(block, ArtifactInputPlan),
        **_artifact_names(block, ArtifactInputPlan, ObjectLabelsArtifactType),
    } == inputs
    assert (
        *_artifact_names(block, ArtifactOutputPlan).get(None, ()),
        *_artifact_names(block, ArtifactOutputPlan, ObjectLabelsArtifactType).get(
            None, ()
        ),
    ) == outputs


def test_block_declares_the_measurements_of_every_cycle_as_its_inputs() -> None:
    """One measurement of the first cycle stands for those of all cycles."""
    declared = {
        case: CellProfilerModule.require_module(
            _CASES[case].name
        ).prior_measurement_feature_names(_CASES[case])
        for case in ("BarcodesMatchedToLibrary", "BarcodesCalledByThreshold")
    }

    assert declared == {
        "BarcodesMatchedToLibrary": tuple(
            f"Intensity_MaxIntensity_CorrCycle{cycle:02d}_{base}"
            for cycle in (1, 2, 3)
            for base in "ACGT"
        ),
        "BarcodesCalledByThreshold": tuple(
            f"Intensity_{measurement}_CorrCycle{cycle:02d}_{base}"
            for measurement, base in (
                ("MaxIntensity", "A"),
                ("MeanIntensity", "A"),
                ("MaxIntensity", "C"),
                ("MaxIntensity", "G"),
                ("MaxIntensity", "T"),
            )
            for cycle in (1, 2, 3)
        ),
    }


_SOURCE = """CellProfiler Pipeline: http://www.cellprofiler.org
NamesAndTypes:[module_num:1|enabled:True]
    Assignments count:1
    Select the image type:Grayscale image
    Name to assign these images:{image}
    Select the rule criteria:and (file does contain "{image}")
"""

# Blocks below are verbatim from pipelines found in the wild, apart from the one
# noted change. They carry both spellings of the 3D setting and a fork's extra
# setting.

# CellProfiler/CellProfiler-plugins tests/headless_test/4.2.5_plugins_test_pipeline_BASIC.cppipe
_PLUGINS_TEST_PIPELINE = (
    _SOURCE.format(image="DNA")
    + """DistanceTransform:[module_num:7|svn_version:'Unknown'|variable_revision_number:1|show_window:True|notes:[]|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Select the input image:DNA
    Name the output image:DistanceTransform
    Rescale values from 0 to 1?:Yes

HistogramEqualization:[module_num:9|svn_version:'Unknown'|variable_revision_number:1|show_window:True|notes:[]|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Select the input image:DNA
    Name the output image:HistogramEqualization
    Bins:256
    Mask:Leave blank
    Local:Yes
    Tile Size:100
    Clip limit:0.01
    Is you image 3D?:No
    Do framewise calculation?:No
    Tile Size (Z):5

HistogramMatching:[module_num:10|svn_version:'Unknown'|variable_revision_number:1|show_window:True|notes:[]|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Select the input image:DNA
    Name the output image:HistogramMatching
    Is you image 3D?:No
    Use a frame within image as reference?:No
    Image to use as reference :None
    Frame number:5
"""
)

# Mas515/Image_analysis 1_Kuo_seg.cppipe
_KUO_SEGMENTATION_PIPELINE = (
    _SOURCE.format(image="GaussianFilterGFP")
    + """HistogramEqualization:[module_num:8|svn_version:'Unknown'|variable_revision_number:1|show_window:False|notes:['256 bin size']|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Select the input image:GaussianFilterGFP
    Name the output image:HistogramEqualizationGFP
    Bins:200
    Mask:Leave blank
    Local:Yes
    Tile Size:50
    Clip limit:0.01
    Is you image 3D?:Yes
    Do framewise calculation?:Yes
    Tile Size (Z):5
"""
)

# Mas515/Image_analysis 2_Kuotracked.cppipe
_KUO_TRACKING_PIPELINE = (
    _SOURCE.format(image="ImageAfterMathAF647Invert")
    + """DistanceTransform:[module_num:31|svn_version:'Unknown'|variable_revision_number:1|show_window:False|notes:[]|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Select the input image:ImageAfterMathAF647Invert
    Name the output image:DistanceTransformAF647
    Rescale values from 0 to 1?:No
"""
)

# TrynkaLab/tglow-pipeline assets/cellprofiler/CELL_DIVIDER/2d_v1.cppipe. The
# block is disabled there; it is enabled here so that it imports. The
# GaussianFilter block only provides the reference image.
_TGLOW_PIPELINE = (
    _SOURCE.format(image="ctv")
    + """GaussianFilter:[module_num:2|enabled:True]
    Select the input image:ctv
    Name the output image:actin
    Sigma:1

HistogramMatching:[module_num:9|svn_version:'Unknown'|variable_revision_number:1|show_window:False|notes:[]|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Select the input image:ctv
    Name the output image:ctv_eq
    Is your image 3D?:No
    Use a frame within image as reference?:No
    Image to use as reference :actin
    Frame number:5
    Plane number in 3d:0
"""
)

_CYCLE_IMAGES = tuple(
    f"CorrCycle{cycle:02d}_{base}" for cycle in range(1, 9) for base in "ACGT"
)

# broadinstitute/pooled-cell-painting-image-processing qc/QC_EightCycle.cppipe at
# 47067a480bebc55b8247652c38f5d645db83ef85, module 36. The folder of the barcode
# file is the author's (Elsewhere...|/Users/eweisbar/Documents/projects/PERISCOPE)
# there and the default input folder here; the notes are left out. The blocks
# before it stand for the pipeline's 34 modules that make the foci and measure
# them in every cycle's four images.
_POOLED_SCREEN_PIPELINE = (
    "CellProfiler Pipeline: http://www.cellprofiler.org\n"
    "NamesAndTypes:[module_num:1|enabled:True]\n"
    f"    Assignments count:{len(_CYCLE_IMAGES)}\n"
    + "".join(
        "    Select the image type:Grayscale image\n"
        f"    Name to assign these images:{name}\n"
        f'    Select the rule criteria:and (file does contain "{name}")\n'
        for name in _CYCLE_IMAGES
    )
    + f"""IdentifyPrimaryObjects:[module_num:2|enabled:True]
    Select the input image:CorrCycle01_A
    Name the primary objects to be identified:Foci
MeasureObjectIntensity:[module_num:3|enabled:True]
    Select images to measure:{", ".join(_CYCLE_IMAGES)}
    Select object sets to measure:Foci
CallBarcodes:[module_num:36|svn_version:'Unknown'|variable_revision_number:1|show_window:False|notes:[]|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Number of cycles:8
    Input object name:Foci
    Select one of the measures from Cycle 1 to use for calling:Intensity_MaxIntensity_CorrCycle01_A
    Input data file location:Default Input Folder|
    Name of the file:Barcodes.csv
    Select the column of barcodes to match against:sgRNA
    Select the column with gene/transcript barcode names:gene_symbol
    Retain an image of the barcodes color coded by call?:Yes
    Enter the called barcode image name:Barcodes_IntValues
    Retain an image of the barcodes color coded by score match?:Yes
    Enter the barcode score image name:BarcodeScores_IntValues
    Do you have an empty vector barcode you would like to add to the barcode list?:No
    What is the empty vector sequence?:AAAAAAAAAAAAAAA
"""
)

_BACKGROUND_SUBTRACTED_IMAGES = tuple(
    f"Cycle{cycle:02d}_{base}_BackSub" for base in "ACGT" for cycle in range(1, 9)
)

# broadinstitute/pooled-cell-painting-image-processing qc/QC_EightCycle.cppipe at
# 47067a480bebc55b8247652c38f5d645db83ef85, module 34, unchanged. The blocks
# before it stand for the pipeline's modules that make the background-subtracted
# images of every cycle and the foci.
_POOLED_SCREEN_COMPENSATION_PIPELINE = (
    "CellProfiler Pipeline: http://www.cellprofiler.org\n"
    "NamesAndTypes:[module_num:1|enabled:True]\n"
    f"    Assignments count:{len(_BACKGROUND_SUBTRACTED_IMAGES)}\n"
    + "".join(
        "    Select the image type:Grayscale image\n"
        f"    Name to assign these images:{name}\n"
        f'    Select the rule criteria:and (file does contain "{name}")\n'
        for name in _BACKGROUND_SUBTRACTED_IMAGES
    )
    + """IdentifyPrimaryObjects:[module_num:2|enabled:True]
    Select the input image:Cycle01_A_BackSub
    Name the primary objects to be identified:Foci
"""
    + """CompensateColors:[module_num:34|svn_version:'Unknown'|variable_revision_number:1|show_window:False|notes:['DO NOT EDIT', 'Uses parameters that have been optimized across many batches. Troubleshooting alrnative compensation parameters is outside the scope of this pipeline.']|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Hidden:32
    Hidden:1
    Select an image to measure:Cycle01_A_BackSub
    What compensation class does this image belong to?:1
    Select an output image name:CorrCycle01_A
    Select an image to measure:Cycle02_A_BackSub
    What compensation class does this image belong to?:1
    Select an output image name:CorrCycle02_A
    Select an image to measure:Cycle03_A_BackSub
    What compensation class does this image belong to?:1
    Select an output image name:CorrCycle03_A
    Select an image to measure:Cycle04_A_BackSub
    What compensation class does this image belong to?:1
    Select an output image name:CorrCycle04_A
    Select an image to measure:Cycle05_A_BackSub
    What compensation class does this image belong to?:1
    Select an output image name:CorrCycle05_A
    Select an image to measure:Cycle06_A_BackSub
    What compensation class does this image belong to?:1
    Select an output image name:CorrCycle06_A
    Select an image to measure:Cycle07_A_BackSub
    What compensation class does this image belong to?:1
    Select an output image name:CorrCycle07_A
    Select an image to measure:Cycle08_A_BackSub
    What compensation class does this image belong to?:1
    Select an output image name:CorrCycle08_A
    Select an image to measure:Cycle01_C_BackSub
    What compensation class does this image belong to?:2
    Select an output image name:CorrCycle01_C
    Select an image to measure:Cycle02_C_BackSub
    What compensation class does this image belong to?:2
    Select an output image name:CorrCycle02_C
    Select an image to measure:Cycle03_C_BackSub
    What compensation class does this image belong to?:2
    Select an output image name:CorrCycle03_C
    Select an image to measure:Cycle04_C_BackSub
    What compensation class does this image belong to?:2
    Select an output image name:CorrCycle04_C
    Select an image to measure:Cycle05_C_BackSub
    What compensation class does this image belong to?:2
    Select an output image name:CorrCycle05_C
    Select an image to measure:Cycle06_C_BackSub
    What compensation class does this image belong to?:2
    Select an output image name:CorrCycle06_C
    Select an image to measure:Cycle07_C_BackSub
    What compensation class does this image belong to?:2
    Select an output image name:CorrCycle07_C
    Select an image to measure:Cycle08_C_BackSub
    What compensation class does this image belong to?:2
    Select an output image name:CorrCycle08_C
    Select an image to measure:Cycle01_G_BackSub
    What compensation class does this image belong to?:3
    Select an output image name:CorrCycle01_G
    Select an image to measure:Cycle02_G_BackSub
    What compensation class does this image belong to?:3
    Select an output image name:CorrCycle02_G
    Select an image to measure:Cycle03_G_BackSub
    What compensation class does this image belong to?:3
    Select an output image name:CorrCycle03_G
    Select an image to measure:Cycle04_G_BackSub
    What compensation class does this image belong to?:3
    Select an output image name:CorrCycle04_G
    Select an image to measure:Cycle05_G_BackSub
    What compensation class does this image belong to?:3
    Select an output image name:CorrCycle05_G
    Select an image to measure:Cycle06_G_BackSub
    What compensation class does this image belong to?:3
    Select an output image name:CorrCycle06_G
    Select an image to measure:Cycle07_G_BackSub
    What compensation class does this image belong to?:3
    Select an output image name:CorrCycle07_G
    Select an image to measure:Cycle08_G_BackSub
    What compensation class does this image belong to?:3
    Select an output image name:CorrCycle08_G
    Select an image to measure:Cycle01_T_BackSub
    What compensation class does this image belong to?:4
    Select an output image name:CorrCycle01_T
    Select an image to measure:Cycle02_T_BackSub
    What compensation class does this image belong to?:4
    Select an output image name:CorrCycle02_T
    Select an image to measure:Cycle03_T_BackSub
    What compensation class does this image belong to?:4
    Select an output image name:CorrCycle03_T
    Select an image to measure:Cycle04_T_BackSub
    What compensation class does this image belong to?:4
    Select an output image name:CorrCycle04_T
    Select an image to measure:Cycle05_T_BackSub
    What compensation class does this image belong to?:4
    Select an output image name:CorrCycle05_T
    Select an image to measure:Cycle06_T_BackSub
    What compensation class does this image belong to?:4
    Select an output image name:CorrCycle06_T
    Select an image to measure:Cycle07_T_BackSub
    What compensation class does this image belong to?:4
    Select an output image name:CorrCycle07_T
    Select an image to measure:Cycle08_T_BackSub
    What compensation class does this image belong to?:4
    Select an output image name:CorrCycle08_T
    Select where to perform color compensation:Within objects
    Select an object to perform compensation within:Foci
    Should individual images be rescaled 0-1 before compensating pre-masking or on unmasked images?:No
    Should images be rescaled 0-1 before compensating but after masking to objects?:No
    Should histogram matching be performed between the image groups?:Yes, post-masking to objects
    What compensation class should serve as the template histogram?:4
    Should images be rescaled 0-1 after compensating?:No
    Should the images be divided by a scalar based on group percentiles:No
    What percentile should be used for multiplication:99.9
    Should the images have a tophat filter applied before correction?:No
    What size radius should be used for the tophat filter?:3
    Should the images have a Laplacian of Gaussian filter applied before correction?:Yes
    What size radius should be used for the LoG filter?:1
    Should the images have a Difference of Gaussians filter applied before correction?:No
    What size sigma should be used for the DoG low sigma?:3
    What size radius should be used for the DoG low sigma?:5
"""
)

# CellProfiler/CellProfiler-plugins
# tests/headless_test/4.2.5_plugins_test_pipeline_BASIC.cppipe at
# e962b48c39f7b191ebf3785fa2af390f3d34e081, module 6, unchanged.
_PLUGINS_TEST_COMPENSATION_PIPELINE = (
    _SOURCE.format(image="DNA")
    + """CompensateColors:[module_num:6|svn_version:'Unknown'|variable_revision_number:1|show_window:True|notes:[]|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Hidden:2
    Hidden:1
    Select an image to measure:DNA
    What compensation class does this image belong to?:1
    Select an output image name:None
    Select an image to measure:DNA
    What compensation class does this image belong to?:1
    Select an output image name:None
    Select where to perform color compensation:Across entire image
    Select an object to perform compensation within:None
    Should individual images be rescaled 0-1 before compensating pre-masking or on unmasked images?:No
    Should images be rescaled 0-1 before compensating but after masking to objects?:No
    Should histogram matching be performed between the image groups?:No
    What compensation class should serve as the template histogram?:1
    Should images be rescaled 0-1 after compensating?:No
    Should the images be divided by a scalar based on group percentiles:No
    What percentile should be used for multiplication:99.0
    Should the images have a tophat filter applied before correction?:No
    What size radius should be used for the tophat filter?:3
    Should the images have a Laplacian of Gaussian filter applied before correction?:No
    What size radius should be used for the LoG filter?:1
    Should the images have a Difference of Gaussians filter applied before correction?:No
    What size sigma should be used for the DoG low sigma?:3
    What size radius should be used for the DoG low sigma?:5
"""
)

# COBA-NIH/Newmark 3DPlanarianOrgans/testes/CP_Testes_4ch.cppipe at
# df202568caa4b98383f1d462d589cc359295bda6, module 8, unchanged. The pipeline
# processes volumes; the block before it stands for the modules that make the
# objects it splits.
_PLANARIAN_TESTES_PIPELINE = (
    """CellProfiler Pipeline: http://www.cellprofiler.org
NamesAndTypes:[module_num:1|enabled:True]
    Process as 3D?:Yes
    Assignments count:1
    Select the image type:Grayscale image
    Name to assign these images:DNA
    Select the rule criteria:and (file does contain "DNA")
ConvertImageToObjects:[module_num:2|enabled:True]
    Select the input image:DNA
    Name the output objects:PreWatershed
"""
    + """DeclumpObjects:[module_num:8|svn_version:'Unknown'|variable_revision_number:1|show_window:False|notes:['Separate objects - separate nuclei that are two closed together that previous module identify as one object']|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Select the input object:PreWatershed
    Name the output object:Watershed
    Declump method:Shape
    Reference Image:None
    Segmentation distance transform smoothing factor:2
    Minimum distance between seeds:7
    Minimum absolute internal distance:0.0
    Pixels from border to exclude:0
    Maximum number of seeds:-1
    Structuring element for seed dilation:Ball,1
    Watershed connectivity:1
"""
)

# carpenter-singh-lab/2025_Haghighi_Mito pipelines/radialdistribution.cppipe at
# 1b92661f0a5b55c606756b0b859bc318f7d4f4cc, module 22, unchanged (that file
# escapes its header lines). The block before it stands for the pipeline's
# modules that make the cells.
_MITO_RADIAL_DISTRIBUTION_PIPELINE = (
    _SOURCE.format(image="actin")
    + """IdentifyPrimaryObjects:[module_num:2|enabled:True]
    Select the input image:actin
    Name the primary objects to be identified:Cells
"""
    + r"""MeasureRadialEntropy:[module_num:22|svn_version:\'Unknown\'|variable_revision_number:1|show_window:True|notes:\x5B\x5D|batch_state:array(\x5B\x5D, dtype=uint8)|enabled:True|wants_pause:False]
    Select an image to measure:actin
    Select objects to measure:Cells
    Which intensity measurement should be used?:Integrated
    Input number of bins:12
"""
)


@pytest.mark.parametrize(
    ("pipeline", "steps"),
    (
        (
            _PLUGINS_TEST_PIPELINE,
            (
                ("distance_transform", {}),
                ("histogram_equalization", {"local": True, "tile_size": 100}),
                ("histogram_matching", {}),
            ),
        ),
        (
            _KUO_SEGMENTATION_PIPELINE,
            (
                (
                    "histogram_equalization",
                    {
                        "bins": 200,
                        "local": True,
                        "planes_form_a_volume": True,
                        "framewise": True,
                    },
                ),
            ),
        ),
        (_KUO_TRACKING_PIPELINE, (("distance_transform", {"rescale": False}),)),
        (
            _TGLOW_PIPELINE,
            (("gaussian_filter", {}), ("histogram_matching", {})),
        ),
        (
            _POOLED_SCREEN_PIPELINE,
            (
                ("identify_primary_objects", {}),
                ("measure_object_intensity", {}),
                (
                    "call_barcodes",
                    {
                        "calling": BrightestBase("Intensity_MaxIntensity_CorrCycle01_A"),
                        "barcode_library": Path("Barcodes.csv"),
                        "barcode_column": "sgRNA",
                        "gene_column": "gene_symbol",
                        "retain_call_image": True,
                        "retain_score_image": True,
                    },
                ),
            ),
        ),
        (
            _POOLED_SCREEN_COMPENSATION_PIPELINE,
            (
                ("identify_primary_objects", {}),
                (
                    "compensate_colors",
                    {
                        "compensation_classes": (1,) * 8 + (2,) * 8 + (3,) * 8 + (4,) * 8,
                        "within_objects": True,
                        "histogram_matching": MatchAfterMasking(template_class=4),
                        "class_percentile": 99.9,
                        "laplacian_of_gaussian_filter": True,
                    },
                ),
            ),
        ),
        (
            _PLANARIAN_TESTES_PIPELINE,
            (
                ("convert_image_to_objects", {}),
                # The function for volumes; a ball of radius 1 is its default.
                (
                    "declump_objects_3d",
                    {"smoothing_sigma": 2.0, "min_seed_distance": 7},
                ),
            ),
        ),
        (
            _MITO_RADIAL_DISTRIBUTION_PIPELINE,
            (
                ("identify_primary_objects", {}),
                (
                    "measure_radial_entropy",
                    {"metric": IntegratedIntensity(), "bins": 12},
                ),
            ),
        ),
    ),
    ids=(
        "plugins_test_pipeline",
        "kuo_segmentation",
        "kuo_tracking",
        "tglow",
        "pooled_screen",
        "pooled_screen_compensation",
        "planarian_testes",
        "mito_radial_distribution",
    ),
)
def test_real_pipeline_blocks_import_as_steps_with_the_plugin_settings(
    tmp_path: Path,
    pipeline: str,
    steps: tuple[tuple[str, dict[str, object]], ...],
) -> None:
    """Imported steps keep only the settings that differ from the plugin defaults.

    A file a block names is found beside the pipeline and shown relative to it.
    """
    cppipe_path = tmp_path / "pipeline.cppipe"
    cppipe_path.write_text(pipeline, encoding="utf-8")
    shutil.copy(_FIXTURES / "Barcodes.csv", tmp_path)

    imported, _pipeline_config = import_cellprofiler_pipeline(cppipe_path)

    settings_of_steps = []
    for step in imported:
        (invocation,) = normalize_function_pattern(step.func).iter_items()
        function = invocation.contract.resolve_canonical_raw_callable()
        settings_of_steps.append(
            (
                invocation.contract.function_name,
                {
                    name: (
                        value.relative_to(tmp_path)
                        if isinstance(value, Path)
                        else value
                    )
                    for name, value in invocation.kwargs_dict.items()
                    if name in inspect.signature(function).parameters
                },
            )
        )
    assert tuple(settings_of_steps) == steps


def test_block_naming_one_output_image_for_several_inputs_is_refused(
    tmp_path: Path,
) -> None:
    """The plugins' own test pipeline keeps the default name of both outputs.

    The plugin then leaves one image, named ``None``, for its two inputs.
    """
    cppipe_path = tmp_path / "pipeline.cppipe"
    cppipe_path.write_text(_PLUGINS_TEST_COMPENSATION_PIPELINE, encoding="utf-8")

    with pytest.raises(ValueError, match="a different output image name for each"):
        import_cellprofiler_pipeline(cppipe_path)
