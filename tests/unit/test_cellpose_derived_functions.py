"""The derived Cellpose functions equal Cellpose, and take everything from it."""

import dataclasses
import inspect
from pathlib import Path
from typing import Any

import numpy as np
import pytest

pytest.importorskip("cellpose", reason="Cellpose is an optional dependency")

from cellpose import denoise, models

from openhcs.core.vfs_protocol import PlateInputFile
from openhcs.processing.backends.lib_registry.derived import (
    cellpose as derived,
)
from openhcs.processing.backends.lib_registry.model_library import (
    Call,
    Derived,
    Forwarded,
    ImageStack,
    Required,
    Resource,
    Stated,
    Supplied,
)

NUCLEI = derived.SegmentationModel.NUCLEI
DENOISE_NUCLEI = derived.RestorationModel.DENOISE_NUCLEI
SIZE_MODEL = Path(models.size_model_path("nuclei"))
DIAMETER = 12.0


@pytest.fixture(scope="module")
def stack() -> np.ndarray:
    rng = np.random.default_rng(0)
    yy, xx = np.mgrid[:96, :96]
    plane = np.zeros((96, 96), np.float32)
    for cy, cx in ((20, 20), (60, 30), (40, 70), (75, 75)):
        plane += np.exp(-((yy - cy) ** 2 + (xx - cx) ** 2) / (2 * 6.0**2))
    return np.stack(
        [plane * (1 + 0.1 * i) + rng.normal(0, 0.02, plane.shape) for i in range(3)]
    ).astype(np.float32)


@pytest.fixture(scope="module")
def nuclei():
    return models.CellposeModel(model_type="nuclei")


def _calls(call: Call = None):
    """Every declared call and the calls its statements build or forward to."""

    for outer in (
        [declared[0] for declared in derived.library._declared.values()]
        if call is None
        else [call]
    ):
        yield outer
        for _site, statement in outer.bound:
            if isinstance(statement, Resource):
                yield from _calls(statement.factory)
            if isinstance(statement, Forwarded):
                yield from _calls(statement.to)


# ---- guards ----------------------------------------------------------------------


def test_every_cellpose_parameter_is_a_control_supplied_or_a_resource():
    for call in _calls():
        assert [site.name for site, _ in call.bound] == list(
            inspect.signature(call.target).parameters
        )
        for site, statement in call.bound:
            assert isinstance(
                statement, (Derived, Stated, Supplied, Resource, Forwarded, ImageStack)
            )
            if isinstance(statement, Supplied):
                assert statement.reason.strip(), (call.target, site.name)


def test_every_statement_names_a_parameter_of_the_installed_cellpose():
    named = {site.name for call in _calls() for site, _ in call.bound}
    assert set(derived.library.statements) <= named
    assert set(derived.library.one_image_when_set) <= named
    with pytest.raises(TypeError, match="no parameter named"):
        derived.library.call(models.CellposeModel.eval, {"gone": Supplied("x")})


def test_no_control_is_typed_any_and_every_default_is_cellposes():
    stated = {
        name: statement
        for name, statement in derived.library.statements.items()
        if isinstance(statement, Stated)
    }
    for call in _calls():
        for site, statement in call.bound:
            for control in statement.controls(site) if not isinstance(
                statement, (Resource, Forwarded)
            ) else ():
                assert control.annotation is not Any
                assert control.annotation is not inspect.Parameter.empty
                library_default = site.parameter.default
                if isinstance(statement, Required):
                    assert control.default is inspect.Parameter.empty
                elif isinstance(statement, Stated) and control.default is not None:
                    assert statement.to_library(control.default) == (
                        models.normalize_default
                        if control.name == "normalize"
                        else library_default
                    )
                else:
                    assert control.default == library_default or (
                        control.default is None and not library_default
                    )
    assert stated


def test_function_signatures_carry_every_control_with_a_description():
    for name, function in derived.library.functions.items():
        call = derived.library._declared[name][0]
        parameters = inspect.signature(function).parameters
        assert list(parameters)[: len(call.controls) + 1] == [
            "image",
            *(control.name for control in call.controls),
        ]
        documented = inspect.getdoc(function)
        for control in call.controls:
            assert parameters[control.name].annotation is not Any
            assert f"    {control.name}: " in documented or not control.text


def test_model_enums_and_options_equal_cellposes():
    assert [member.value for member in derived.SegmentationModel] == list(
        dict.fromkeys(models.MODEL_NAMES)
    )
    assert [member.value for member in derived.RestorationModel] == list(
        dict.fromkeys(denoise.MODEL_NAMES)
    )
    assert dataclasses.asdict(derived.NormalizeOptions()) == models.normalize_default


# ---- parity with the direct Cellpose call ------------------------------------------


def _channels_last(flow_field: np.ndarray) -> np.ndarray:
    return np.moveaxis(flow_field, 0, -1)


def _assert_rows(rows, **columns):
    for column, expected in columns.items():
        got = np.array([getattr(row, column) for row in rows.rows])
        assert np.array_equal(got, np.asarray(expected)), column


def _assert_segmentation(outputs, masks, flows, styles, count_per_image):
    """``masks``, ``flows`` and ``styles`` are lists with one entry per image."""

    labels, probability, flow_field, flow_rgb, rows = outputs
    as_planes = lambda array, rank: array if array.ndim > rank else array[None]
    assert np.array_equal(
        labels, np.concatenate([as_planes(m, 2) for m in masks])
    )
    assert labels.dtype == np.int32
    assert np.array_equal(
        probability, np.concatenate([as_planes(f[2], 2) for f in flows])
    )
    assert np.array_equal(
        flow_field,
        np.concatenate([as_planes(_channels_last(f[1]), 3) for f in flows]),
    )
    assert np.array_equal(
        flow_rgb, np.concatenate([as_planes(f[0], 3) for f in flows])
    )
    assert [row.slice_index for row in rows.rows] == list(range(len(masks)))
    _assert_rows(rows, object_count=count_per_image)
    if np.ndim(styles[0]) == 1:
        _assert_rows(
            rows, **{f"style_{k}": [s[k] for s in styles] for k in (0, 17, 255)}
        )


def test_segment_planes_with_thresholds_and_normalization_equals_cellpose(
    stack, nuclei
):
    options = derived.NormalizeOptions(percentile=(2.0, 98.0), tile_norm_blocksize=0)
    image, *outputs = derived.segment(
        stack,
        model_type=NUCLEI,
        diameter=DIAMETER,
        flow_threshold=0.6,
        cellprob_threshold=-1.0,
        normalize=options,
    )
    masks, flows, styles = nuclei.eval(
        list(stack),
        diameter=DIAMETER,
        flow_threshold=0.6,
        cellprob_threshold=-1.0,
        normalize=dataclasses.asdict(options),
    )
    assert np.array_equal(image, stack)
    assert max(m.max() for m in masks) > 0
    _assert_segmentation(outputs, masks, flows, styles, [m.max() for m in masks])


def test_segment_with_defaults_equals_cellpose_with_defaults(stack, nuclei):
    _, *outputs = derived.segment(stack, model_type=NUCLEI, diameter=DIAMETER)
    masks, flows, styles = nuclei.eval(list(stack), diameter=DIAMETER)
    _assert_segmentation(outputs, masks, flows, styles, [m.max() for m in masks])


def test_segment_stitched_volume_equals_cellpose(stack, nuclei):
    _, *outputs = derived.segment(
        stack, model_type=NUCLEI, diameter=DIAMETER, z_axis=0, stitch_threshold=0.3
    )
    masks, flows, styles = nuclei.eval(
        stack, diameter=DIAMETER, z_axis=0, stitch_threshold=0.3
    )
    assert masks.shape == stack.shape
    _assert_segmentation(outputs, [masks], [flows], [styles], [masks.max()])


def test_segment_3d_equals_cellpose(stack, nuclei):
    _, *outputs = derived.segment(
        stack, model_type=NUCLEI, diameter=DIAMETER, z_axis=0, do_3D=True
    )
    masks, flows, styles = nuclei.eval(stack, diameter=DIAMETER, z_axis=0, do_3D=True)
    assert flows[1].shape == (3, *stack.shape)
    assert outputs[2].shape == (*stack.shape, 3)
    _assert_segmentation(outputs, [masks], [flows], [styles], [masks.max()])


def test_segment_two_channels_equals_cellpose(stack, nuclei):
    _, *outputs = derived.segment(
        stack[:2], model_type=NUCLEI, diameter=DIAMETER, channel_axis=0, channels=(1, 2)
    )
    masks, flows, styles = nuclei.eval(
        stack[:2], diameter=DIAMETER, channel_axis=0, channels=[1, 2]
    )
    assert outputs[0].shape == (1, *stack.shape[1:])
    _assert_segmentation(outputs, [masks], [flows], [styles], [masks.max()])


def test_segment_without_masks_equals_cellpose_and_labels_nothing(stack, nuclei):
    _, *outputs = derived.segment(
        stack, model_type=NUCLEI, diameter=DIAMETER, compute_masks=False
    )
    masks, flows, styles = nuclei.eval(
        list(stack), diameter=DIAMETER, compute_masks=False
    )
    assert all(not m.size for m in masks)
    _assert_segmentation(
        outputs, [np.zeros(stack.shape[1:])] * 3, flows, styles, [0, 0, 0]
    )


def test_segment_estimating_diameter_equals_cellpose(stack):
    _, *outputs = derived.segment_estimating_diameter(
        stack, model_type=NUCLEI, diameter=None, flow_threshold=0.6
    )
    masks, flows, styles, diameters = models.Cellpose(model_type="nuclei").eval(
        list(stack), diameter=None, channels=[0, 0], flow_threshold=0.6
    )
    _assert_segmentation(outputs, masks, flows, styles, [m.max() for m in masks])
    _assert_rows(outputs[-1], diameter=diameters)


def test_estimate_diameter_with_a_built_in_model_equals_cellpose(stack):
    image, rows = derived.estimate_diameter(stack, model_type=NUCLEI, channels=(0, 0))
    diameters, from_style = models.Cellpose(model_type="nuclei").sz.eval(
        list(stack), channels=[0, 0]
    )
    assert np.array_equal(image, stack)
    assert all(diameter > 0 for diameter in diameters)
    _assert_rows(rows, diameter=diameters, diameter_from_style=from_style)


def test_estimate_diameter_with_a_size_model_file_equals_cellpose(stack, nuclei):
    function = derived.estimate_diameter_with_size_model_file
    required = inspect.signature(function).parameters["pretrained_size"]
    assert required.default is inspect.Parameter.empty
    assert required.annotation is PlateInputFile
    with pytest.raises(TypeError, match="pretrained_size"):
        function(stack, model_type=NUCLEI)
    image, rows = function(
        stack, model_type=NUCLEI, pretrained_size=SIZE_MODEL, channels=(0, 0)
    )
    diameters, from_style = models.SizeModel(
        nuclei, pretrained_size=str(SIZE_MODEL)
    ).eval(list(stack), channels=[0, 0])
    assert np.array_equal(image, stack)
    _assert_rows(rows, diameter=diameters, diameter_from_style=from_style)


def test_restore_equals_cellpose(stack):
    (restored,) = derived.restore(
        stack, model_type=DENOISE_NUCLEI, diameter=DIAMETER, channels=(0, 0)
    )
    expected = denoise.DenoiseModel(model_type="denoise_nuclei").eval(
        list(stack), diameter=DIAMETER, channels=[0, 0]
    )
    assert restored.shape == stack.shape
    assert np.array_equal(restored, np.stack(expected)[..., 0])
    assert not np.array_equal(restored, stack)


def test_restore_and_segment_equals_cellpose(stack):
    restored, *outputs = derived.restore_and_segment(
        stack,
        model_type=NUCLEI,
        restore_type=DENOISE_NUCLEI,
        diameter=DIAMETER,
        channels=(0, 0),
    )
    masks, flows, styles, expected = denoise.CellposeDenoiseModel(
        model_type="nuclei", restore_type="denoise_nuclei"
    ).eval(list(stack), diameter=DIAMETER, channels=[0, 0])
    assert np.array_equal(restored, np.stack(expected)[..., 0])
    _assert_segmentation(outputs, masks, flows, styles, [m.max() for m in masks])
