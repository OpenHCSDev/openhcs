"""The derived Cellpose functions equal Cellpose, and take everything from it."""

import dataclasses
import inspect
from pathlib import Path
from typing import Any, Optional

import numpy as np
import pytest

pytest.importorskip("cellpose", reason="Cellpose is an optional dependency")

import torch
from cellpose import denoise, dynamics, metrics, models, train, utils

from openhcs.core.callable_contract import CallableContract
from openhcs.core.vfs_protocol import PlateInputFile
from openhcs.processing.backends.lib_registry.derived import (
    cellpose as derived,
)
from openhcs.processing.backends.lib_registry.model_library import (
    Call,
    Converted,
    Derived,
    Forwarded,
    FromEarlierStep,
    ImageStack,
    Required,
    Resource,
    SameControl,
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
                statement,
                (Derived, Stated, Supplied, Resource, Forwarded, ImageStack)
                + (FromEarlierStep, SameControl, Converted),
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
                if control.source is not None:
                    assert control.source.parameter_name == site.name
                elif isinstance(statement, Required):
                    assert control.default is inspect.Parameter.empty
                elif isinstance(statement, Stated) and control.default is not None:
                    assert statement.to_library(control.default) == (
                        models.normalize_default
                        if control.name == "normalize"
                        else library_default
                    )
                elif isinstance(library_default, list):
                    assert control.default == tuple(library_default)
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

    probability, flow_field, flow_rgb, labels, rows = outputs
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
    assert outputs[1].shape == (*stack.shape, 3)
    _assert_segmentation(outputs, [masks], [flows], [styles], [masks.max()])


def test_segment_two_channels_equals_cellpose(stack, nuclei):
    _, *outputs = derived.segment(
        stack[:2], model_type=NUCLEI, diameter=DIAMETER, channel_axis=0, channels=(1, 2)
    )
    masks, flows, styles = nuclei.eval(
        stack[:2], diameter=DIAMETER, channel_axis=0, channels=[1, 2]
    )
    assert outputs[3].shape == (1, *stack.shape[1:])
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
    restored = derived.restore(
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


# ---- plain functions of masks and flows ------------------------------------------


@pytest.fixture(scope="module")
def segmented(stack, nuclei):
    """Labels, flow field (channels last) and cell probability, as a step publishes them."""

    masks, flows, _ = nuclei.eval(list(stack), diameter=DIAMETER)
    assert min(mask.max() for mask in masks) > 1
    return {
        "labels": np.stack(masks).astype(np.int32),
        "flows": np.stack([_channels_last(flow[1]) for flow in flows]),
        "probability": np.stack([flow[2] for flow in flows]),
    }


def _one_plane(given: dict, plane: int) -> dict:
    return {
        name: np.moveaxis(array[plane], -1, 0).copy() if array.ndim == 4 else array[plane].copy()
        for name, array in given.items()
    }


ARRAY_RESULTS = {
    "resize_and_compute_masks": (
        dynamics.resize_and_compute_masks,
        {"dP": "flows", "cellprob": "probability"},
        {"min_size": 5, "flow_threshold": 0.6},
    ),
    "compute_masks": (
        dynamics.compute_masks,
        {"dP": "flows", "cellprob": "probability"},
        {"cellprob_threshold": -0.5},
    ),
    "remove_bad_flow_masks": (
        dynamics.remove_bad_flow_masks,
        {"masks": "labels", "flows": "flows"},
        {"threshold": 1.0},
    ),
    "remove_edge_masks": (utils.remove_edge_masks, {"masks": "labels"}, {}),
    "dilate_masks": (utils.dilate_masks, {"masks": "labels"}, {"n_iter": 2}),
    "fill_holes_and_remove_small_masks": (
        utils.fill_holes_and_remove_small_masks,
        {"masks": "labels"},
        {"min_size": 120},
    ),
    "masks_to_flows": (dynamics.masks_to_flows, {"masks": "labels"}, {}),
    "masks_to_outlines": (utils.masks_to_outlines, {"masks": "labels"}, {}),
    "masks_to_edges": (utils.masks_to_edges, {"masks": "labels"}, {"threshold": 2.0}),
    "distance_to_boundary": (utils.distance_to_boundary, {"masks": "labels"}, {}),
}
LABEL_RESULTS = list(ARRAY_RESULTS)[:6]


@pytest.mark.parametrize("name", ARRAY_RESULTS)
def test_a_function_of_one_plane_equals_cellpose_on_every_plane(name, stack, segmented):
    direct, takes, controls = ARRAY_RESULTS[name]
    given = {parameter: segmented[artifact] for parameter, artifact in takes.items()}
    function = getattr(derived, name)
    published = {parameter: array.copy() for parameter, array in given.items()}
    image, *counts, result = function(stack, **given, **controls)
    # Cellpose changes some of its arguments in place; what a step published stays.
    for parameter, array in published.items():
        assert np.array_equal(given[parameter], array), parameter
    expected = [
        np.asarray(direct(**_one_plane(given, plane), **controls))
        for plane in range(len(stack))
    ]
    if expected[0].ndim == 3:
        expected = [_channels_last(flow) for flow in expected]
    assert np.array_equal(image, stack)
    result = np.asarray(result)
    assert np.array_equal(result, np.stack(expected))
    assert result.any()
    if name in LABEL_RESULTS:
        assert result.dtype == np.int32
    consumed = CallableContract.from_callable(function).artifact_inputs
    assert sorted(spec.parameter_name for spec in consumed) == sorted(takes)


def test_stitch3d_takes_the_stack_as_one_volume(stack, segmented):
    _, _, stitched = derived.stitch3D(stack, masks=segmented["labels"], stitch_threshold=0.1)
    expected = utils.stitch3D(segmented["labels"].copy(), stitch_threshold=0.1)
    assert np.array_equal(stitched, expected)
    assert stitched.dtype == np.int32


def _columns(rows) -> dict[str, np.ndarray]:
    names = [field.name for field in dataclasses.fields(rows.row_type)]
    return {name: np.array([getattr(row, name) for row in rows.rows]) for name in names}


def test_measurements_of_every_object_equal_cellpose(stack, segmented):
    labels = segmented["labels"]
    counts = [len(np.unique(plane)) - 1 for plane in labels]

    def per_object(values) -> np.ndarray:
        return np.concatenate(
            [np.broadcast_to(value, count) for value, count in zip(values, counts)]
        )

    for name, direct, columns in (
        ("diameters", utils.diameters, {"median_diameter": 0, "diameter": 1}),
        ("get_mask_compactness", utils.get_mask_compactness, {"compactness": None}),
        ("get_mask_perimeters", utils.get_mask_perimeters, {"perimeter": None}),
    ):
        _, rows = getattr(derived, name)(stack, masks=labels)
        expected = [direct(plane) for plane in labels]
        table = _columns(rows)
        assert list(table) == ["slice_index", "object", *columns], name
        assert np.array_equal(
            table["slice_index"], np.repeat(np.arange(len(labels)), counts)
        )
        assert np.array_equal(
            table["object"], np.concatenate([np.arange(count) for count in counts])
        )
        for column, at in columns.items():
            assert np.array_equal(
                table[column], per_object([e if at is None else e[at] for e in expected])
            ), (name, column)

    predicted = np.stack([utils.dilate_masks(plane, 1) for plane in labels]).astype(np.int32)
    _, rows = derived.mask_ious(stack, masks_true=labels, masks_pred=predicted)
    expected = [metrics.mask_ious(true, pred) for true, pred in zip(labels, predicted)]
    table = _columns(rows)
    assert np.array_equal(table["iou"], per_object([e[0] for e in expected]))
    assert np.array_equal(table["matched_prediction"], per_object([e[1] for e in expected]))
    assert 0 < table["iou"].min() < 1


def test_measurements_of_every_plane_equal_cellpose(stack, segmented):
    labels = segmented["labels"]
    predicted = np.stack([utils.dilate_masks(plane, 1) for plane in labels]).astype(np.int32)
    _, rows = derived.size_distribution(stack, masks=labels)
    assert np.array_equal(
        _columns(rows)["size_distribution"],
        [utils.size_distribution(plane) for plane in labels],
    )
    _, rows = derived.aggregated_jaccard_index(stack, masks_true=labels, masks_pred=predicted)
    assert np.array_equal(
        _columns(rows)["aggregated_jaccard_index"],
        metrics.aggregated_jaccard_index(list(labels), list(predicted)),
    )
    _, rows = derived.average_precision(
        stack, masks_true=labels, masks_pred=predicted, threshold=(0.5, 0.9)
    )
    expected = metrics.average_precision(list(labels), list(predicted), threshold=[0.5, 0.9])
    table = _columns(rows)
    for column, values in zip(
        ("average_precision", "true_positives", "false_positives", "false_negatives"),
        expected,
    ):
        for threshold in (0, 1):
            assert np.array_equal(table[f"{column}_{threshold}"], values[:, threshold])
    assert list(table["slice_index"]) == [0, 1, 2]


# ---- training ----------------------------------------------------------------------

TRAINING = {"n_epochs": 2, "min_train_masks": 1}


def test_training_then_segmenting_with_the_trained_file_equals_cellpose(
    stack, segmented, tmp_path
):
    labels = segmented["labels"]
    cellpose_options = {
        **TRAINING,
        "channels": [0, 0],
        "normalize": dataclasses.asdict(derived.NormalizeOptions()),
    }
    image, rows = derived.train_segmentation(
        stack,
        train_labels=labels,
        model_type=NUCLEI,
        save_path=tmp_path / "derived",
        model_name="tiny",
        channels=(0, 0),
        **TRAINING,
    )
    (tmp_path / "direct").mkdir()
    file, train_losses, test_losses = train.train_seg(
        models.CellposeModel(model_type="nuclei").net,
        train_data=list(stack),
        train_labels=list(labels),
        save_path=str(tmp_path / "direct"),
        model_name="tiny",
        **cellpose_options,
    )
    trained = tmp_path / "derived" / "models" / "tiny"
    assert np.array_equal(image, stack)
    assert trained.is_file() and file == tmp_path / "direct" / "models" / "tiny"
    table = _columns(rows)
    assert list(table["epoch"]) == [0, 1]
    assert np.array_equal(table["train_loss"], train_losses) and train_losses.all()
    assert np.array_equal(table["test_loss"], test_losses)

    *_, segmented_labels, _ = derived.segment(
        stack, pretrained_model=trained, diameter=DIAMETER
    )
    masks, _, _ = models.CellposeModel(pretrained_model=str(file)).eval(
        list(stack), diameter=DIAMETER
    )
    assert np.array_equal(segmented_labels, np.stack(masks))
    assert segmented_labels.any()

    derived.train_size(
        stack, train_labels=labels, pretrained_model=trained, channels=(0, 0), **TRAINING
    )
    expected = train.train_size(
        models.CellposeModel(pretrained_model=str(file)).net,
        str(file),
        train_data=list(stack),
        train_labels=list(labels),
        **cellpose_options,
    )
    size_model = tmp_path / "derived" / "models" / "tiny_size.npy"
    saved = np.load(size_model, allow_pickle=True).item()
    assert sorted(saved) == sorted(expected)
    for key, value in expected.items():
        assert np.array_equal(saved[key], value), key
    _, rows = derived.estimate_diameter_with_size_model_file(
        stack, pretrained_model=trained, pretrained_size=size_model, channels=(0, 0)
    )
    assert (_columns(rows)["diameter"] > 0).all()


def test_restoration_training_is_derived_and_stopped_by_cellpose_without_cuda(
    stack, segmented, tmp_path
):
    """``denoise.py:470`` loads the segmentation weights with no ``map_location``."""

    parameters = inspect.signature(derived.train_restoration).parameters
    assert parameters["lam"].default == (1.0, 1.5, 0.0)
    assert parameters["seg_model_type"].default is derived.SegmentationModel.CYTO2
    assert parameters["model_type"].annotation == Optional[derived.RestorationModel]
    if torch.cuda.is_available():
        pytest.skip("With CUDA Cellpose loads its weights; the run is not checked here.")
    with pytest.raises(RuntimeError, match="deserialize object on a CUDA device"):
        derived.train_restoration(
            stack,
            train_labels=segmented["labels"],
            save_path=tmp_path,
            n_epochs=100,
            seg_model_type=NUCLEI,
        )
