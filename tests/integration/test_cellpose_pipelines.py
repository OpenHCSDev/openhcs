"""The derived Cellpose functions in pipelines through the execution server, on CPU."""

import dataclasses

import numpy as np
import pytest
import tifffile

pytest.importorskip("cellpose", reason="Cellpose is an optional dependency")

from cellpose import denoise, models, utils

from openhcs.core.config import LazyProcessingConfig
from openhcs.core.steps import FunctionStep
from openhcs.domains.microscopy.axes import Microscopy
from openhcs.processing.backends.lib_registry.derived import cellpose as derived
from openhcs.processing.custom_functions import CustomFunctionManager
from tests.cellpose_pipeline_support import (
    DIAMETER,
    EXAMPLES,
    NUCLEI,
    cellpose_planes,
    make_plate,
    one,
    output,
    run_pipeline,
    source_stack,
    step,
    table,
)


def test_segment_with_its_own_parameters_materializes_every_output(tmp_path):
    plate = make_plate(tmp_path)
    options = derived.NormalizeOptions(percentile=(2.0, 98.0))
    controls = {"diameter": DIAMETER, "flow_threshold": 0.6, "cellprob_threshold": -1.0}
    root = run_pipeline(
        plate, [step(derived.segment, model_type=NUCLEI, normalize=options, **controls)]
    )
    masks, flows, styles = models.CellposeModel(model_type="nuclei").eval(
        list(source_stack(plate)), normalize=dataclasses.asdict(options), **controls
    )
    assert min(mask.max() for mask in masks) >= 5
    for artifact, expected in cellpose_planes(masks, flows).items():
        assert np.array_equal(output(root, artifact), expected), artifact
    rows = table(root, "*measurements_step*_details.csv")
    assert [int(row["object_count"]) for row in rows] == [mask.max() for mask in masks]
    assert [float(row["style_17"]) for row in rows] == [float(style[17]) for style in styles]
    assert len(sorted(root.rglob("*cellpose_labels_step*_rois.roi.zip"))) == len(masks)
    assert np.array_equal(
        np.stack([tifffile.imread(f) for f in sorted(root.rglob("*_cellpose/images/*.tif"))]),
        source_stack(plate),
    )


def test_labels_pass_through_a_mask_function_to_a_measuring_custom_function(
    tmp_path, monkeypatch
):
    monkeypatch.setenv("XDG_DATA_HOME", str(tmp_path / "data-home"))
    (measure,) = CustomFunctionManager().register_from_code(
        (EXAMPLES / "measure_labelled_objects.py").read_text(),
        persist=True,
        emit_signal=False,
    )
    plate = make_plate(tmp_path)
    root = run_pipeline(
        plate,
        [
            step(derived.segment, model_type=NUCLEI, diameter=DIAMETER),
            step(derived.remove_edge_masks),
            step(measure, min_area_px=10),
        ],
    )
    masks, _, _ = models.CellposeModel(model_type="nuclei").eval(
        list(source_stack(plate)), diameter=DIAMETER
    )
    kept = np.stack([utils.remove_edge_masks(mask.astype(np.int32)) for mask in masks])
    assert kept.max() < np.stack(masks).max()
    after = tifffile.imread(one(root, "*cellpose_labels_step1.cellpose_labels.tif"))
    assert np.array_equal(after, kept)
    counts = table(root, "*object_counts_step1_details.csv")
    assert [int(row["object_count"]) for row in counts] == [plane.max() for plane in kept]
    measured = table(root, "*object_measurements_step2_details.csv")
    assert sorted((int(row["slice_index"]), int(row["label"])) for row in measured) == [
        (index, label) for index, plane in enumerate(kept) for label in np.unique(plane)[1:]
    ]
    areas = {(int(row["slice_index"]), int(row["label"])): float(row["area_px"]) for row in measured}
    assert areas[0, 1] == np.count_nonzero(kept[0] == 1)


def test_restore_then_segment_in_one_pipeline(tmp_path):
    plate = make_plate(tmp_path)
    restore = {"diameter": DIAMETER, "channels": (0, 0)}
    root = run_pipeline(
        plate,
        [
            step(derived.restore, model_type=derived.RestorationModel.DENOISE_NUCLEI, **restore),
            step(derived.segment, model_type=NUCLEI, diameter=DIAMETER),
        ],
    )
    restored = denoise.DenoiseModel(model_type="denoise_nuclei").eval(
        list(source_stack(plate)), diameter=DIAMETER, channels=[0, 0]
    )
    restored = np.stack(restored)[..., 0]
    masks, _, _ = models.CellposeModel(model_type="nuclei").eval(
        list(restored), diameter=DIAMETER
    )
    assert np.stack(masks).max() >= 5
    assert np.array_equal(output(root, "cellpose_labels"), np.stack(masks))


@pytest.mark.parametrize(
    "volume", [{"do_3D": True}, {"stitch_threshold": 0.3}], ids=["do_3D", "stitched"]
)
def test_a_z_stack_is_segmented_as_one_volume(tmp_path, volume):
    plate = make_plate(tmp_path, sites=1, z_levels=3)
    controls = {"diameter": DIAMETER, "z_axis": 0, **volume}
    root = run_pipeline(
        plate,
        [
            FunctionStep(
                name="segment",
                func=(derived.segment, {"model_type": NUCLEI, **controls}),
                processing_config=LazyProcessingConfig(
                    variable_components=[Microscopy.ZIndex]
                ),
            )
        ],
    )
    stack = source_stack(plate)
    assert stack.shape == (3, 128, 128)
    masks, flows, _ = models.CellposeModel(model_type="nuclei").eval(stack, **controls)
    assert masks.shape == stack.shape and masks.max() >= 5
    assert np.array_equal(output(root, "cellpose_labels"), masks)
    assert np.array_equal(output(root, "cell_probability"), flows[2])
    assert np.array_equal(output(root, "flow_field"), np.moveaxis(flows[1], 0, -1))
    (row,) = table(root, "*measurements_step*_details.csv")
    assert int(row["object_count"]) == masks.max()


def test_segment_estimating_diameter_reports_the_diameter(tmp_path):
    plate = make_plate(tmp_path)
    root = run_pipeline(
        plate, [step(derived.segment_estimating_diameter, model_type=NUCLEI, diameter=None)]
    )
    masks, _, _, diameters = models.Cellpose(model_type="nuclei").eval(
        list(source_stack(plate)), diameter=None, channels=[0, 0]
    )
    rows = table(root, "*measurements_step*_details.csv")
    assert [float(row["diameter"]) for row in rows] == [float(d) for d in diameters]
    assert all(8 < diameter < 30 for diameter in diameters)
    assert np.array_equal(output(root, "cellpose_labels"), np.stack(masks))


def test_train_in_one_pipeline_then_segment_with_the_model_file_in_another(tmp_path):
    training = {"n_epochs": 2, "min_train_masks": 1, "channels": (0, 0)}
    plate = make_plate(tmp_path)
    models_home = tmp_path / "trained"
    root = run_pipeline(
        plate,
        [
            step(derived.segment, model_type=NUCLEI, diameter=DIAMETER),
            step(
                derived.train_segmentation,
                model_type=NUCLEI,
                save_path=models_home,
                model_name="tiny",
                **training,
            ),
        ],
    )
    trained = models_home / "models" / "tiny"
    assert trained.is_file()
    losses = table(root, "*losses_step1_details.csv")
    assert [int(row["epoch"]) for row in losses] == [0, 1]
    assert all(float(row["train_loss"]) > 0 for row in losses)

    again = make_plate(tmp_path / "second")
    root = run_pipeline(
        again, [step(derived.segment, pretrained_model=trained, diameter=DIAMETER)]
    )
    masks, _, _ = models.CellposeModel(pretrained_model=str(trained)).eval(
        list(source_stack(again)), diameter=DIAMETER
    )
    assert np.stack(masks).max() >= 5
    assert np.array_equal(output(root, "cellpose_labels"), np.stack(masks))
