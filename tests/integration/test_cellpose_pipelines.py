"""The derived Cellpose functions in pipelines through the execution server, on CPU."""

import csv
import dataclasses
import io
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

import numpy as np
import pytest
import tifffile

pytest.importorskip("cellpose", reason="Cellpose is an optional dependency")

from cellpose import denoise, models, utils
from objectstate.lazy_factory import ensure_global_config_context
from zmqruntime.execution.responses import (
    ExecutionSubmissionResponse,
    ExecutionWaitResult,
)

from openhcs.core.config import (
    GlobalPipelineConfig,
    LazyPathPlanningConfig,
    LazyProcessingConfig,
    LazyVFSConfig,
    MaterializeToDisk,
    PathPlanningConfig,
    PipelineConfig,
    VFSConfig,
)
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.core.steps import FunctionStep
from openhcs.demo.synthetic_data import SyntheticMicroscopyGenerator
from openhcs.domains.microscopy.axes import Microscopy
from openhcs.microscopes.imagexpress import ImageXpressHandler
from openhcs.processing.backends.lib_registry.derived import cellpose as derived
from openhcs.processing.custom_functions import CustomFunctionManager
from openhcs.runtime.zmq_execution_client import (
    OpenHCSExecutionSubmission,
    ZMQExecutionClient,
)

NUCLEI = derived.SegmentationModel.NUCLEI
DIAMETER = 12.0
SUFFIX = "_cellpose"
EXAMPLES = Path(__file__).parents[2] / "examples" / "custom_functions"
CENTRES = ((20, 20), (60, 30), (40, 70), (75, 75), (30, 100), (100, 50), (105, 105), (3, 64))


def _field(seed: int, size: int = 128) -> np.ndarray:
    """Bright blobs on a noisy background, as a 16-bit camera field."""

    rng = np.random.default_rng(seed)
    yy, xx = np.mgrid[:size, :size]
    field = np.zeros((size, size))
    for cy, cx in CENTRES:
        cy, cx = cy + rng.integers(-3, 4), cx + rng.integers(-3, 4)
        field += np.exp(-((yy - cy) ** 2 + (xx - cx) ** 2) / (2 * 6.0**2))
    return (500 + 20000 * field + rng.normal(0, 100, field.shape)).clip(0).astype(np.uint16)


def make_plate(root: Path, *, wells=("A01",), sites: int = 2, z_levels: int = 1) -> Path:
    """An ImageXpress plate of one channel whose pixels are ``_field`` of the file's index."""

    plate = root / "plate"
    with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
        SyntheticMicroscopyGenerator(
            output_dir=str(plate),
            grid_size=(1, sites),
            tile_size=(128, 128),
            overlap_percent=10,
            stage_error_px=1,
            wavelengths=1,
            z_stack_levels=z_levels,
            num_cells=2,
            wells=list(wells),
            format="ImageXpress",
            random_seed=7,
        ).generate_dataset()
    for index, file in enumerate(sorted(plate.rglob("*.tif"))):
        tifffile.imwrite(file, _field(index))
    return plate


def run_pipeline(plate: Path, steps: list[FunctionStep]) -> Path:
    """Compile and run ``steps`` on a private execution server; return the plate's parent."""

    vfs_config = VFSConfig(materialization_backend=MaterializeToDisk)
    global_config = GlobalPipelineConfig(
        num_workers=1,
        dataset_source=ImageXpressHandler,
        use_threading=False,
        path_planning_config=PathPlanningConfig(output_dir_suffix=SUFFIX),
        vfs_config=vfs_config,
    )
    pipeline_config = PipelineConfig(
        path_planning_config=LazyPathPlanningConfig(output_dir_suffix=SUFFIX),
        vfs_config=LazyVFSConfig.from_config(vfs_config),
    )
    ensure_global_config_context(GlobalPipelineConfig, global_config)

    def submission(**compiled) -> OpenHCSExecutionSubmission:
        return OpenHCSExecutionSubmission(
            subject_id=plate,
            pipeline_document=PipelineDocumentCodec.from_values(
                pipeline_config=pipeline_config, pipeline_steps=steps
            ),
            global_config=global_config,
            **compiled,
        )

    with ZMQExecutionClient.with_private_server() as client:
        compile_id = ExecutionSubmissionResponse.from_wire(
            client.submit_compile(submission())
        ).require_execution_id("Cellpose pipeline compilation")
        ExecutionWaitResult.from_wire(
            client.wait_for_completion(compile_id)
        ).require_complete("Cellpose pipeline compilation")
        execution_id = ExecutionSubmissionResponse.from_wire(
            client.submit_pipeline(submission(compile_artifact_id=compile_id))
        ).require_execution_id("Cellpose pipeline execution")
        ExecutionWaitResult.from_wire(
            client.wait_for_completion(execution_id)
        ).require_complete("Cellpose pipeline execution")
    return plate.parent


def source_stack(plate: Path, well: str = "A01") -> np.ndarray:
    return np.stack([tifffile.imread(file) for file in sorted(plate.rglob(f"{well}_*.tif"))])


def one(root: Path, pattern: str) -> Path:
    (found,) = sorted(root.rglob(pattern))
    return found


def table(root: Path, pattern: str) -> list[dict[str, str]]:
    with one(root, pattern).open(newline="") as handle:
        return list(csv.DictReader(handle))


def output(root: Path, artifact: str) -> np.ndarray:
    return tifffile.imread(one(root, f"*{artifact}_step*.{artifact}.tif"))


def cellpose_planes(masks, flows) -> dict[str, np.ndarray]:
    """One direct Cellpose result, shaped as the derived function publishes it."""

    return {
        "cellpose_labels": np.stack(masks),
        "cell_probability": np.stack([flow[2] for flow in flows]),
        "flow_field": np.stack([np.moveaxis(flow[1], 0, -1) for flow in flows]),
        "flow_rgb": np.stack([flow[0] for flow in flows]),
    }


def step(function, **controls) -> FunctionStep:
    return FunctionStep(name=function.__name__, func=(function, controls))


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
