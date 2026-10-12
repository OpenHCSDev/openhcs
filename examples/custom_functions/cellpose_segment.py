"""Cellpose segmentation as an OpenHCS custom function.

Paste this file into the custom-function editor, or register it with
``CustomFunctionManager().register_from_code(source)``. It needs the optional
``cellpose`` package (3.x) in the environment that runs OpenHCS; pretrained
weights are downloaded by Cellpose into its own cache, never into this repo.
"""

from dataclasses import dataclass
from enum import Enum
from typing import Optional

import numpy as np
from cellpose import models

from openhcs.core.artifacts.kinds import (
    MeasurementsArtifactType,
    ObjectLabelsArtifactType,
)
from openhcs.core.artifacts.relations import ArtifactMeasurementSubjectRelation
from openhcs.core.artifacts.specs import ArtifactSpec
from openhcs.core.materialization import (
    CsvOptions,
    ImageFileOptions,
    MaterializationSpec,
    NameByArtifactName,
    ROIOptions,
)
from openhcs.core.measurement_row_materialization import (
    DataclassMeasurementColumnarRows,
)
from openhcs.core.memory import numpy
from openhcs.core.pipeline.function_contracts import artifact_outputs


class CellposeModel(Enum):
    """Pretrained Cellpose 3 models."""

    NUCLEI = "nuclei"
    CYTO3 = "cyto3"
    CYTO2 = "cyto2"


@dataclass(frozen=True)
class CellposeCount:
    """Objects found in one plane."""

    slice_index: int
    object_count: int
    model: str
    diameter_px: float


_LOADED_MODELS: dict = {}


def _load(model: CellposeModel, use_gpu: bool):
    key = (model, use_gpu)
    if key not in _LOADED_MODELS:
        _LOADED_MODELS[key] = models.CellposeModel(gpu=use_gpu, model_type=model.value)
    return _LOADED_MODELS[key]


def _warm_up() -> None:
    """Download the default weights, load them and run one small image."""
    _load(CellposeModel.NUCLEI, False).eval(
        np.zeros((64, 64), dtype=np.float32), channels=[0, 0]
    )


@numpy(prepare=_warm_up)
@artifact_outputs(
    ArtifactSpec(
        "cellpose_counts",
        MeasurementsArtifactType,
        materialization=MaterializationSpec(CsvOptions()),
        relations=(ArtifactMeasurementSubjectRelation(),),
    ),
    ArtifactSpec(
        "cellpose_labels",
        ObjectLabelsArtifactType,
        materialization=MaterializationSpec(
            ROIOptions(),
            ImageFileOptions(filename_suffix=".labels.tif", filename_identity=NameByArtifactName),
        ),
    ),
)
def cellpose_segment(
    image,
    model: CellposeModel = CellposeModel.NUCLEI,
    diameter: Optional[float] = None,
    channels: tuple[int, int] = (0, 0),
    flow_threshold: float = 0.4,
    cellprob_threshold: float = 0.0,
    do_3D: bool = False,
    use_gpu: bool = False,
) -> tuple[np.ndarray, DataclassMeasurementColumnarRows, np.ndarray]:
    """Segment cells or nuclei with a pretrained Cellpose model.

    Each plane of the input stack is segmented on its own unless ``do_3D`` is
    set, in which case the stack is treated as one Z volume. The input image is
    passed on unchanged; labels and per-plane counts are extra outputs.

    Args:
        image: Image stack (planes, Y, X).
        model: Pretrained Cellpose model to run.
        diameter: Expected object diameter in pixels. Leave empty to use the
            diameter the model was trained at (17 px for nuclei, 30 px otherwise).
        channels: Cellpose channel pair (segment, nuclear helper). (0, 0) means
            grayscale, where every plane is segmented independently.
        flow_threshold: Maximum flow error per mask; raise it to keep more masks.
        cellprob_threshold: Minimum cell probability; lower it to keep more pixels.
        do_3D: Segment the stack as one 3D volume instead of plane by plane.
        use_gpu: Run on the first CUDA device instead of the CPU.

    Returns:
        The unchanged image, per-plane counts and the label stack.
    """
    network = _load(model, use_gpu)
    settings = dict(
        diameter=diameter,
        channels=list(channels),
        flow_threshold=flow_threshold,
        cellprob_threshold=cellprob_threshold,
    )
    if do_3D:
        labels, _, _ = network.eval(np.asarray(image), do_3D=True, z_axis=0, **settings)
        labels = np.asarray(labels, dtype=np.int32)
    else:
        labels = np.stack(
            [
                np.asarray(network.eval(plane, **settings)[0], dtype=np.int32)
                for plane in np.asarray(image)
            ]
        )
    used_diameter = float(diameter if diameter is not None else network.diam_mean)
    counts = [
        CellposeCount(index, int(plane.max()), model.value, used_diameter)
        for index, plane in enumerate(labels)
    ]
    return image, DataclassMeasurementColumnarRows(counts, CellposeCount), labels
