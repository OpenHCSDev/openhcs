"""A step may return its label image in any array library, on any device.

Each test compiles and executes a real pipeline in this process and reads the
label file OpenHCS wrote. The torch, CuPy and Cellpose tests need those
libraries and are skipped without them; torch runs on whichever device it is
assigned, CuPy needs an accelerator.
"""

from __future__ import annotations

import sys
import types
from dataclasses import dataclass
from pathlib import Path

import openhcs  # noqa: F401 - prefer repository submodules before direct imports
import numpy as np
import pytest
from arraybridge import MemoryType
import tifffile
from polystore.roi import load_rois_from_zip

from openhcs.core import memory
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
from openhcs.core.pipeline.function_contracts import artifact_outputs
from openhcs.core.device_assignment import DevicePreference, DeviceRule
from openhcs.core.steps import FunctionStep
from tests.integration.pipeline_runs import NUCLEUS_CENTRES, SIDE, compile_and_run

EXAMPLE_FUNCTIONS = Path(__file__).resolve().parents[1] / "fixtures" / "custom_functions"

@dataclass(frozen=True)
class PlaneCount:
    slice_index: int
    object_count: int


COUNTS = ArtifactSpec(
    "probe_counts",
    MeasurementsArtifactType,
    materialization=MaterializationSpec(CsvOptions()),
    relations=(ArtifactMeasurementSubjectRelation(),),
)
LABELS = ArtifactSpec(
    "probe_labels",
    ObjectLabelsArtifactType,
    materialization=MaterializationSpec(
        ROIOptions(),
        ImageFileOptions(
            filename_suffix=".labels.tif", filename_identity=NameByArtifactName
        ),
    ),
)


def _square_labels(shape: tuple[int, ...]) -> np.ndarray:
    labels = np.zeros(shape, dtype=np.int32)
    labels[:, 4:12, 4:12] = 1
    labels[:, 40:60, 70:90] = 2
    return labels


def _one_count_per_plane(plane_count: int) -> DataclassMeasurementColumnarRows:
    return DataclassMeasurementColumnarRows(
        [PlaneCount(index, 2) for index in range(plane_count)], PlaneCount
    )


class _DeviceArray:
    """Stands in for ``cupy.ndarray``: no implicit host copy, ``get()`` copies."""

    def __init__(self, host: np.ndarray) -> None:
        self._host = host
        self.shape = host.shape
        self.ndim = host.ndim
        self.dtype = host.dtype
        # A cupy.ndarray names its device; ArrayBridge reads it when it records a copy.
        self.device = types.SimpleNamespace(id=0)

    def __array__(self, dtype: object = None, copy: object = None) -> np.ndarray:
        raise TypeError(
            "Implicit conversion to a NumPy array is not allowed. "
            "Please use `.get()` to construct a NumPy array explicitly."
        )

    def get(self) -> np.ndarray:
        return self._host.copy()


_DeviceArray.__module__ = "cupy"


@memory.numpy
@artifact_outputs(COUNTS, LABELS)
def labels_in_a_device_array(
    image,
) -> tuple[np.ndarray, DataclassMeasurementColumnarRows, np.ndarray]:
    return image, _one_count_per_plane(len(image)), _DeviceArray(
        _square_labels(image.shape)
    )


@memory.numpy
@artifact_outputs(("probe_masks", MaterializationSpec(ROIOptions())))
def masks_in_a_device_array(image):
    return image, _DeviceArray(_square_labels(image.shape))


@pytest.fixture
def device_array_library(monkeypatch):
    """Make ArrayBridge recognise ``_DeviceArray`` as CuPy, without CuPy or a GPU."""
    module = types.ModuleType("cupy")
    module.ndarray = _DeviceArray
    monkeypatch.setitem(sys.modules, "cupy", module)


def _written_labels(results_dir: Path) -> np.ndarray:
    [label_file] = results_dir.glob("*.labels.tif")
    assert list(results_dir.glob("*_rois.roi.zip"))
    return tifffile.imread(label_file)


def test_labels_returned_in_a_device_array_are_written(
    tmp_path, device_array_library
):
    results_dir = compile_and_run(tmp_path, [FunctionStep(func=labels_in_a_device_array)]).results_dir

    np.testing.assert_array_equal(
        np.squeeze(_written_labels(results_dir)), _square_labels((1, SIDE, SIDE))[0]
    )


def test_masks_returned_in_a_device_array_are_written_as_rois(
    tmp_path, device_array_library
):
    results_dir = compile_and_run(tmp_path, [FunctionStep(func=masks_in_a_device_array)]).results_dir

    [roi_archive] = results_dir.glob("*probe_masks*_rois.roi.zip")
    assert len(load_rois_from_zip(roi_archive)) == 2


LABELS_IN_DECLARED_LIBRARY_SOURCE = '''
from dataclasses import dataclass

import numpy as np
import {library}

from openhcs.core.artifacts.kinds import MeasurementsArtifactType, ObjectLabelsArtifactType
from openhcs.core.artifacts.relations import ArtifactMeasurementSubjectRelation
from openhcs.core.artifacts.specs import ArtifactSpec
from openhcs.core.materialization import (
    CsvOptions,
    ImageFileOptions,
    MaterializationSpec,
    NameByArtifactName,
    ROIOptions,
)
from openhcs.core.measurement_row_materialization import DataclassMeasurementColumnarRows
from openhcs.core.memory import {library} as declared_library
from openhcs.core.pipeline.function_contracts import artifact_outputs


@dataclass(frozen=True)
class PlaneCount:
    slice_index: int
    object_count: int


@declared_library
@artifact_outputs(
    ArtifactSpec(
        "probe_counts",
        MeasurementsArtifactType,
        materialization=MaterializationSpec(CsvOptions()),
        relations=(ArtifactMeasurementSubjectRelation(),),
    ),
    ArtifactSpec(
        "probe_labels",
        ObjectLabelsArtifactType,
        materialization=MaterializationSpec(
            ROIOptions(),
            ImageFileOptions(
                filename_suffix=".labels.tif", filename_identity=NameByArtifactName
            ),
        ),
    ),
)
def labels_in_{library}(
    image,
) -> tuple[{array_type}, DataclassMeasurementColumnarRows, {array_type}]:
    """Return two square objects per plane as a label image in {library}."""
    labels = np.zeros(tuple(image.shape), dtype=np.int32)
    labels[:, 4:12, 4:12] = 1
    labels[:, 40:60, 70:90] = 2
    counts = [PlaneCount(index, 2) for index in range(len(labels))]
    return image, DataclassMeasurementColumnarRows(counts, PlaneCount), {labels_on_device}
'''


@pytest.mark.parametrize(
    ("library", "array_type", "labels_on_device"),
    (
        ("torch", "torch.Tensor", "torch.from_numpy(labels).to(image.device)"),
        ("cupy", "cupy.ndarray", "cupy.asarray(labels)"),
    ),
    ids=("torch", "cupy"),
)
def test_labels_returned_in_the_declared_library_on_its_assigned_device_are_written(
    tmp_path, register_source, library, array_type, labels_on_device
):
    pytest.importorskip(library, reason=f"{library} is an optional dependency")
    try:
        DeviceRule.assign(MemoryType(library).library, DevicePreference())
    except ValueError as no_device:
        pytest.skip(str(no_device))
    labels_in_library = register_source(
        LABELS_IN_DECLARED_LIBRARY_SOURCE.format(
            library=library, array_type=array_type, labels_on_device=labels_on_device
        )
    )

    results_dir = compile_and_run(tmp_path / "run", [FunctionStep(func=labels_in_library)]).results_dir

    np.testing.assert_array_equal(
        np.squeeze(_written_labels(results_dir)), _square_labels((1, SIDE, SIDE))[0]
    )


# The example returns the NumPy labels Cellpose produced. These two edits make it
# return them in its declared library, on the device OpenHCS assigned to the step.
CELLPOSE_LABELS_AS_TENSOR = (
    (
        ") -> tuple[torch.Tensor, DataclassMeasurementColumnarRows, np.ndarray]:",
        ") -> tuple[torch.Tensor, DataclassMeasurementColumnarRows, torch.Tensor]:",
    ),
    (
        "    return image, DataclassMeasurementColumnarRows(counts, CellposeCount), labels",
        "    return (\n"
        "        image,\n"
        "        DataclassMeasurementColumnarRows(counts, CellposeCount),\n"
        "        torch.from_numpy(labels).to(image.device),\n"
        "    )",
    ),
)


@pytest.mark.parametrize(
    "edits", ((), CELLPOSE_LABELS_AS_TENSOR), ids=("as written", "tensor labels")
)
def test_cellpose_example_segments_and_is_measured_on_its_assigned_device(
    tmp_path, register_source, edits
):
    pytest.importorskip("torch", reason="torch is an optional dependency")
    pytest.importorskip("cellpose", reason="Cellpose is an optional dependency")
    source = (EXAMPLE_FUNCTIONS / "cellpose_segment.py").read_text()
    for returned_numpy, returned_tensor in edits:
        assert source.count(returned_numpy) == 1
        source = source.replace(returned_numpy, returned_tensor)
    segment = register_source(source)
    measure = register_source(
        (EXAMPLE_FUNCTIONS / "measure_labelled_objects.py").read_text()
    )

    results_dir = compile_and_run(
        tmp_path / "run",
        [
            FunctionStep(func=(segment, {"diameter": 14.0})),
            FunctionStep(func=(measure, {"min_area_px": 30})),
        ],
    ).results_dir

    labels = np.squeeze(_written_labels(results_dir))
    assert sorted(np.unique(labels)) == [0, 1, 2, 3, 4]
    assert all(labels[centre] > 0 for centre in NUCLEUS_CENTRES)
    [measurements] = results_dir.glob("*object_measurements*details.csv")
    assert len(measurements.read_text().strip().splitlines()) == 1 + len(NUCLEUS_CENTRES)
