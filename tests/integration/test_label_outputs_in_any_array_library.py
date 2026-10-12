"""A step may return its label image in any array library, on any device.

Each test compiles and executes a real pipeline in this process and reads the
label file OpenHCS wrote. The torch, CuPy and Cellpose tests need those
libraries and a CUDA device, and are skipped without them.
"""

from __future__ import annotations

import io
import sys
import types
from contextlib import redirect_stderr, redirect_stdout
from dataclasses import dataclass
from multiprocessing import SimpleQueue
from pathlib import Path

import openhcs  # noqa: F401 - prefer repository submodules before direct imports
import numpy as np
import pytest
import tifffile
from polystore.roi import load_rois_from_zip
from objectstate import ObjectStateRegistry
from objectstate.lazy_factory import ensure_global_config_context

import openhcs.processing.custom_functions.manager as manager_module
from openhcs.core import memory
from openhcs.core.artifacts.kinds import (
    MeasurementsArtifactType,
    ObjectLabelsArtifactType,
)
from openhcs.core.artifacts.relations import ArtifactMeasurementSubjectRelation
from openhcs.core.artifacts.specs import ArtifactSpec
from openhcs.core.config import (
    GlobalPipelineConfig,
    LazyPathPlanningConfig,
    PipelineConfig,
)
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
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.pipeline.function_contracts import artifact_outputs
from openhcs.core.progress import ProgressExecutionContext, set_progress_queue
from openhcs.core.steps import FunctionStep
from openhcs.demo.synthetic_data import SyntheticMicroscopyGenerator
from openhcs.processing.custom_functions import CustomFunctionManager
from openhcs.processing.custom_functions.runtime_registry import (
    CustomFunctionRuntimeRegistry,
)

EXAMPLE_FUNCTIONS = Path(__file__).resolve().parents[1] / "fixtures" / "custom_functions"
SIDE = 128
NUCLEUS_CENTRES = ((30, 30), (30, 90), (90, 40), (95, 100))


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


def _nuclei_image() -> np.ndarray:
    yy, xx = np.mgrid[:SIDE, :SIDE]
    image = np.full((SIDE, SIDE), 200.0)
    for centre_y, centre_x in NUCLEUS_CENTRES:
        image += 3000.0 * np.exp(
            -((yy - centre_y) ** 2 + (xx - centre_x) ** 2) / (2 * 6.0**2)
        )
    return image.astype(np.uint16)


def _run_pipeline(root: Path, steps: list[FunctionStep]) -> Path:
    """Compile and execute ``steps`` on a one-field plate; return the results folder."""
    plate = root / "plate"
    with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
        SyntheticMicroscopyGenerator(
            output_dir=str(plate),
            grid_size=(1, 1),
            tile_size=(SIDE, SIDE),
            overlap_percent=10,
            stage_error_px=1,
            wavelengths=1,
            z_stack_levels=1,
            num_cells=2,
            wells=["A01"],
            format="ImageXpress",
            random_seed=7,
        ).generate_dataset()
    for field in (plate / "TimePoint_1").glob("*.tif"):
        tifffile.imwrite(field, _nuclei_image())

    ObjectStateRegistry.clear()
    queue = SimpleQueue()
    set_progress_queue(queue)
    try:
        ensure_global_config_context(
            GlobalPipelineConfig,
            GlobalPipelineConfig(num_workers=1, use_threading=True),
        )
        orchestrator = PipelineOrchestrator(
            plate,
            pipeline_config=PipelineConfig(
                path_planning_config=LazyPathPlanningConfig(
                    global_output_folder=root / "out"
                )
            ),
        ).initialize()
        compiled = orchestrator.compile_pipelines(
            pipeline_definition=steps, enable_visualizer_override=False
        )
        results = orchestrator.execute_compiled_bundle(
            execution_bundle=compiled,
            max_workers=1,
            progress_queue=queue,
            progress_context=ProgressExecutionContext(
                execution_id=str(root), subject_id=str(root)
            ),
        )
    finally:
        set_progress_queue(None)
    failures = {
        key: result.error_message
        for key, result in results.items()
        if not result.is_success()
    }
    assert not failures, failures
    [results_dir] = (root / "out").glob("*/results")
    return results_dir


def _written_labels(results_dir: Path) -> np.ndarray:
    [label_file] = results_dir.glob("*.labels.tif")
    assert list(results_dir.glob("*_rois.roi.zip"))
    return tifffile.imread(label_file)


def test_labels_returned_in_a_device_array_are_written(
    tmp_path, device_array_library
):
    results_dir = _run_pipeline(tmp_path, [FunctionStep(func=labels_in_a_device_array)])

    np.testing.assert_array_equal(
        np.squeeze(_written_labels(results_dir)), _square_labels((1, SIDE, SIDE))[0]
    )


def test_masks_returned_in_a_device_array_are_written_as_rois(
    tmp_path, device_array_library
):
    results_dir = _run_pipeline(tmp_path, [FunctionStep(func=masks_in_a_device_array)])

    [roi_archive] = results_dir.glob("*probe_masks*_rois.roi.zip")
    assert len(load_rois_from_zip(roi_archive)) == 2


@pytest.fixture
def register_source(monkeypatch, tmp_path):
    """Register a custom-function source the way the editor and the MCP service do."""
    storage_dir = tmp_path / "custom_functions"
    storage_dir.mkdir()
    monkeypatch.setattr(
        manager_module, "get_data_file_path", lambda _name, *, create=True: storage_dir
    )
    for attribute in (
        "_declarations_by_name",
        "_published_exports",
        "_preparation_outcomes",
        "_preparation_threads",
    ):
        monkeypatch.setattr(CustomFunctionRuntimeRegistry, attribute, {})
    monkeypatch.setattr(CustomFunctionRuntimeRegistry, "_source_revision", None)

    def register(source: str):
        [function] = CustomFunctionManager().register_from_code(
            source, persist=False, emit_signal=False
        )
        return function

    yield register
    CustomFunctionRuntimeRegistry.clear()


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
    ids=("torch-cuda", "cupy"),
)
def test_labels_returned_on_a_gpu_in_the_declared_library_are_written(
    tmp_path, register_source, library, array_type, labels_on_device
):
    pytest.importorskip(library, reason=f"{library} is an optional dependency")
    torch = pytest.importorskip("torch", reason="the CUDA check uses torch")
    if not torch.cuda.is_available():
        pytest.skip("a GPU-declared step compiles only with a CUDA device")
    labels_on_gpu = register_source(
        LABELS_IN_DECLARED_LIBRARY_SOURCE.format(
            library=library, array_type=array_type, labels_on_device=labels_on_device
        )
    )

    results_dir = _run_pipeline(tmp_path / "run", [FunctionStep(func=labels_on_gpu)])

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


def test_cellpose_example_returning_tensor_labels_segments_and_is_measured(
    tmp_path, register_source
):
    torch = pytest.importorskip("torch", reason="torch is an optional dependency")
    pytest.importorskip("cellpose", reason="Cellpose is an optional dependency")
    if not torch.cuda.is_available():
        pytest.skip("a torch-declared step compiles only with a CUDA device")
    source = (EXAMPLE_FUNCTIONS / "cellpose_segment.py").read_text()
    for returned_numpy, returned_tensor in CELLPOSE_LABELS_AS_TENSOR:
        assert source.count(returned_numpy) == 1
        source = source.replace(returned_numpy, returned_tensor)
    segment = register_source(source)
    measure = register_source(
        (EXAMPLE_FUNCTIONS / "measure_labelled_objects.py").read_text()
    )

    results_dir = _run_pipeline(
        tmp_path / "run",
        [
            FunctionStep(func=(segment, {"diameter": 14.0})),
            FunctionStep(func=(measure, {"min_area_px": 30})),
        ],
    )

    labels = np.squeeze(_written_labels(results_dir))
    assert sorted(np.unique(labels)) == [0, 1, 2, 3, 4]
    assert all(labels[centre] > 0 for centre in NUCLEUS_CENTRES)
    [measurements] = results_dir.glob("*object_measurements*details.csv")
    assert len(measurements.read_text().strip().splitlines()) == 1 + len(NUCLEUS_CENTRES)
