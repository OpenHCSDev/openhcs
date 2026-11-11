"""What the derived Cellpose functions still need from the platform.

Each test fails today for the stated reason and is written to pass, unchanged,
when the named branch lands.
"""

import inspect
import json

import pytest

pytest.importorskip("cellpose", reason="Cellpose is an optional dependency")

import cellpose
import torch

from openhcs.processing.backends.lib_registry import model_library
from openhcs.processing.backends.lib_registry.derived import cellpose as derived
from openhcs.processing.custom_functions import CustomFunctionManager
from tests.cellpose_pipeline_support import (
    DIAMETER,
    EXAMPLES,
    NUCLEI,
    make_plate,
    one,
    run_pipeline,
    step,
)


@pytest.mark.xfail(
    strict=True,
    reason="refactor/DL2-declared-files-between-steps: on main a declared input file "
    "must exist when the pipeline is compiled, so a model trained by one step "
    "cannot be the input of a later step ('Declared input file does not exist').",
)
def test_train_then_segment_with_the_trained_model_in_one_pipeline(tmp_path):
    plate = make_plate(tmp_path, wells=("A01", "B01"))
    trained = tmp_path / "trained" / "models" / "tiny"
    root = run_pipeline(
        plate,
        [
            step(derived.segment, model_type=NUCLEI, diameter=DIAMETER),
            step(
                derived.train_segmentation,
                model_type=NUCLEI,
                save_path=tmp_path / "trained",
                model_name="tiny",
                n_epochs=2,
                min_train_masks=1,
                channels=(0, 0),
            ),
            step(derived.segment, pretrained_model=trained, diameter=DIAMETER),
        ],
    )
    assert trained.is_file()
    # One training call for the plate: one loss table, not one for each well.
    assert len(sorted(root.rglob("*losses_step1_details.csv"))) == 1
    assert len(sorted(root.rglob("*cellpose_labels_step2.cellpose_labels.tif"))) == 2


@pytest.mark.xfail(
    strict=True,
    reason="refactor/DL1-device-and-memory-types: on main the platform assigns no "
    "device to a NumPy-declared function, so Cellpose's own `gpu` is a control of "
    "the derived functions that build a model.",
)
def test_the_platform_not_a_gpu_control_chooses_the_device():
    for name, function in derived.library.functions.items():
        assert "gpu" not in inspect.signature(function).parameters, name


@pytest.mark.xfail(
    strict=True,
    condition=not torch.cuda.is_available(),
    reason="refactor/DL1-device-and-memory-types: on main a torch-executing "
    "declaration does not compile on a machine without CUDA.",
)
def test_a_torch_executing_declaration_compiles_without_cuda(tmp_path, monkeypatch):
    monkeypatch.setenv("XDG_DATA_HOME", str(tmp_path / "data-home"))
    (segment,) = CustomFunctionManager().register_from_code(
        (EXAMPLES / "cellpose_segment.py").read_text(), persist=True, emit_signal=False
    )
    root = run_pipeline(make_plate(tmp_path), [step(segment, diameter=DIAMETER)])
    assert sorted(root.rglob("*cellpose_labels*.tif"))


@pytest.mark.xfail(
    strict=True,
    reason="refactor/DL4-custom-function-preparation: on main the preparation hook "
    "takes no arguments, so only the default model can be loaded before readiness.",
)
def test_preparation_loads_the_model_the_step_selects(monkeypatch):
    monkeypatch.setattr(model_library, "_SHARED_RESOURCES", {})
    derived.segment.__openhcs_prepare__(model_type=NUCLEI)
    (built,) = model_library._SHARED_RESOURCES
    assert ("model_type", "nuclei") in built


@pytest.mark.xfail(
    strict=True,
    reason="refactor/DL3-output-provenance: on main openhcs_metadata.json records "
    "neither the function, nor the model, nor the Cellpose version.",
)
def test_output_metadata_names_the_function_the_model_and_the_cellpose_version(tmp_path):
    root = run_pipeline(
        make_plate(tmp_path), [step(derived.segment, model_type=NUCLEI, diameter=DIAMETER)]
    )
    recorded = one(root, "*_cellpose/openhcs_metadata.json").read_text()
    assert json.loads(recorded)
    assert "cellpose:segment" in recorded
    assert "nuclei" in recorded
    assert cellpose.version in recorded
