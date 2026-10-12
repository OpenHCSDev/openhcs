"""The example custom functions register through the user path and behave as documented.

Cellpose and torch are optional: tests that need them are skipped when they are
not installed; the missing-dependency test runs everywhere.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pytest

import openhcs.processing.custom_functions.manager as manager_module
from openhcs.core.callable_contract import CallableContract
from openhcs.processing.custom_functions import CustomFunctionManager, ValidationError
from openhcs.processing.custom_functions.runtime_registry import (
    CustomFunctionRuntimeRegistry,
)

EXAMPLES = Path(__file__).resolve().parents[2] / "examples" / "custom_functions"


@pytest.fixture
def register(monkeypatch, tmp_path):
    """Register an example source the way the editor and the MCP service do."""
    storage_dir = tmp_path / "custom_functions"
    storage_dir.mkdir()
    monkeypatch.setattr(
        manager_module, "get_data_file_path", lambda _name, *, create=True: storage_dir
    )
    for attribute in ("_declarations_by_name", "_published_exports",
                      "_preparation_outcomes", "_preparation_threads"):
        monkeypatch.setattr(CustomFunctionRuntimeRegistry, attribute, {})
    monkeypatch.setattr(CustomFunctionRuntimeRegistry, "_source_revision", None)

    def register_example(name: str):
        [function] = CustomFunctionManager().register_from_code(
            (EXAMPLES / f"{name}.py").read_text(), persist=False, emit_signal=False,
        )
        return function

    yield register_example
    CustomFunctionRuntimeRegistry.clear()


def _nuclei_image(side: int = 128) -> np.ndarray:
    yy, xx = np.mgrid[:side, :side]
    image = np.full((side, side), 200.0, dtype=np.float32)
    for centre_y, centre_x in ((30, 30), (30, 90), (90, 40), (95, 100)):
        image += 3000.0 * np.exp(-((yy - centre_y) ** 2 + (xx - centre_x) ** 2) / (2 * 6.0**2))
    return image


def test_measure_labelled_objects_measures_each_label(register):
    measure = register("measure_labelled_objects")
    contract = CallableContract.from_callable(measure)
    assert (contract.input_memory_type, contract.output_memory_type) == ("numpy", "numpy")
    assert [spec.name for spec in contract.artifact_inputs] == ["cellpose_labels"]

    image = _nuclei_image()[None]
    labels = np.zeros_like(image, dtype=np.int32)
    labels[0, 20:40, 20:40] = 1
    labels[0, 85:90, 35:40] = 2
    returned, rows = measure(image, labels=labels, min_area_px=30)

    assert returned is image
    assert [(row.label, row.area_px) for row in rows.rows] == [(1, 400.0)]
    assert rows.rows[0].mean_intensity == pytest.approx(float(image[0, 20:40, 20:40].mean()))


def test_cellpose_source_is_rejected_at_registration_when_its_import_fails(
    register, monkeypatch
):
    monkeypatch.setitem(sys.modules, "cellpose", None)
    monkeypatch.setitem(sys.modules, "torch", None)
    with pytest.raises(ValidationError, match="Code execution failed: .*(cellpose|torch)"):
        register("cellpose_segment")
    assert CustomFunctionRuntimeRegistry.metadata_for_name("cellpose_segment") is None


def test_cellpose_segment_declares_torch_and_typed_outputs_and_segments_blobs(register):
    torch = pytest.importorskip("torch", reason="torch is an optional dependency")
    pytest.importorskip("cellpose", reason="Cellpose is an optional dependency")
    segment = register("cellpose_segment")
    contract = CallableContract.from_callable(segment)
    assert (contract.input_memory_type, contract.output_memory_type) == ("torch", "torch")
    assert {spec.name: spec.artifact_type.value for spec in contract.artifact_outputs} == {
        "cellpose_counts": "measurements",
        "cellpose_labels": "object_labels",
    }

    image = torch.from_numpy(_nuclei_image()[None])
    returned, counts, labels = segment(image, diameter=14.0)

    assert returned is image
    assert isinstance(labels, np.ndarray) and labels.shape == (1, 128, 128)
    assert counts.rows[0].object_count == int(labels.max()) == 4
    assert counts.rows[0].model == "nuclei"


def test_n2v2_fit_writes_one_reproducible_model_and_denoise_is_deterministic(
    register, tmp_path
):
    torch = pytest.importorskip("torch", reason="torch is an optional dependency")
    fit = register("n2v2_fit")
    denoise = register("n2v2_denoise")
    assert set(CallableContract.from_callable(fit).declared_path_parameters) == {"model_file"}
    assert set(CallableContract.from_callable(denoise).declared_path_parameters) == {"model_file"}

    noisy = torch.from_numpy(
        np.random.default_rng(0).normal(1000.0, 100.0, (2, 64, 64)).astype(np.float32)
    )
    settings = dict(epochs=1, patches_per_epoch=8, patch_size=32)
    first, second = tmp_path / "first.pt", tmp_path / "second.pt"
    assert fit(noisy, model_file=first, **settings) is noisy
    fit(noisy, model_file=second, **settings)
    # torch.save embeds the file's own name in the archive, so compare contents, not bytes.
    one, two = (torch.load(path, weights_only=True) for path in (first, second))
    assert one["training"] == two["training"]
    assert all(torch.equal(one["weights"][name], two["weights"][name]) for name in one["weights"])

    once = denoise(noisy, model_file=first, tile_size=32)
    again = denoise(noisy, model_file=first, tile_size=32)
    assert once.shape == noisy.shape and once.dtype == torch.float32
    assert torch.equal(once, again)
