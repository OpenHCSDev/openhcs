"""A function declares its array library; the platform assigns the device.

Each test registers a custom-function source, compiles it and executes it
through the real orchestrator in this process. What the test expects is derived
from the environment it runs in, so the same file is run once per mode:

* as is (an accelerator is assigned when the library has one);
* ``CUDA_VISIBLE_DEVICES=`` (no accelerator is present: host is assigned);
* ``OPENHCS_CPU_ONLY=1`` (accelerators are excluded: host is assigned, the
  library is never asked what accelerators exist, and CUDA is never started).

The numeric result is compared with one fixed NumPy computation, so it is the
same in every mode.
"""

from __future__ import annotations

import inspect
import json

import openhcs  # noqa: F401 - prefer repository submodules before direct imports
import numpy as np
import pytest
from arraybridge import MemoryType
from arraybridge.devices import HOST, Device
from arraybridge.libraries import Array, ArrayLibrary

from openhcs.core.runtime_array_values import ArrayPlacement
from openhcs.core.steps import FunctionStep
from openhcs.processing.backends.lib_registry.openhcs_registry import OpenHCSRegistry
from openhcs.utils.environment import OpenHCSProcessEnvironment
from tests.integration.pipeline_runs import (
    compile_and_run,
    compiled_pipeline,
    nuclei_image,
)

QUARTER_SOURCE = '''
import {module} as array_module

from openhcs.core.memory import {library} as declared_library
from openhcs.core.runtime_array_values import ArrayPlacement

PLACEMENTS_SEEN = []


@declared_library
def quarter_in_{library}(image):
    """Divide every pixel by four, rounding down, in {library}."""
    PLACEMENTS_SEEN.append(ArrayPlacement.of(image))
    return array_module.floor({as_float} / 4)
'''
QUARTER_SOURCES = {
    "torch": QUARTER_SOURCE.format(
        library="torch", module="torch", as_float="image.to(array_module.float32)"
    ),
    "jax": QUARTER_SOURCE.format(
        library="jax", module="jax.numpy", as_float="image.astype(array_module.float32)"
    ),
}

IDENTITY_SOURCE = '''
from openhcs.core.memory import {library} as declared_library


@declared_library
def unchanged_in_{library}(image):
    """Return the image as it arrived."""
    return image
'''


def _expected_device_and_reason(library: ArrayLibrary[Array]) -> tuple[Device, str]:
    """What the rules must give ``library`` in this process's environment."""
    if OpenHCSProcessEnvironment.accelerators_excluded():
        return HOST, "accelerators are excluded for this process"
    accelerators = library.accelerator_devices()
    if accelerators:
        return accelerators[0], "the preferred accelerator is present"
    return HOST, "no accelerator is present"


def _catalogue_libraries() -> list[str]:
    """The array libraries whose functions this process's catalogue holds."""
    registry = OpenHCSRegistry()
    registry.MODULES_TO_SCAN = []
    return json.loads(registry.get_discovery_signature())["context"][
        "allowed_memory_types"
    ]


@pytest.mark.parametrize("name", ("torch", "jax"))
def test_a_library_with_a_host_device_runs_on_the_device_its_environment_implies(
    tmp_path, register_source, name
):
    pytest.importorskip(name, reason=f"{name} is an optional dependency")
    library = MemoryType(name).library
    device, reason = _expected_device_and_reason(library)
    quarter = register_source(QUARTER_SOURCES[name])

    run = compile_and_run(tmp_path / "run", [FunctionStep(func=quarter)])

    [step_plan] = run.step_plans.values()
    assigned = step_plan.device_assignment.of(library)
    assert (assigned.device, assigned.rule.reason) == (device, reason)
    assert assigned.describe() == f"{name} on {device.label} ({reason})"
    assert inspect.unwrap(quarter).__globals__["PLACEMENTS_SEEN"] == [
        ArrayPlacement(library, device)
    ]
    assert name in _catalogue_libraries()
    [written] = run.output_images()
    np.testing.assert_array_equal(np.squeeze(written), nuclei_image() // 4)


def test_excluding_accelerators_never_starts_cuda(tmp_path, register_source):
    torch = pytest.importorskip("torch", reason="torch is an optional dependency")
    if not OpenHCSProcessEnvironment.accelerators_excluded():
        pytest.skip("accelerators are not excluded in this run")
    quarter = register_source(QUARTER_SOURCES["torch"])

    compile_and_run(tmp_path / "run", [FunctionStep(func=quarter)])

    assert not torch.cuda.is_initialized()


def test_a_library_without_a_host_device_needs_an_accelerator_to_compile(
    tmp_path, register_source, stand_in_library
):
    library = MemoryType.CUPY.library
    if not library.is_installed():
        # The real CuPy class, reading a module that reports no accelerator.
        stand_in_library("cupy", 0)
    device, reason = _expected_device_and_reason(library)
    unchanged = register_source(IDENTITY_SOURCE.format(library="cupy"))
    steps = [FunctionStep(func=unchanged)]

    if device != HOST:
        with compiled_pipeline(tmp_path / "run", steps) as (_, compiled, _queue):
            [context] = compiled.runtime_contexts.values()
            [step_plan] = context.step_plans.values()
        assert step_plan.device_assignment.of(library).device == device
        return

    with pytest.raises(Exception) as error:
        with compiled_pipeline(tmp_path / "run", steps):
            pass
    message = str(error.value)
    assert "CuPy has no device to run on" in message
    assert reason in message
    assert "CuPy has no host device" in message


def test_an_image_output_aligned_to_its_sources_stays_on_the_torch_host_device():
    torch = pytest.importorskip("torch", reason="torch is an optional dependency")
    from openhcs.core.runtime_image_values import ImagePayload
    from openhcs.core.runtime_plane_projection import (
        RuntimePlaneAxisValueProjection,
        RuntimeSlicePlaneAxis,
    )
    from openhcs.core.runtime_slice_alignment import RuntimeSliceAlignedValues

    sources = RuntimeSliceAlignedValues(
        tuple(ImagePayload.of(np.ones((16, 16), np.float32)) for _ in range(2))
    )
    output = ImagePayload.of(torch.full((2, 16, 16), 3.0))

    aligned = sources.contextualize_image_output(
        output,
        RuntimePlaneAxisValueProjection.preserve(axis=RuntimeSlicePlaneAxis, axis_size=2),
    )

    assert ArrayPlacement.of(aligned.data) == ArrayPlacement(
        MemoryType.TORCH.library, HOST
    )
    np.testing.assert_array_equal(
        MemoryType.TORCH.library.to_numpy(aligned.data), np.full((2, 16, 16), 3.0)
    )
