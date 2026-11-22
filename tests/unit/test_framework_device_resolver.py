import pytest

from arraybridge import MemoryType
from arraybridge.devices import AcceleratorDevice

from openhcs.core.execution.compiled_step_plan import FrameworkDeviceAssignment
from openhcs.core.util.framework_device_resolver import FrameworkDeviceResolver
from openhcs.utils.environment import OpenHCSProcessEnvironment


def test_empty_footprint_does_not_import_frameworks(on_every_library) -> None:
    on_every_library(
        "import_if_installed",
        lambda _library: (_ for _ in ()).throw(
            AssertionError("empty footprint imported a GPU runtime")
        ),
    )

    assert FrameworkDeviceResolver().resolve(frozenset()).bindings == ()


def test_cpu_only_authority_rejects_gpu_footprint_before_import(
    monkeypatch, on_every_library,
) -> None:
    monkeypatch.setenv(OpenHCSProcessEnvironment.cpu_only_key, "true")
    on_every_library(
        "import_if_installed",
        lambda _library: (_ for _ in ()).throw(
            AssertionError("CPU-only resolution imported a GPU runtime")
        ),
    )

    with pytest.raises(ValueError, match="GPU imports are disabled"):
        FrameworkDeviceResolver().resolve(frozenset({MemoryType.TORCH}))


def test_framework_namespaces_receive_independent_local_devices(
    monkeypatch, on_every_library,
) -> None:
    modules = {
        MemoryType.CUPY: object(),
        MemoryType.TORCH: object(),
    }
    available = {
        MemoryType.CUPY: (2, 3),
        MemoryType.TORCH: (5,),
    }
    monkeypatch.delenv(OpenHCSProcessEnvironment.cpu_only_key, raising=False)
    monkeypatch.delenv(
        OpenHCSProcessEnvironment.subprocess_no_gpu_key,
        raising=False,
    )
    monkeypatch.delenv(
        OpenHCSProcessEnvironment.polystore_subprocess_no_gpu_key,
        raising=False,
    )
    on_every_library(
        "import_if_installed",
        lambda library: modules[MemoryType(library.name)],
    )
    on_every_library(
        "accelerator_devices",
        lambda library: tuple(
            AcceleratorDevice(index) for index in available[MemoryType(library.name)]
        ),
    )

    assignment = FrameworkDeviceResolver(preferred_device_id=3).resolve(
        frozenset(modules)
    )

    assert assignment.device_for(MemoryType.CUPY) == AcceleratorDevice(3)
    assert assignment.device_for(MemoryType.TORCH) == AcceleratorDevice(5)


def test_compiled_cleanup_visits_only_assigned_framework_devices(on_every_library) -> None:
    cleaned = []
    on_every_library(
        "cleanup_loaded",
        lambda library, device=None: cleaned.append((MemoryType(library.name), device.index)),
    )
    assignment = FrameworkDeviceAssignment.from_mapping(
        {
            MemoryType.CUPY: 2,
            MemoryType.TORCH: 5,
        }
    )

    assignment.cleanup_loaded()

    assert cleaned == [
        (MemoryType.CUPY, 2),
        (MemoryType.TORCH, 5),
    ]


def test_compiled_cleanup_attempts_every_binding_before_reporting_failures(
    on_every_library,
) -> None:
    cleaned = []

    def cleanup(library, device=None):
        cleaned.append((MemoryType(library.name), device.index))
        if library is MemoryType.CUPY.library:
            raise RuntimeError("cupy cleanup failed")

    on_every_library("cleanup_loaded", cleanup)
    assignment = FrameworkDeviceAssignment.from_mapping(
        {
            MemoryType.CUPY: 2,
            MemoryType.JAX: 4,
            MemoryType.TORCH: 5,
        }
    )

    with pytest.raises(ExceptionGroup) as caught:
        assignment.cleanup_loaded()

    assert cleaned == [
        (MemoryType.CUPY, 2),
        (MemoryType.JAX, 4),
        (MemoryType.TORCH, 5),
    ]
    assert [str(error) for error in caught.value.exceptions] == ["cupy cleanup failed"]
