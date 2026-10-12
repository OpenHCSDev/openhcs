"""The device rule: a declared array library is assigned a device from what exists.

A library that is absent from the environment is stood in for by a module with
only the accelerator-count entry points the real library class reads, so every
case runs the real ``arraybridge`` family code and the real OpenHCS rules.
"""

from __future__ import annotations

import pickle
import sys
from importlib.machinery import ModuleSpec
from types import ModuleType, SimpleNamespace

import pytest
from arraybridge.devices import HOST, AcceleratorDevice
from arraybridge.libraries import AcceleratorDevices, ArrayLibrary, HostDevices

from openhcs.core.device_assignment import (
    DeviceAssignment,
    DevicePreference,
    DeviceRule,
)
from openhcs.utils.environment import OpenHCSProcessEnvironment

ALLOWED = DevicePreference(accelerators_excluded=False)
EXCLUDED = DevicePreference(accelerators_excluded=True)


def _never_asked() -> int:
    raise AssertionError("the library was asked which accelerators exist")


def _stand_in(name: str, accelerator_count) -> ModuleType:
    """A module answering only how many accelerators there are."""

    count = accelerator_count if callable(accelerator_count) else lambda: accelerator_count
    module = ModuleType(name)
    module.__spec__ = ModuleSpec(name, None)
    module.cuda = SimpleNamespace(
        is_available=lambda: count() > 0,
        device_count=count,
        runtime=SimpleNamespace(getDeviceCount=count),
    )
    return module


@pytest.fixture
def library(monkeypatch):
    def install(name: str, accelerator_count) -> ArrayLibrary:
        monkeypatch.setitem(sys.modules, name, _stand_in(name, accelerator_count))
        return ArrayLibrary.named(name)

    return install


@pytest.mark.parametrize(
    ("name", "accelerators", "preference", "device", "rule"),
    [
        ("torch", 2, ALLOWED, AcceleratorDevice(0), "preferred_accelerator_present"),
        (
            "torch",
            2,
            DevicePreference(AcceleratorDevice(5), accelerators_excluded=False),
            AcceleratorDevice(0),
            "preferred_accelerator_absent",
        ),
        ("torch", 0, ALLOWED, HOST, "no_accelerator_present"),
        ("torch", _never_asked, EXCLUDED, HOST, "accelerators_excluded"),
        ("cupy", 1, ALLOWED, AcceleratorDevice(0), "preferred_accelerator_present"),
    ],
)
def test_a_library_is_assigned_a_device_by_the_first_rule_that_applies(
    library, name, accelerators, preference, device, rule
) -> None:
    assigned = DeviceRule.assign(library(name, accelerators), preference)

    assert (assigned.device, assigned.rule.name) == (device, rule)
    assert assigned.rule.reason in assigned.describe()


@pytest.mark.parametrize("preference", [ALLOWED, EXCLUDED])
def test_numpy_is_assigned_its_only_device(preference) -> None:
    assigned = DeviceRule.assign(ArrayLibrary.named("numpy"), preference)

    assert (assigned.device, assigned.rule.name) == (HOST, "only_host_devices")


@pytest.mark.parametrize(
    ("accelerators", "preference", "reason"),
    [
        (0, ALLOWED, "no accelerator is present"),
        (_never_asked, EXCLUDED, "accelerators are excluded for this process"),
    ],
)
def test_a_library_with_no_host_device_and_no_accelerator_is_a_named_error(
    library, accelerators, preference, reason
) -> None:
    with pytest.raises(ValueError) as error:
        DeviceAssignment.for_libraries((library("cupy", accelerators),), preference)

    assert "CuPy has no device to run on" in str(error.value)
    assert reason in str(error.value)
    assert "CuPy has no host device" in str(error.value)


def test_a_declared_library_that_is_not_installed_is_a_named_error(monkeypatch) -> None:
    tensorflow = ArrayLibrary.named("tensorflow")
    monkeypatch.setattr(type(tensorflow), "is_installed", lambda self: False)

    with pytest.raises(ValueError, match="TensorFlow.*not installed"):
        DeviceRule.assign(tensorflow, ALLOWED)


def test_jax_without_an_accelerator_is_assigned_host() -> None:
    jax = ArrayLibrary.named("jax")
    if not jax.is_installed():
        pytest.skip("JAX is not installed")
    if jax.accelerator_devices():
        pytest.skip("this machine has a JAX accelerator")

    assigned = DeviceRule.assign(jax, ALLOWED)

    assert (assigned.device, assigned.rule.name) == (HOST, "no_accelerator_present")


def test_excluding_accelerators_rules_out_exactly_the_libraries_without_a_host_device(
    monkeypatch,
) -> None:
    for each in ArrayLibrary.all():
        monkeypatch.setattr(
            type(each), "accelerator_devices", lambda self: _never_asked()
        )

    ruled_out = {
        str(each.name) for each in ArrayLibrary.all() if DeviceRule.rules_out(each, EXCLUDED)
    }

    assert ruled_out == {
        str(each.name) for each in ArrayLibrary.all() if not isinstance(each, HostDevices)
    }
    assert ruled_out == {"cupy", "pyclesperanto"}
    assert not any(DeviceRule.rules_out(each, ALLOWED) for each in ArrayLibrary.all())


def test_the_catalogue_keeps_every_installed_library_that_has_a_device(monkeypatch) -> None:
    from openhcs.processing.backends.lib_registry.openhcs_registry import (
        _allowed_openhcs_memory_types,
    )

    for each in ArrayLibrary.all():
        monkeypatch.setattr(type(each), "is_installed", lambda self: True)
    monkeypatch.setenv(OpenHCSProcessEnvironment.cpu_only_key, "true")
    with_accelerators_excluded = _allowed_openhcs_memory_types()
    monkeypatch.delenv(OpenHCSProcessEnvironment.cpu_only_key)

    assert with_accelerators_excluded == {"numpy", "torch", "tensorflow", "jax"}
    assert _allowed_openhcs_memory_types() == set(ArrayLibrary.__registry__)


def test_an_assignment_reaches_a_worker_with_its_rules(library) -> None:
    assignment = DeviceAssignment.for_libraries(
        (library("torch", 1), ArrayLibrary.named("numpy")), ALLOWED
    )

    received = pickle.loads(pickle.dumps(assignment))

    assert received == assignment
    assert [(str(each.library.name), each.device, each.rule.name) for each in received.assigned] == [
        ("numpy", HOST, "only_host_devices"),
        ("torch", AcceleratorDevice(0), "preferred_accelerator_present"),
    ]
    assert received.of(ArrayLibrary.named("torch")).library is ArrayLibrary.named("torch")


def test_accelerator_use_is_asked_of_the_assigned_devices_not_the_declaration(library) -> None:
    on_host = DeviceAssignment.for_libraries((library("torch", 0),), ALLOWED)
    on_accelerator = DeviceAssignment.for_libraries((library("torch", 1),), ALLOWED)

    assert isinstance(ArrayLibrary.named("torch"), AcceleratorDevices)
    assert not on_host.uses_accelerator
    assert on_accelerator.uses_accelerator


def test_only_assigned_accelerators_are_released(library, monkeypatch) -> None:
    torch = library("torch", 1)
    released: list[object] = []
    monkeypatch.setattr(
        type(torch), "cleanup_loaded", lambda self, device=None: released.append(device)
    )
    assignment = DeviceAssignment.for_libraries((torch, ArrayLibrary.named("numpy")), ALLOWED)

    assignment.cleanup_loaded()

    assert released == [AcceleratorDevice(0)]


def test_steps_that_disagree_on_a_library_device_cannot_be_merged(library) -> None:
    on_accelerator = DeviceAssignment.for_libraries((library("torch", 1),), ALLOWED)
    on_host = DeviceAssignment.for_libraries((library("torch", 1),), EXCLUDED)

    with pytest.raises(ValueError, match="Conflicting 'torch' device assignments"):
        DeviceAssignment.merge((on_accelerator, on_host))
    assert DeviceAssignment.merge((on_host, on_host)) == on_host


def test_excluding_accelerators_is_one_flag_and_tells_jax() -> None:
    environment: dict[str, str] = {}

    OpenHCSProcessEnvironment.exclude_accelerators(environment)

    assert OpenHCSProcessEnvironment.accelerators_excluded(environment)
    assert environment[OpenHCSProcessEnvironment.cpu_only_key] == "true"
    assert environment[OpenHCSProcessEnvironment.jax_platforms_key] == "cpu"
    assert not any("NO_GPU" in key for key in environment)
