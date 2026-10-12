"""Which device each declared array library runs on, and the rule that chose it.

A function declares the array library it speaks. The device is a separate
answer: OpenHCS assigns it from the devices that library has on this machine.
Each way of choosing a device is one ``DeviceRule`` subclass; the rules are
tried in the order they are declared here, and the first whose condition holds
supplies the device and is recorded with it.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Iterable, Sequence
from contextlib import AbstractContextManager
from dataclasses import dataclass, field
from typing import ClassVar

from arraybridge.devices import AcceleratorDevice, Device
from arraybridge.libraries import AcceleratorDevices, Array, ArrayLibrary
from metaclass_registry import AutoRegisterMeta

from openhcs.core.runtime_array_values import ArrayPlacement
from openhcs.utils.environment import OpenHCSProcessEnvironment


@dataclass(frozen=True, slots=True)
class DevicePreference:
    """What this process asks of device assignment before any library is consulted."""

    preferred_accelerator: AcceleratorDevice = AcceleratorDevice(0)
    accelerators_excluded: bool = field(
        default_factory=OpenHCSProcessEnvironment.accelerators_excluded
    )


class DeviceRule(ABC, metaclass=AutoRegisterMeta):
    """One reason a library is assigned a device.

    ``name`` identifies the rule in a compiled plan; ``reason`` is the sentence
    shown to a person. A rule instance has no state, so two instances of one
    rule are equal and a pickled plan carries the rule by its class.
    """

    __registry_key__ = "name"
    __skip_if_no_key__ = True

    name: ClassVar[str | None] = None
    reason: ClassVar[str]
    asks_which_accelerators_exist: ClassVar[bool] = False

    def __eq__(self, other: object) -> bool:
        return type(self) is type(other)

    def __hash__(self) -> int:
        return hash(type(self))

    def __repr__(self) -> str:
        return f"<{type(self).__name__}>"

    @abstractmethod
    def applies(self, library: ArrayLibrary[Array], preference: DevicePreference) -> bool:
        """Whether this rule is the one that decides for ``library``."""

    @abstractmethod
    def devices(
        self, library: ArrayLibrary[Array], preference: DevicePreference
    ) -> Sequence[Device]:
        """The devices this rule offers, best first; empty when the library has none."""

    @classmethod
    def ordered(cls) -> tuple[DeviceRule, ...]:
        """Every rule, in declaration order."""

        return tuple(rule() for rule in DeviceRule.__registry__.values())

    @classmethod
    def rules_out(cls, library: ArrayLibrary[Array], preference: DevicePreference) -> bool:
        """Whether ``library`` certainly gets no device, known without asking the machine.

        The rules are read in order up to the first that would have to ask which
        accelerators exist. The function catalogue uses this to leave out
        libraries that cannot run in this process without importing any of them.
        """

        for rule in cls.ordered():
            if rule.asks_which_accelerators_exist:
                return False
            if rule.applies(library, preference):
                return not rule.devices(library, preference)
        return False

    @classmethod
    def assign(
        cls, library: ArrayLibrary[Array], preference: DevicePreference
    ) -> AssignedDevice:
        """The device of the first rule that applies to ``library``."""

        if not library.is_installed():
            raise ValueError(
                f"{library.display_name} is declared by this pipeline but is not "
                "installed."
            )
        for rule in cls.ordered():
            if not rule.applies(library, preference):
                continue
            offered = tuple(rule.devices(library, preference))
            if not offered:
                raise ValueError(
                    f"{library.display_name} has no device to run on: "
                    f"{rule.reason}, and {library.display_name} has no host device."
                )
            return AssignedDevice(ArrayPlacement(library, offered[0]), rule)
        raise ValueError(f"No device rule applies to {library.display_name}.")


class HostRule(DeviceRule):
    """A rule whose answer is the library's host device."""

    def devices(
        self, library: ArrayLibrary[Array], preference: DevicePreference
    ) -> Sequence[Device]:
        return library.host_devices()


class OnlyHostDevices(HostRule):
    name = "only_host_devices"
    reason = "the library keeps arrays only in main memory"

    def applies(self, library: ArrayLibrary[Array], preference: DevicePreference) -> bool:
        return not isinstance(library, AcceleratorDevices)


class AcceleratorsExcluded(HostRule):
    """Decides before any library is asked what accelerators exist."""

    name = "accelerators_excluded"
    reason = "accelerators are excluded for this process"

    def applies(self, library: ArrayLibrary[Array], preference: DevicePreference) -> bool:
        return preference.accelerators_excluded


class AcceleratorRule(DeviceRule):
    """A rule that asks the library which accelerators this machine has."""

    asks_which_accelerators_exist = True


class PreferredAcceleratorPresent(AcceleratorRule):
    name = "preferred_accelerator_present"
    reason = "the preferred accelerator is present"

    def applies(self, library: ArrayLibrary[Array], preference: DevicePreference) -> bool:
        return preference.preferred_accelerator in library.accelerator_devices()

    def devices(
        self, library: ArrayLibrary[Array], preference: DevicePreference
    ) -> Sequence[Device]:
        return (preference.preferred_accelerator,)


class PreferredAcceleratorAbsent(AcceleratorRule):
    name = "preferred_accelerator_absent"
    reason = "the preferred accelerator is absent, so the first accelerator present"

    def applies(self, library: ArrayLibrary[Array], preference: DevicePreference) -> bool:
        return bool(library.accelerator_devices())

    def devices(
        self, library: ArrayLibrary[Array], preference: DevicePreference
    ) -> Sequence[Device]:
        return library.accelerator_devices()


class NoAcceleratorPresent(HostRule):
    """Reached only after the accelerator rules found none."""

    name = "no_accelerator_present"
    asks_which_accelerators_exist = True
    reason = "no accelerator is present"

    def applies(self, library: ArrayLibrary[Array], preference: DevicePreference) -> bool:
        return True


@dataclass(frozen=True, slots=True)
class AssignedDevice:
    """The device one library runs on in a compiled step, and the rule that chose it."""

    placement: ArrayPlacement
    rule: DeviceRule

    @property
    def library(self) -> ArrayLibrary[Array]:
        return self.placement.library

    @property
    def device(self) -> Device:
        return self.placement.device

    def describe(self) -> str:
        return f"{self.library.name} on {self.device.label} ({self.rule.reason})"

    def cleanup_loaded(self) -> None:
        """Release the library's cached memory on an assigned accelerator."""

        if isinstance(self.device, AcceleratorDevice):
            self.library.cleanup_loaded(self.device)


@dataclass(frozen=True, slots=True)
class DeviceAssignment:
    """The assigned device of every array library a step or pipeline declares."""

    assigned: tuple[AssignedDevice, ...] = ()

    def __post_init__(self) -> None:
        libraries = tuple(each.library for each in self.assigned)
        if len(libraries) != len(frozenset(libraries)):
            raise ValueError("DeviceAssignment cannot assign one library twice.")

    @classmethod
    def for_libraries(
        cls,
        libraries: Iterable[ArrayLibrary[Array]],
        preference: DevicePreference,
    ) -> DeviceAssignment:
        """Assign every declared library; every library that cannot run is named."""

        assigned: list[AssignedDevice] = []
        failures: list[str] = []
        for library in sorted(frozenset(libraries), key=lambda each: str(each.name)):
            try:
                assigned.append(DeviceRule.assign(library, preference))
            except ValueError as error:
                failures.append(str(error))
        if failures:
            raise ValueError(" ".join(failures))
        return cls(tuple(assigned))

    @classmethod
    def merge(cls, assignments: Sequence[DeviceAssignment]) -> DeviceAssignment:
        """One assignment covering several steps; a library has one device in all."""

        merged: dict[ArrayLibrary[Array], AssignedDevice] = {}
        for assignment in assignments:
            for each in assignment.assigned:
                existing = merged.setdefault(each.library, each)
                if existing.device != each.device:
                    raise ValueError(
                        f"Conflicting {each.library.name!r} device assignments: "
                        f"{existing.device.label} and {each.device.label}."
                    )
        return cls(
            tuple(merged[library] for library in sorted(merged, key=lambda each: str(each.name)))
        )

    def select(self, libraries: frozenset[ArrayLibrary[Array]]) -> DeviceAssignment:
        """The part of this assignment one step declares."""

        return type(self)(tuple(self.of(library) for library in self._ordered(libraries)))

    @staticmethod
    def _ordered(
        libraries: Iterable[ArrayLibrary[Array]],
    ) -> tuple[ArrayLibrary[Array], ...]:
        return tuple(sorted(libraries, key=lambda each: str(each.name)))

    def of(self, library: ArrayLibrary[Array]) -> AssignedDevice:
        for each in self.assigned:
            if each.library is library:
                return each
        raise ValueError(f"No compiled device assignment exists for {library.name!r}.")

    def scope_for(self, library: ArrayLibrary[Array]) -> AbstractContextManager[None]:
        """A block in which new arrays of ``library`` are created on its device."""

        return library.device_scope(self.of(library).device)

    @property
    def uses_accelerator(self) -> bool:
        """Whether any library was assigned an accelerator."""

        return any(isinstance(each.device, AcceleratorDevice) for each in self.assigned)

    def cleanup_loaded(self) -> None:
        """Release cached accelerator memory of every assigned library."""

        failures: list[Exception] = []
        for each in self.assigned:
            try:
                each.cleanup_loaded()
            except Exception as error:
                error.add_note(f"Cleanup failed for {each.describe()}.")
                failures.append(error)
        if failures:
            raise ExceptionGroup("Compiled device cleanup failed", failures)


__all__ = [
    "AssignedDevice",
    "DeviceAssignment",
    "DevicePreference",
    "DeviceRule",
]
