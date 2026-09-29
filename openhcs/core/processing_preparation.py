"""Declared processing preparation and its process-local readiness."""

from __future__ import annotations

import importlib
import multiprocessing
from abc import ABC, abstractmethod
from collections.abc import Callable, Hashable, Iterable, Iterator
from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass
from threading import Lock
from typing import ClassVar

from openhcs.core.autoregister_preparation import AutoRegisterRegistryPreparation
from openhcs.core.callable_contract import (
    CallableMetadataReader,
    CallableProjection,
    CompilerPreparedAutoRegisterFamily,
)
from openhcs.core.function_contract_metadata import FunctionContractAttribute


class PreparationOperation(ABC):
    """Share successful completion while retaining each obligation's identity."""

    _completed: ClassVar[set[Hashable]] = set()
    _lock: ClassVar[Lock] = Lock()

    @property
    @abstractmethod
    def identity(self) -> Hashable:
        """Return the process-local obligation, independent of runtime adapters."""

    @abstractmethod
    def execute(self) -> None:
        """Perform this operation in the current process."""

    def cache_operations(self) -> tuple[PreparationOperation, ...]:
        """Project cache work without claiming parent readiness."""
        return (self,)

    def can_prepare_in_child(self) -> bool:
        """Opt out unless this operation declares persistent child-safe work."""
        return False

    def prepare(self) -> None:
        """Skip completed work and leave failed operations eligible for retry."""
        identity = self.identity
        with self._lock:
            if identity in self._completed:
                return
        self.execute()
        with self._lock:
            self._completed.add(identity)

    @classmethod
    def reset(cls) -> None:
        """Clear core readiness, preserving independently owned kernel caches."""
        with cls._lock:
            cls._completed.clear()
        AutoRegisterRegistryPreparation.cached_module_registry_families.cache_clear()


@dataclass(frozen=True, slots=True)
class RegistryFamilyPreparation(PreparationOperation):
    """Execute a family's declared warmup and project its admitted child work."""

    family: type[CompilerPreparedAutoRegisterFamily]

    @property
    def identity(self) -> Hashable:
        return ("registry-family", id(self.family.__registry__))

    def execute(self) -> None:
        self.family.prepare_registered_family()

    def can_prepare_in_child(self) -> bool:
        return self.family.can_prepare_in_child()


@dataclass(frozen=True, slots=True)
class ModuleRegistryPreparation(PreparationOperation):
    """Derive the same registry owners for parent preparation and child caches."""

    module_name: str

    @property
    def identity(self) -> Hashable:
        return ("module-registry", self.module_name)

    def execute(self) -> None:
        AutoRegisterRegistryPreparation.prepare_module_registered_families(
            (importlib.import_module(self.module_name),)
        )

    def cache_operations(self) -> tuple[PreparationOperation, ...]:
        return tuple(
            RegistryFamilyPreparation(family)
            for family in AutoRegisterRegistryPreparation.module_registry_owners(
                (importlib.import_module(self.module_name),),
                compiler_prepared_only=True,
            )
        )


@dataclass(frozen=True, slots=True)
class DeclaredHookPreparation(PreparationOperation):
    """Own hook execution once; contextual leaves supply only identity policy."""

    hook: Callable[..., object]

    def execute(self) -> None:
        self.hook()


@dataclass(frozen=True, slots=True)
class ModuleHookPreparation(DeclaredHookPreparation):
    module_name: str

    @property
    def identity(self) -> Hashable:
        return ("module", self.module_name, id(self.hook))


@dataclass(frozen=True, slots=True)
class CallableHookPreparation(DeclaredHookPreparation):
    module_name: str | None
    function_name: str

    @property
    def identity(self) -> Hashable:
        module_label = "<unknown>" if self.module_name is None else self.module_name
        return (
            "callable",
            f"{module_label}.{self.function_name}",
            (str(self.hook.__module__), str(self.hook.__qualname__)),
        )


@dataclass(frozen=True, slots=True)
class CallablePreparation:
    """Project declared operations lazily in their original effect order."""

    projection: CallableProjection

    @classmethod
    def from_callable(cls, func: Callable[..., object]) -> CallablePreparation:
        return cls(CallableProjection.from_callable(func))

    def operations(self) -> Iterator[PreparationOperation]:
        """Read later hook declarations only after preceding operations finish."""
        module_name = self.projection.module_name
        if module_name is not None:
            yield ModuleRegistryPreparation(module_name)
            module = importlib.import_module(module_name)
            hook = CallableMetadataReader(
                vars(module), f"Module {module_name}"
            ).optional_callable(FunctionContractAttribute.processing_prepare)
            if hook is not None:
                yield ModuleHookPreparation(hook, module_name)
        hook = CallableMetadataReader(
            self.projection.namespace, self.projection.name
        ).optional_callable(FunctionContractAttribute.processing_prepare)
        if hook is not None:
            yield CallableHookPreparation(hook, module_name, self.projection.name)

    def prepare(self) -> None:
        for operation in self.operations():
            operation.prepare()

    def cache_sources(self) -> tuple[PreparationOperation, ...]:
        module_name = self.projection.module_name
        if module_name is None:
            return ()
        return (ModuleRegistryPreparation(module_name),)


@dataclass(frozen=True, slots=True)
class PreparationCacheBatch:
    """Schedule derived cache operations without interpreting backend families."""

    preparations: tuple[PreparationOperation, ...]

    @classmethod
    def from_callables(
        cls, callables: Iterable[Callable[..., object]]
    ) -> PreparationCacheBatch:
        sources = {
            operation.identity: operation
            for func in callables
            for operation in CallablePreparation.from_callable(func).cache_sources()
        }
        return cls(tuple(sources.values()))

    def populate_child_caches(self) -> None:
        if "fork" not in multiprocessing.get_all_start_methods():
            return
        operations = {
            operation.identity: operation
            for preparation in self.preparations
            for operation in preparation.cache_operations()
        }
        children = tuple(
            operation
            for operation in operations.values()
            if operation.can_prepare_in_child()
        )
        if len(children) < 2:
            return
        with ProcessPoolExecutor(
            max_workers=min(4, len(children)),
            mp_context=multiprocessing.get_context("fork"),
        ) as executor:
            futures = tuple(
                executor.submit(operation.execute) for operation in children
            )
            for future in futures:
                future.result()
