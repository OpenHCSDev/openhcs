"""Declared processing preparation and its process-local readiness."""

from __future__ import annotations

import importlib
import multiprocessing
import os
import signal
import traceback
from abc import ABC, abstractmethod
from collections.abc import Callable, Hashable, Iterable, Iterator
from contextlib import ExitStack
from dataclasses import dataclass, field
from itertools import islice
from multiprocessing.connection import Connection, wait
from multiprocessing.process import BaseProcess
from pathlib import Path
from threading import Lock
from typing import ClassVar

from openhcs.core.autoregister_preparation import AutoRegisterRegistryPreparation
from openhcs.core.callable_contract import (
    CallableMetadataReader,
    CallableProjection,
    CompilerPreparedAutoRegisterFamily,
)
from openhcs.core.function_contract_metadata import FunctionContractAttribute
from openhcs.utils.environment import OpenHCSProcessEnvironment


class PersistentNumbaKernelPreparation(CompilerPreparedAutoRegisterFamily):
    """Admit persistent Numba work only for an empty explicit CPU cache."""

    @classmethod
    def requires_persistent_kernel_cache(cls) -> bool:
        """Declared pure kernel operations require a persistent Numba cache."""
        return True

    @classmethod
    def can_prepare_in_child(cls) -> bool:
        if not OpenHCSProcessEnvironment.cpu_only_mode():
            return False
        if not cls.requires_persistent_kernel_cache():
            return False
        from numba import config as numba_config

        cache_directory = numba_config.CACHE_DIR
        return (
            bool(cache_directory)
            and next(Path(cache_directory).rglob("*.nbi"), None) is None
        )


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


class RegisteredNumbaKernelPreparation(
    PersistentNumbaKernelPreparation, PreparationOperation
):
    """Derive independent pure-kernel obligations from each declared registry.

    This abstract parent has no registry. Concrete AutoRegisterMeta declarations
    own their registries; the common parent owns identity, operation derivation
    and successful parent preparation.
    """

    __registry_key__ = "__name__"
    __registry__: ClassVar[dict[str, type[RegisteredNumbaKernelPreparation]]]

    @property
    def identity(self) -> Hashable:
        return type(self)

    @classmethod
    def cache_preparation_operations(cls) -> tuple[PreparationOperation, ...]:
        return tuple(declaration() for declaration in cls.__registry__.values())

    @classmethod
    def prepare_registered_family(cls) -> None:
        for operation in cls.cache_preparation_operations():
            operation.prepare()


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
            operation
            for family in AutoRegisterRegistryPreparation.module_registry_owners(
                (importlib.import_module(self.module_name),),
                compiler_prepared_only=True,
            )
            for operation in family.cache_preparation_operations()
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


def _execute_cache_preparation(operation, result_connection) -> None:
    """Report completion while allowing the parent to terminate its exact worker."""

    signal.signal(signal.SIGTERM, signal.SIG_DFL)
    try:
        operation.execute()
    except BaseException:
        result_connection.send(traceback.format_exc()[-4000:])
        raise
    else:
        result_connection.send(None)
    finally:
        result_connection.close()


@dataclass(slots=True)
class PreparationCacheWorker:
    """Own one cache process and its completion channel through cancellation."""

    process: BaseProcess
    result_connection: Connection
    closed: bool = field(default=False, init=False)

    @classmethod
    def start(cls, context, operation: PreparationOperation) -> PreparationCacheWorker:
        receiver, sender = context.Pipe(duplex=False)
        process = context.Process(
            target=_execute_cache_preparation, args=(operation, sender)
        )
        try:
            process.start()
        except BaseException:
            receiver.close()
            process.close()
            raise
        finally:
            sender.close()
        return cls(process, receiver)

    def wait(self) -> None:
        try:
            error = self.result_connection.recv()
        except EOFError as error:
            self.process.join()
            raise RuntimeError(
                f"Cache preparation worker exited without a result (exit code {self.process.exitcode})"
            ) from error
        self.process.join()
        if error is not None:
            raise RuntimeError(error)
        if self.process.exitcode != 0:
            raise RuntimeError(
                f"Cache preparation worker failed (exit code {self.process.exitcode})"
            )

    def close(self) -> None:
        """Release this owned worker once, including after early slot retirement."""

        if self.closed:
            return
        try:
            if self.process.is_alive():
                self.process.terminate()
                self.process.join(timeout=0.25)
            if self.process.is_alive():
                self.process.kill()
                self.process.join(timeout=1.0)
            if self.process.is_alive():
                raise TimeoutError("Cache preparation worker did not terminate")
            self.process.join()
            self.process.close()
            self.closed = True
        finally:
            self.result_connection.close()


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

    def populate_child_caches(
        self, *, max_workers: int = 1,
        status_callback: Callable[[str], None] | None = None
    ) -> None:
        """Admit optional cache parallelism, never parent process-local readiness."""
        if max_workers < 1:
            raise ValueError("Preparation worker budget must be positive.")
        if "fork" not in multiprocessing.get_all_start_methods():
            return
        if max_workers == 1:
            return
        try:
            worker_capacity = min(max_workers, len(os.sched_getaffinity(0)))
        except AttributeError:
            # Without an affinity witness there is no admitted parallel cache
            # work. The existing parent preparation still owns readiness.
            return
        if worker_capacity < 2:
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
        context = multiprocessing.get_context("fork")
        pending = iter(children)
        with ExitStack() as resources:
            workers: list[PreparationCacheWorker] = []
            while True:
                for operation in islice(pending, worker_capacity - len(workers)):
                    worker = PreparationCacheWorker.start(context, operation)
                    resources.callback(worker.close)
                    workers.append(worker)
                if not workers:
                    break
                ready = wait(tuple(worker.result_connection for worker in workers))
                for worker in tuple(workers):
                    if worker.result_connection in ready:
                        worker.wait()
                        if status_callback is not None:
                            status_callback(
                                f"Prepared kernel cache worker {worker.process.pid}"
                            )
                        worker.close()
                        workers.remove(worker)
