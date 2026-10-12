"""Declared processing preparation and its process-local readiness."""

from __future__ import annotations

import enum
import importlib
import inspect
import multiprocessing
import os
import signal
import traceback
from abc import ABC, abstractmethod
from collections.abc import Callable, Hashable, Iterable, Iterator, Mapping
from concurrent.futures import CancelledError
from contextlib import ExitStack
from dataclasses import dataclass, field
from itertools import chain, islice, product
from multiprocessing.connection import Connection, wait
from multiprocessing.process import BaseProcess
from threading import Lock
from typing import ClassVar, Literal, get_args, get_origin, get_type_hints

from openhcs.core.autoregister_preparation import AutoRegisterRegistryPreparation
from openhcs.core.callable_contract import (
    DeclaredCallable,
    CallableProjection,
    CompilerPreparedAutoRegisterFamily,
)
from openhcs.core.function_contract_metadata import FunctionContractAttribute
from openhcs.utils.environment import OpenHCSProcessEnvironment


class PersistentNumbaKernelPreparation(CompilerPreparedAutoRegisterFamily):
    """Isolate declared persistent CPU kernel cache preparation."""

    @classmethod
    def requires_persistent_kernel_cache(cls) -> bool:
        """Declared pure kernel operations require a persistent Numba cache."""
        return True

    @classmethod
    def can_prepare_in_child(cls) -> bool:
        """A forked child compiles for the server wherever Numba persists.

        Numba always has a cache for a ``cache=True`` kernel: ``NUMBA_CACHE_DIR``,
        else ``__pycache__`` beside the source, else its per-user directory. It
        refuses to define the kernel otherwise.
        """
        return (
            OpenHCSProcessEnvironment.cpu_only_mode()
            and cls.requires_persistent_kernel_cache()
        )


class PreparationOperation(ABC):
    """Share successful completion while retaining each obligation's identity."""

    _completed: ClassVar[set[Hashable]] = set()
    # Why an operation that ran is not completed, until a later run completes it.
    _failure_causes: ClassVar[dict[Hashable, str]] = {}
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
        """Skip completed work; a run that raises is recorded with its cause.

        A failed operation is not completed, so the next ``prepare`` runs it
        again. Nothing here runs it again on its own.
        """
        identity = self.identity
        with self._lock:
            if identity in self._completed:
                return
        try:
            self.execute()
        except Exception as error:
            with self._lock:
                self._failure_causes[identity] = f"{type(error).__name__}: {error}"
            raise
        with self._lock:
            self._completed.add(identity)
            self._failure_causes.pop(identity, None)

    def failure_cause(self) -> str | None:
        """What the last run raised, when this operation ran and did not complete."""
        with self._lock:
            return self._failure_causes.get(self.identity)

    def forget_failure(self) -> None:
        """Drop the record of a failed run: its owner reports the failure itself."""
        with self._lock:
            self._failure_causes.pop(self.identity, None)

    @classmethod
    def reset(cls) -> None:
        """Clear core readiness, preserving independently owned kernel caches."""
        with cls._lock:
            cls._completed.clear()
            cls._failure_causes.clear()
        CallablePreparation._serves_prepared_callables = False
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

    @property
    def call(self) -> Hashable:
        """The call this operation makes: the same call is made once per batch."""
        return self.hook

    def cache_operations(self) -> tuple[PreparationOperation, ...]:
        """A hook bound to a declared operation is that operation's cache work."""
        operation = getattr(self.hook, "__self__", None)
        if isinstance(operation, PreparationOperation):
            return operation.cache_operations()
        return (self,)

    def can_prepare_in_child(self) -> bool:
        """A hook's kernels reach the server through the persistent Numba cache."""
        return PersistentNumbaKernelPreparation.can_prepare_in_child()


@dataclass(frozen=True, slots=True)
class ModuleHookPreparation(DeclaredHookPreparation):
    module_name: str

    @property
    def identity(self) -> Hashable:
        return ("module", self.module_name, id(self.hook))


HookArguments = tuple[tuple[str, Hashable], ...]


class UnpreparedValueError(ValueError):
    """A step selects a value its function's preparation did not acquire."""


class AcquisitionFailedError(RuntimeError):
    """A value a pipeline selects could not be acquired when it was tried again."""


@dataclass(frozen=True, slots=True)
class UnacquiredValue:
    """One declared value of a published function whose acquisition failed."""

    arguments: str
    cause: str

    def describe(self) -> str:
        return f"{self.arguments} ({self.cause})"


def declared_hook_arguments(hook: Callable[..., object]) -> tuple[HookArguments, ...]:
    """Every argument combination a hook declares it can be called with.

    A hook names parameters of its function. Each must be annotated with a
    finite type: an ``Enum`` (every member) or a ``Literal`` (its values, which
    is how a hook declares fewer values than its function accepts). A hook
    without parameters declares the single empty combination.
    """
    hints = get_type_hints(hook)
    names = tuple(inspect.signature(hook).parameters)
    values_by_name: list[tuple[Hashable, ...]] = []
    for name in names:
        annotation = hints.get(name)
        if get_origin(annotation) is Literal:
            values_by_name.append(get_args(annotation))
        elif isinstance(annotation, type) and issubclass(annotation, enum.Enum):
            values_by_name.append(tuple(annotation))
        else:
            raise TypeError(
                f"Preparation hook {hook.__qualname__!r} parameter {name!r} must be "
                f"annotated with an Enum or a Literal, got {annotation!r}."
            )
    return tuple(tuple(zip(names, values)) for values in product(*values_by_name))


def selected_hook_arguments(
    hook: Callable[..., object],
    func: Callable[..., object],
    kwargs: Mapping[str, object],
) -> HookArguments:
    """What a call of ``func`` with ``kwargs`` selects for the hook's parameters.

    ``func`` is read for a default only when the call does not pass the value.
    """
    selected: list[tuple[str, Hashable]] = []
    for name in inspect.signature(hook).parameters:
        if name in kwargs:
            selected.append((name, kwargs[name]))
            continue
        parameters = inspect.signature(func).parameters
        if name not in parameters or parameters[name].default is inspect.Parameter.empty:
            raise TypeError(
                f"Preparation hook {hook.__qualname__!r} names {name!r}, which is not "
                f"a parameter with a default of {func!r}."
            )
        selected.append((name, parameters[name].default))
    return tuple(selected)


@dataclass(frozen=True, slots=True)
class CallableHookPreparation(DeclaredHookPreparation):
    """One call of a function's hook: the function, the hook and its arguments."""

    module_name: str | None
    function_name: str
    arguments: HookArguments = ()

    lifetime: ClassVar[str]

    @property
    def identity(self) -> Hashable:
        module_label = "<unknown>" if self.module_name is None else self.module_name
        return (
            self.lifetime,
            f"{module_label}.{self.function_name}",
            (str(self.hook.__module__), str(self.hook.__qualname__)),
            self.arguments,
        )

    def execute(self) -> None:
        self.hook(**dict(self.arguments))

    @property
    def call(self) -> Hashable:
        return (self.hook, self.arguments)

    def is_completed(self) -> bool:
        with self._lock:
            return self.identity in self._completed

    def described_arguments(self) -> str:
        """The values this call is for, as a message names them."""
        return ", ".join(f"{name}={value!r}" for name, value in self.arguments)


class AcquireHookPreparation(CallableHookPreparation):
    """Put a resource on this machine (kernel cache, weights): before readiness."""

    lifetime = "callable"


@dataclass(frozen=True, slots=True)
class LoadHookPreparation(CallableHookPreparation):
    """Load a resource into this process or onto its device: per pipeline."""

    lifetime = "load"
    device_id: int | None = None

    @property
    def identity(self) -> Hashable:
        return (*CallableHookPreparation.identity.fget(self), self.device_id)

    def can_prepare_in_child(self) -> bool:
        """A load lives in the process that runs it; a child cannot do it."""
        return False


@dataclass(frozen=True, slots=True)
class CallablePreparation:
    """Project declared operations lazily in their original effect order."""

    projection: CallableProjection
    # True once this process (or the server it was forked from) prepared its
    # catalogue for serving: from then on a callable is prepared when published.
    _serves_prepared_callables: ClassVar[bool] = False

    @classmethod
    def from_callable(cls, func: Callable[..., object]) -> CallablePreparation:
        return cls(CallableProjection.from_callable(func))

    @classmethod
    def prepare_published(cls, func: Callable[..., object]) -> None:
        """Prepare a callable that is published after serving preparation.

        A serving process holds "prepared before usable" for every callable a
        pipeline can name, so a late publication prepares as part of publishing.
        Any other process (authoring, a client) prepares nothing here.
        """
        if cls._serves_prepared_callables:
            cls.prepare_for_serving(
                CallableProjection.from_callable(func).prepare_targets(),
                lambda _message: None,
            )

    def module_operations(self) -> Iterator[PreparationOperation]:
        """Read later hook declarations only after preceding operations finish."""
        module_name = self.projection.module_name
        if module_name is not None:
            yield ModuleRegistryPreparation(module_name)
            module = importlib.import_module(module_name)
            hook = DeclaredCallable().read(
                vars(module).get(FunctionContractAttribute.processing_prepare),
                owner=f"Module {module_name}.{FunctionContractAttribute.processing_prepare}",
            )
            if hook is not None:
                yield ModuleHookPreparation(hook, module_name)

    def operations(self) -> Iterator[PreparationOperation]:
        """The module's operations, then every acquisition the callable declares."""
        yield from self.module_operations()
        yield from self.acquisitions()

    def _hook(self, attribute: str) -> Callable[..., object] | None:
        return DeclaredCallable().read(
            self.projection.namespace.get(attribute),
            owner=f"{self.projection.name!r}.{attribute}",
        )

    def acquisitions(self) -> tuple[AcquireHookPreparation, ...]:
        """One acquisition per argument combination the acquire hook declares."""
        hook = self._hook(FunctionContractAttribute.processing_prepare)
        if hook is None:
            return ()
        return tuple(
            AcquireHookPreparation(
                hook, self.projection.module_name, self.projection.name, arguments
            )
            for arguments in declared_hook_arguments(hook)
        )

    def selected_load(
        self, kwargs: Mapping[str, object], device_id: int | None
    ) -> LoadHookPreparation | None:
        """The load a step with these keyword arguments needs in its workers."""
        hook = self._hook(FunctionContractAttribute.processing_load)
        if hook is None:
            return None
        return LoadHookPreparation(
            hook,
            self.projection.module_name,
            self.projection.name,
            selected_hook_arguments(hook, self.projection.func, kwargs),
            device_id,
        )

    def selected_acquisition(
        self, kwargs: Mapping[str, object]
    ) -> AcquireHookPreparation | None:
        """The acquisition a step with these keyword arguments selects."""
        hook = self._hook(FunctionContractAttribute.processing_prepare)
        if hook is None:
            return None
        return AcquireHookPreparation(
            hook,
            self.projection.module_name,
            self.projection.name,
            selected_hook_arguments(hook, self.projection.func, kwargs),
        )

    def prepare_selected(self, kwargs: Mapping[str, object]) -> None:
        """Make what a step selects available to a compile, acquiring nothing late.

        A serving process tried every declared value before it reported ready.
        A selection it never tried (the hook does not declare it) is refused,
        naming what was acquired. A selection whose acquisition failed is let
        through: "prepare this pipeline" tries it again before any worker
        loads. A process that does not serve has no readiness: it acquires the
        selected value here, and nothing else.
        """
        selection = self.selected_acquisition(kwargs)
        if selection is None or selection.is_completed():
            return
        if not self._serves_prepared_callables:
            selection.prepare()
            return
        if selection.failure_cause() is not None:
            return
        acquired = [
            operation.described_arguments()
            for operation in self.acquisitions()
            if operation.is_completed()
        ]
        raise UnpreparedValueError(
            f"{self.projection.name!r} was not prepared for "
            + selection.described_arguments()
            + ". Prepared before this server reported ready: "
            + ("; ".join(acquired) or "nothing")
            + "."
        )

    def acquire_selected_again(self, kwargs: Mapping[str, object]) -> bool:
        """Try again the acquisition a step selects, if it failed; say whether it ran.

        A second failure names the function, the value and the cause, and
        stays recorded for the next attempt.
        """
        selection = self.selected_acquisition(kwargs)
        if selection is None or selection.failure_cause() is None:
            return False
        try:
            selection.prepare()
        except CancelledError:
            raise
        except Exception as error:
            raise AcquisitionFailedError(
                f"{self.projection.name!r} could not be acquired for "
                f"{selection.described_arguments()}: {type(error).__name__}: {error}"
            ) from error
        return True

    def unacquired(self) -> tuple[UnacquiredValue, ...]:
        """The declared values whose acquisition ran and failed, with the cause."""
        return tuple(
            UnacquiredValue(operation.described_arguments(), cause)
            for operation in self.acquisitions()
            if (cause := operation.failure_cause()) is not None
        )

    def acquire_unacquired_again(self) -> None:
        """Try again every declared value whose acquisition failed.

        Each value that fails again stays recorded with its new cause.
        """
        self._attempt(
            operation
            for operation in self.acquisitions()
            if operation.failure_cause() is not None
        )

    @staticmethod
    def _attempt(operations: Iterable[PreparationOperation]) -> list[Exception]:
        """Run each operation; return what the ones that failed raised."""
        errors: list[Exception] = []
        for operation in operations:
            try:
                operation.prepare()
            except CancelledError:
                raise
            except Exception as error:
                errors.append(error)
        return errors

    def prepare(self) -> None:
        """Prepare everything the callable declares: what a serving process does.

        Every declared value of the acquire hook that has no outcome yet is
        tried. A value recorded as failed is not tried here again: that takes
        an explicit retry, or preparing a pipeline that selects it. When no
        value could be acquired the callable is not prepared: the first cause
        is raised and is the callable's failure, so no value keeps a record.
        When some were acquired the callable is usable for those, and each
        value that failed stays recorded with its cause.
        """
        for operation in self.module_operations():
            operation.prepare()
        acquisitions = self.acquisitions()
        errors = self._attempt(
            operation for operation in acquisitions if operation.failure_cause() is None
        )
        if errors and not any(operation.is_completed() for operation in acquisitions):
            for operation in acquisitions:
                operation.forget_failure()
            raise errors[0]

    def prepare_for_call(self, kwargs: Mapping[str, object]) -> None:
        """Prepare for one compiled call: the module, then what the call selects."""
        for operation in self.module_operations():
            operation.prepare()
        self.prepare_selected(kwargs)

    @classmethod
    def prepare_for_serving(
        cls,
        callables: Iterable[Callable[..., object]],
        status_callback: Callable[[str], None],
    ) -> None:
        """Prepare every callable, then complete the registries their modules use.

        Only this step completes lazy registries, so none is first discovered
        during compilation or execution. Preparing one callable does not.
        """
        preparations = tuple(cls.from_callable(func) for func in callables)
        CallablePreparation._serves_prepared_callables = True
        for preparation in preparations:
            preparation.prepare()
            status_callback(
                f"Prepared callable {preparation.projection.module_name}.{preparation.projection.name}"
            )
        status_callback("Completing the registries prepared callables use")
        AutoRegisterRegistryPreparation.discover_module_registries(
            importlib.import_module(module_name)
            for module_name in dict.fromkeys(
                preparation.projection.module_name for preparation in preparations
            )
            if module_name is not None
        )

    def cache_sources(self) -> tuple[PreparationOperation, ...]:
        module_name = self.projection.module_name
        if module_name is None:
            return ()
        return (ModuleRegistryPreparation(module_name),)

    def hooks(self) -> tuple[DeclaredHookPreparation, ...]:
        """The declared hooks, which load the kernels the registries cached."""
        return tuple(
            operation
            for operation in self.operations()
            if isinstance(operation, DeclaredHookPreparation)
        )


def _execute_cache_preparation(
    operations: tuple[PreparationOperation, ...], result_connection: Connection
) -> None:
    """Report completion while allowing the parent to terminate its exact worker."""

    signal.signal(signal.SIGTERM, signal.SIG_DFL)
    try:
        for operation in operations:
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
    def start(
        cls, context, operations: tuple[PreparationOperation, ...]
    ) -> PreparationCacheWorker:
        receiver, sender = context.Pipe(duplex=False)
        process = context.Process(
            target=_execute_cache_preparation, args=(operations, sender)
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


def _schedulable_cpu_count() -> int:
    """CPUs this process may run on.

    Linux exposes the scheduler's affinity set. macOS has no affinity API:
    every online CPU is schedulable there.
    """
    try:
        return len(os.sched_getaffinity(0))
    except AttributeError:
        return os.cpu_count() or 1


@dataclass(frozen=True, slots=True)
class PreparationCacheBatch:
    """Schedule derived cache operations without interpreting backend families.

    Stages run in order and each finishes before the next starts, so a later
    stage loads from the persistent cache what an earlier one compiled.
    """

    preparations: tuple[PreparationOperation, ...]
    hooks: tuple[PreparationOperation, ...] = ()

    @classmethod
    def from_callables(
        cls, callables: Iterable[Callable[..., object]]
    ) -> PreparationCacheBatch:
        """Registry kernels first, then the hooks that call them."""
        preparations = tuple(
            CallablePreparation.from_callable(func) for func in callables
        )
        sources = {
            operation.identity: operation
            for preparation in preparations
            for operation in preparation.cache_sources()
        }
        hooks = {
            operation.call: operation
            for preparation in preparations
            for operation in preparation.hooks()
        }
        return cls(tuple(sources.values()), tuple(hooks.values()))

    def populate_child_caches(
        self,
        *,
        max_workers: int = 1,
        status_callback: Callable[[str], None] | None = None,
    ) -> None:
        """Isolate declared cache work, never parent process-local readiness."""
        if max_workers < 1:
            raise ValueError("Preparation worker budget must be positive.")
        if "fork" not in multiprocessing.get_all_start_methods():
            return
        worker_capacity = min(max_workers, _schedulable_cpu_count())
        context = multiprocessing.get_context("fork")
        registry_operations = {
            operation.identity: operation
            for preparation in self.preparations
            for operation in preparation.cache_operations()
        }
        hook_operations = dict.fromkeys(
            operation
            for hook in self.hooks
            for operation in hook.cache_operations()
            if operation.identity not in registry_operations
        )
        registries, hooks = (
            tuple(
                operation
                for operation in operations
                if operation.can_prepare_in_child()
            )
            for operations in (registry_operations.values(), hook_operations)
        )
        # A registry operation compiles for seconds, so each gets a child. A
        # hook mostly loads what the registries cached, and a child costs about
        # a second before it does anything: hooks share one child per CPU.
        for tasks in (
            tuple((operation,) for operation in registries),
            tuple(hooks[index::worker_capacity] for index in range(worker_capacity)),
        ):
            self._run_children(
                context, tuple(filter(None, tasks)), worker_capacity, status_callback
            )

    @staticmethod
    def _run_children(
        context,
        tasks: tuple[tuple[PreparationOperation, ...], ...],
        worker_capacity: int,
        status_callback: Callable[[str], None] | None,
    ) -> None:
        """Run each task in its own child, or all in one child on a single CPU."""
        pending = (
            iter(filter(None, (tuple(chain.from_iterable(tasks)),)))
            if worker_capacity == 1
            else iter(tasks)
        )
        with ExitStack() as resources:
            workers: list[PreparationCacheWorker] = []
            while True:
                for operations in islice(pending, worker_capacity - len(workers)):
                    worker = PreparationCacheWorker.start(context, operations)
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
