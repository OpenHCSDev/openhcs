"""Backend providers and backend selection for OpenHCS processing kernels.

Providers form one nominal family: each provider is a class, and the class owns
how an explicit request for it resolves to an implementation. The string choice
list that function signatures, forms and MCP schemas expose is derived from the
family's registry.
"""

from __future__ import annotations

import re
from abc import ABC, abstractmethod
from collections.abc import Hashable
from dataclasses import dataclass
from enum import Enum
from functools import lru_cache
from typing import Annotated, ClassVar, TypeAlias, TypeVar, cast

from metaclass_registry import AutoRegisterMeta

from openhcs.constants.constants import MemoryType
from openhcs.core.callable_contract import CallableContract
from openhcs.core.processing_preparation import PersistentNumbaKernelPreparation
from openhcs.core.runtime_object_labels import DenseArrayObjectLabelStorageStrategy

_BACKEND_KEY_SEPARATOR = ":"
_SELECTION_SUFFIXES = ("BackendProvider", "BackendSelection")
BackendProviderSelectionIdentity: TypeAlias = tuple[tuple[str, Hashable], ...]

BackendStrategyT = TypeVar(
    "BackendStrategyT",
    bound="CellProfilerBackendStrategyMixin",
)


def _selection_name(name: str, cls: type) -> str | None:
    """Derive a selection's name from its class name; family roots have none."""
    if ABC in cls.__bases__:
        return None
    for suffix in _SELECTION_SUFFIXES:
        if name.endswith(suffix):
            name = name[: -len(suffix)]
            break
    return re.sub(r"(?<!^)(?=[A-Z])", "_", name).lower()


@dataclass(frozen=True, slots=True)
class CellProfilerBackendRegistrySnapshot:
    """Immutable registry view used as the backend-selection cache key."""

    strategy_family: type["CellProfilerBackendStrategyMixin"]
    memory_type: MemoryType
    registry_keys: tuple[str, ...]

    @classmethod
    def for_family(
        cls,
        strategy_family: type["CellProfilerBackendStrategyMixin"],
        memory_type: MemoryType,
    ) -> "CellProfilerBackendRegistrySnapshot":
        registry = strategy_family.__registry__
        return cls(strategy_family, memory_type, tuple(sorted(registry)))

    @property
    def registry(self) -> dict[str, type[BackendStrategyT]]:
        return cast(
            dict[str, type[BackendStrategyT]], self.strategy_family.__registry__
        )

    def available_backend_providers(self) -> tuple[type["BackendProvider"], ...]:
        return self.strategy_family.available_backend_providers(self.memory_type)


class CellProfilerBackendSelection(ABC, metaclass=AutoRegisterMeta):
    """How a backend family chooses its implementation for one memory type.

    Members are classes and are used as values: the default selection, or one
    explicit provider.
    """

    __registry__: ClassVar[dict[str, type["CellProfilerBackendSelection"]]] = {}
    __registry_key__ = "selection_name"
    __key_extractor__ = staticmethod(_selection_name)
    __skip_if_no_key__ = True
    selection_name: ClassVar[str | None] = None

    @classmethod
    @abstractmethod
    def backend_class(
        cls,
        snapshot: CellProfilerBackendRegistrySnapshot,
    ) -> type[BackendStrategyT]:
        """Return the backend implementation this selection resolves to."""

    @classmethod
    @abstractmethod
    def provider_or(
        cls,
        default_provider: type["BackendProvider"],
    ) -> type["BackendProvider"]:
        """Return the explicit provider or a caller-owned contextual default."""

    @classmethod
    def semantic_identity(cls) -> BackendProviderSelectionIdentity:
        """Return a stable identity for equivalent backend-selection semantics."""
        return (("selection", cls.selection_name),)

    @classmethod
    def from_input(
        cls,
        backend_provider: "BackendProviderSelectionInput" = None,
    ) -> type["CellProfilerBackendSelection"]:
        """Resolve a function argument: a choice, a selection class, or None."""
        if backend_provider is None:
            return DefaultBackendSelection
        if isinstance(backend_provider, CellProfilerBackendProvider):
            return backend_provider.provider
        if isinstance(backend_provider, type) and issubclass(
            backend_provider, CellProfilerBackendSelection
        ):
            return backend_provider
        raise TypeError(
            "Backend provider must be a CellProfilerBackendProvider choice, a "
            f"backend selection class, or None; got {backend_provider!r}."
        )


class DefaultBackendSelection(CellProfilerBackendSelection):
    """Select the single declared default backend for the requested memory type."""

    @classmethod
    def backend_class(
        cls,
        snapshot: CellProfilerBackendRegistrySnapshot,
    ) -> type[BackendStrategyT]:
        matches = [
            strategy_cls
            for strategy_cls in snapshot.registry.values()
            if strategy_cls.memory_type is snapshot.memory_type
            and bool(strategy_cls.is_default_backend)
        ]
        if len(matches) == 1:
            return matches[0]
        if not matches:
            raise NotImplementedError(
                f"No default CellProfiler {snapshot.strategy_family.__name__} backend "
                f"is "
                f"registered for memory type {snapshot.memory_type.value!r}. "
                f"Registered providers for this memory type: "
                f"{snapshot.available_backend_providers()!r}."
            )
        raise RuntimeError(
            f"Multiple default CellProfiler {snapshot.strategy_family.__name__} "
            f"backends are "
            f"registered for memory type {snapshot.memory_type.value!r}: "
            f"{tuple(strategy.__name__ for strategy in matches)!r}."
        )

    @classmethod
    def provider_or(
        cls,
        default_provider: type["BackendProvider"],
    ) -> type["BackendProvider"]:
        return default_provider


class BackendProvider(CellProfilerBackendSelection, ABC):
    """One implementation provider; selecting it never falls back to another."""

    requires_compiler_prewarm: ClassVar[bool] = False

    @classmethod
    def backend_key(cls, memory_type: MemoryType) -> str:
        """Return the registry key of this provider's backend for a memory type."""
        if not isinstance(memory_type, MemoryType):
            raise TypeError("Backend memory type must be a MemoryType enum value")
        return memory_type.value + _BACKEND_KEY_SEPARATOR + cls.selection_name

    @classmethod
    def backend_class(
        cls,
        snapshot: CellProfilerBackendRegistrySnapshot,
    ) -> type[BackendStrategyT]:
        key = cls.backend_key(snapshot.memory_type)
        try:
            return snapshot.registry[key]
        except KeyError as exc:
            raise NotImplementedError(
                f"No CellProfiler {snapshot.strategy_family.__name__} backend is "
                f"registered for "
                f"memory type {snapshot.memory_type.value!r} and provider "
                f"{cls.selection_name!r}. Registered providers for this memory "
                f"type: {snapshot.available_backend_providers()!r}."
            ) from exc

    @classmethod
    def provider_or(
        cls,
        default_provider: type["BackendProvider"],
    ) -> type["BackendProvider"]:
        del default_provider
        return cls


class NativeBackendProvider(BackendProvider):
    """Python/NumPy implementation following the native CellProfiler code path."""


class NumbaBackendProvider(BackendProvider):
    """Numba kernels specialized at compile time."""

    requires_compiler_prewarm = True


class CppBackendProvider(BackendProvider):
    """Compiled C++ extension kernels."""


class CentrosomeBackendProvider(BackendProvider):
    """Algorithms absorbed from CellProfiler's centrosome library."""


class OpencvBackendProvider(BackendProvider):
    """OpenCV kernels."""


class LegacyFastBackendProvider(BackendProvider):
    """Fast approximations of CellProfiler 3 behaviour."""


class CucimBackendProvider(BackendProvider):
    """cuCIM GPU kernels."""


class PyclesperantoBackendProvider(BackendProvider):
    """pyclesperanto GPU kernels."""


class SkimageBackendProvider(BackendProvider):
    """scikit-image implementations."""


class _BackendProviderChoice(str):
    """Choice-list member that names one provider class."""

    @property
    def provider(self) -> type[BackendProvider]:
        return cast(
            type[BackendProvider],
            CellProfilerBackendSelection.__registry__[self.value],
        )


CellProfilerBackendProvider = Enum(
    "CellProfilerBackendProvider",
    {
        name.upper(): name
        for name, selection in CellProfilerBackendSelection.__registry__.items()
        if issubclass(selection, BackendProvider)
    },
    type=_BackendProviderChoice,
    module=__name__,
    qualname="CellProfilerBackendProvider",
)
"""Provider choice list for function signatures, derived from the provider family."""

BackendProviderInput: TypeAlias = Annotated[
    CellProfilerBackendProvider | None,
    "Processing implementation selection for the parameter's named "
    "CellProfiler operation; leave the default to use its registered implementation.",
]
BackendProviderSelectionInput: TypeAlias = (
    CellProfilerBackendProvider | type[CellProfilerBackendSelection] | None
)
DEFAULT_CELLPROFILER_BACKEND_SELECTION: BackendProviderInput = None


def _backend_key(name: str, cls: type) -> str | None:
    """Derive a backend's registry key from its declared memory type and provider."""
    del name
    memory_type = cls.memory_type
    if memory_type is None:
        return None
    key = cls.backend_provider.backend_key(memory_type)
    registered = dict.get(cls.__registry__, key)
    if registered is not None and (
        registered.__module__,
        registered.__qualname__,
    ) != (cls.__module__, cls.__qualname__):
        raise TypeError(
            f"{cls.__module__}.{cls.__qualname__} and "
            f"{registered.__module__}.{registered.__qualname__} both declare "
            f"memory type {memory_type.value!r} and provider "
            f"{cls.backend_provider.selection_name!r}."
        )
    return key


class CellProfilerBackendStrategyMixin(PersistentNumbaKernelPreparation):
    """Backend strategies keyed by their declared memory type and provider.

    A family root combines this mixin with ``metaclass=AutoRegisterMeta``. A
    backend declares ``memory_type`` and ``backend_provider``; its registry key
    is derived from them.
    """

    __registry_key__ = "backend_key"
    __key_extractor__ = staticmethod(_backend_key)
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type["CellProfilerBackendStrategyMixin"]]]
    backend_key: ClassVar[str | None] = None
    memory_type: ClassVar[MemoryType | None] = None
    backend_provider: ClassVar[type[BackendProvider]]
    is_default_backend: ClassVar[bool] = False

    def __init_subclass__(cls, **kwargs: object) -> None:
        super().__init_subclass__(**kwargs)
        # The key is always derived from this class's own declarations.
        cls.backend_key = None

    @classmethod
    def requires_persistent_kernel_cache(cls) -> bool:
        """Require cache preparation only for declared compiler-backed providers."""
        if cls is CellProfilerBackendStrategyMixin:
            return False
        return any(
            strategy.requires_explicit_prepare_backend()
            for strategy in cls.__registry__.values()
        )

    @classmethod
    def prepare_registered_family(cls) -> None:
        """Prepare every registered backend implementation for compiler warmup."""
        if cls is CellProfilerBackendStrategyMixin:
            return
        DenseArrayObjectLabelStorageStrategy.prepare_coordinates()
        snapshot = CellProfilerBackendRegistrySnapshot.for_family(
            cls,
            MemoryType.NUMPY,
        )
        _prepare_cellprofiler_backend_family_cached(snapshot)

    def prepare_backend(self) -> None:
        """Prepare this concrete backend implementation."""
        return

    @classmethod
    def requires_explicit_prepare_backend(cls) -> bool:
        """Return whether this provider must prewarm runtime-specialized code."""
        return cls.backend_provider.requires_compiler_prewarm

    @classmethod
    def for_memory_type(
        cls: type[BackendStrategyT],
        memory_type: MemoryType = MemoryType.NUMPY,
        *,
        backend_provider: BackendProviderSelectionInput = (
            DEFAULT_CELLPROFILER_BACKEND_SELECTION
        ),
    ) -> BackendStrategyT:
        """Instantiate the exact backend for ``memory_type`` and provider.

        The default selection resolves the single default provider for the
        memory type. Explicit providers never fall back to another backend.
        """
        return cls._resolve_backend_class(memory_type, backend_provider)()

    @classmethod
    def for_callable(
        cls: type[BackendStrategyT],
        func: object,
        *,
        backend_provider: BackendProviderSelectionInput = (
            DEFAULT_CELLPROFILER_BACKEND_SELECTION
        ),
    ) -> BackendStrategyT:
        """Instantiate a backend using a function's OpenHCS memory contract."""
        contract = CallableContract.from_callable(func)
        memory_type = (
            contract.input_memory_type
            or contract.output_memory_type
            or MemoryType.NUMPY.value
        )
        return cls.for_memory_type(
            MemoryType(memory_type),
            backend_provider=backend_provider,
        )

    @classmethod
    def available_backend_providers(
        cls,
        memory_type: MemoryType | None = None,
    ) -> tuple[type[BackendProvider], ...]:
        """Return registered providers, optionally filtered by memory type."""
        if memory_type is not None and not isinstance(memory_type, MemoryType):
            raise TypeError("Backend memory type must be a MemoryType enum value")
        providers = {
            strategy_cls.backend_provider
            for strategy_cls in cls.__registry__.values()
            if memory_type is None or strategy_cls.memory_type is memory_type
        }
        return tuple(sorted(providers, key=lambda provider: provider.selection_name))

    @classmethod
    def _resolve_backend_class(
        cls: type[BackendStrategyT],
        memory_type: MemoryType,
        backend_provider: BackendProviderSelectionInput,
    ) -> type[BackendStrategyT]:
        if not isinstance(memory_type, MemoryType):
            raise TypeError("Backend memory type must be a MemoryType enum value")
        snapshot = CellProfilerBackendRegistrySnapshot.for_family(cls, memory_type)
        selection = CellProfilerBackendSelection.from_input(backend_provider)
        return _resolve_backend_class_cached(snapshot, selection)


@lru_cache(maxsize=None)
def _resolve_backend_class_cached(
    snapshot: CellProfilerBackendRegistrySnapshot,
    selection: type[CellProfilerBackendSelection],
) -> type[BackendStrategyT]:
    return selection.backend_class(snapshot)


@lru_cache(maxsize=None)
def _prepare_cellprofiler_backend_family_cached(
    snapshot: CellProfilerBackendRegistrySnapshot,
) -> None:
    for strategy_cls in snapshot.registry.values():
        if (
            strategy_cls.requires_explicit_prepare_backend()
            and strategy_cls.prepare_backend
            is CellProfilerBackendStrategyMixin.prepare_backend
        ):
            raise RuntimeError(
                f"{strategy_cls.__module__}.{strategy_cls.__name__} uses the "
                "Numba backend provider but does not implement "
                "prepare_backend(). Numba specializations must be compiled "
                "during OpenHCS compiler preparation, not first timed execution."
            )
        strategy_cls().prepare_backend()


__all__ = [
    "DEFAULT_CELLPROFILER_BACKEND_SELECTION",
    "BackendProvider",
    "BackendProviderInput",
    "BackendProviderSelectionInput",
    "BackendProviderSelectionIdentity",
    "CellProfilerBackendProvider",
    "CellProfilerBackendSelection",
    "CellProfilerBackendStrategyMixin",
    "CentrosomeBackendProvider",
    "CppBackendProvider",
    "CucimBackendProvider",
    "DefaultBackendSelection",
    "LegacyFastBackendProvider",
    "NativeBackendProvider",
    "NumbaBackendProvider",
    "OpencvBackendProvider",
    "PyclesperantoBackendProvider",
    "SkimageBackendProvider",
]
