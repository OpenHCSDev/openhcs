"""Declared persistent kernel work shared by registry and callable preparation."""

from __future__ import annotations

from collections.abc import Hashable
from pathlib import Path
from typing import ClassVar

from openhcs.core.callable_contract import CompilerPreparedAutoRegisterFamily
from openhcs.core.processing_preparation import PreparationOperation
from openhcs.utils.environment import OpenHCSProcessEnvironment


class CellProfilerKernelCachePreparationMixin:
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


class CellProfilerCallableKernelPreparation(
    CellProfilerKernelCachePreparationMixin,
    PreparationOperation,
    CompilerPreparedAutoRegisterFamily,
):
    """Own pure kernel work; concrete declarations own independent registries.

    This abstract protocol has no registry. AutoRegisterMeta creates one on
    each direct concrete declaration, deriving child work from the existing
    module registry discovery without inspecting callable or module hooks.
    Parent registry and callable preparation share successful readiness.
    """

    __registry_key__ = "__name__"
    __registry__: ClassVar[dict[str, type[CellProfilerCallableKernelPreparation]]]

    @property
    def identity(self) -> Hashable:
        return type(self)

    @classmethod
    def prepare_registered_family(cls) -> None:
        for declaration in cls.__registry__.values():
            declaration().prepare()
