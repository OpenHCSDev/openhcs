"""Compiler-bound preparation for AutoRegisterMeta registries."""

from __future__ import annotations

import sys
from functools import lru_cache
from types import ModuleType
from typing import Iterable

from metaclass_registry import AutoRegisterMeta

from openhcs.core.callable_contract import CompilerPreparedAutoRegisterFamily

AUTO_REGISTER_REGISTRY_ATTRIBUTE = "__registry__"


class AutoRegisterRegistryPreparation:
    """Prepare AutoRegisterMeta registries at compiler/runtime boundaries."""

    @classmethod
    def prepare_module_registered_families(
        cls,
        modules: Iterable[ModuleType | None],
    ) -> tuple[type, ...]:
        """Run the preparation hook of each compiler-prepared family a module uses.

        Preparing one callable must not complete a lazy registry: reading a
        registry's members imports its whole discovery package. A family whose
        hook needs every member asks its own registry.
        """
        families = cls.module_registry_owners(modules, compiler_prepared_only=True)
        for family in families:
            family.prepare_registered_family()
        return families

    @classmethod
    def discover_module_registries(
        cls,
        modules: Iterable[ModuleType | None],
    ) -> tuple[type, ...]:
        """Complete every lazy registry the modules use, without family warmups.

        Serving readiness calls this once for the whole catalog so that no
        registry is first discovered during compilation or execution.
        """
        families = cls.module_registry_owners(modules, compiler_prepared_only=False)
        for family in families:
            tuple(family.__registry__.values())
        return families

    @classmethod
    def module_registry_owners(
        cls,
        modules: Iterable[ModuleType | None],
        *,
        compiler_prepared_only: bool,
    ) -> tuple[type, ...]:
        """Derive registry owners once for both discovery and preparation."""
        registry_ids: set[int] = set()
        families: list[type] = []
        for module in modules:
            if not isinstance(module, ModuleType):
                continue
            for candidate in cls.module_registry_families(module):
                if compiler_prepared_only and not issubclass(
                    candidate, CompilerPreparedAutoRegisterFamily
                ):
                    continue
                registry = candidate.__registry__
                registry_id = id(registry)
                if registry_id in registry_ids:
                    continue
                families.append(candidate)
                registry_ids.add(registry_id)
        return tuple(families)

    @staticmethod
    def module_registry_families(
        module: ModuleType,
    ) -> tuple[type, ...]:
        """Return AutoRegisterMeta classes in a module that own registries."""
        return AutoRegisterRegistryPreparation.cached_module_registry_families(
            module.__name__
        )

    @staticmethod
    @lru_cache(maxsize=None)
    def cached_module_registry_families(
        module_name: str,
    ) -> tuple[type, ...]:
        """Return cached AutoRegisterMeta registry families for one loaded module."""
        module = sys.modules.get(module_name)
        if module is None:
            return ()
        families: list[type] = []
        for candidate in vars(module).values():
            if not isinstance(candidate, type):
                continue
            if not isinstance(candidate, AutoRegisterMeta):
                continue
            if AUTO_REGISTER_REGISTRY_ATTRIBUTE not in vars(candidate):
                continue
            families.append(candidate)
        return tuple(families)
