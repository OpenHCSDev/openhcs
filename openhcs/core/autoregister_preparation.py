"""Compiler-bound preparation for AutoRegisterMeta registries."""

from __future__ import annotations

import multiprocessing
import sys
from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass
from functools import lru_cache
from types import ModuleType
from typing import Iterable

from metaclass_registry import AutoRegisterMeta

from openhcs.core.callable_contract import CompilerPreparedAutoRegisterFamily

AUTO_REGISTER_REGISTRY_ATTRIBUTE = "__registry__"


@dataclass(slots=True)
class AutoRegisterRegistryPreparationReport:
    """Summary of AutoRegister registries prepared before worker execution."""

    registry_count: int = 0
    class_count: int = 0
    prepared_family_count: int = 0


class AutoRegisterRegistryPreparation:
    """Prepare AutoRegisterMeta registries at compiler/runtime boundaries."""

    @classmethod
    def prepare_module_registered_families(
        cls,
        modules: Iterable[ModuleType | None],
    ) -> AutoRegisterRegistryPreparationReport:
        """Prepare compiler-owned AutoRegister families defined in modules."""
        return cls._scan_module_registries(modules, prepare_families=True)

    @classmethod
    def discover_module_registries(
        cls,
        modules: Iterable[ModuleType | None],
    ) -> AutoRegisterRegistryPreparationReport:
        """Force registry discovery without invoking backend family warmups."""
        return cls._scan_module_registries(modules, prepare_families=False)

    @classmethod
    def prepare_module_caches_in_children(
        cls,
        modules: Iterable[ModuleType | None],
    ) -> None:
        """Populate eligible cold compiler caches before normal parent preparation."""
        if "fork" not in multiprocessing.get_all_start_methods():
            return
        families = tuple(
            family
            for family in cls._unique_module_registry_families(
                modules, compiler_prepared_only=True
            )
            if family.can_prepare_in_child()
        )
        if len(families) < 2:
            return
        with ProcessPoolExecutor(
            max_workers=min(4, len(families)),
            mp_context=multiprocessing.get_context("fork"),
        ) as executor:
            futures = tuple(
                executor.submit(family.prepare_registered_family) for family in families
            )
            for future in futures:
                future.result()

    @classmethod
    def _scan_module_registries(
        cls,
        modules: Iterable[ModuleType | None],
        *,
        prepare_families: bool,
    ) -> AutoRegisterRegistryPreparationReport:
        """Scan module registries and optionally prepare module-owned families."""
        report = AutoRegisterRegistryPreparationReport()
        for candidate in cls._unique_module_registry_families(
            modules, compiler_prepared_only=prepare_families
        ):
            registry = candidate.__registry__
            report.class_count += len(tuple(registry.values()))
            report.registry_count += 1
            if prepare_families:
                candidate.prepare_registered_family()
                report.prepared_family_count += 1
        return report

    @classmethod
    def _unique_module_registry_families(
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
                # Counting an unrelated lazy registry would discover its whole
                # package even though this path has no preparation hook to run.
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
