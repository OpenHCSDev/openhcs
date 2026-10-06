"""Public function lookup and registry-owned import projections.

``RegistryService`` owns the complete catalog. Persisted custom functions have a
separate process-local projection owned by ``CustomFunctionRuntimeRegistry``;
this module coordinates source reconciliation and delegates exact canonical
lookup to the registry declaration without copying catalog state.
"""

from __future__ import annotations

import ast
import logging
import sys
import threading
import types
from collections.abc import Callable, Mapping
from importlib.machinery import PathFinder
from typing import Any

from arraybridge.types import VALID_MEMORY_TYPES

import openhcs
from openhcs.core.callable_contract import CallableContract

logger = logging.getLogger(__name__)

_registry_lock = threading.RLock()
_registry_initialized = False
_external_projection_exports: dict[str, set[str]] = {}
_external_projection_modules: set[str] = set()


def pipeline_source_requires_import_projection(source: str) -> bool:
    """Admit direct imports without building the external virtual-module view.

    The registry owns virtual ``openhcs.<library>`` modules, while real
    OpenHCS package children are importable without registry initialization.
    Dynamic imports conservatively retain the full projection.
    """

    requested_modules: set[str] = set()
    for node in ast.walk(ast.parse(source)):
        if isinstance(node, ast.Import):
            requested_modules.update(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            if node.level:
                return True
            if node.module == "openhcs":
                requested_modules.update(
                    f"openhcs.{alias.name}" for alias in node.names
                )
            elif node.module is not None:
                requested_modules.add(node.module)
        elif isinstance(node, ast.Call) and (
            (
                isinstance(node.func, ast.Name)
                and node.func.id in {"__import__", "exec", "eval"}
            )
            or (
                isinstance(node.func, ast.Attribute)
                and node.func.attr == "import_module"
            )
        ):
            if not node.args or not isinstance(node.args[0], ast.Constant):
                return True
            imported = node.args[0].value
            if not isinstance(imported, str):
                return True
            if isinstance(node.func, ast.Name) and node.func.id in {"exec", "eval"}:
                return True
            requested_modules.add(imported)

    for module_name in requested_modules:
        parts = module_name.split(".")
        if len(parts) < 2 or parts[0] != "openhcs":
            continue
        top_level_module = f"openhcs.{parts[1]}"
        if PathFinder.find_spec(top_level_module, openhcs.__path__) is None:
            return True
    return False


def _create_external_virtual_modules(all_functions: Mapping[str, Any]) -> None:
    """Reconcile the canonical external-callable import projection."""

    external_functions_by_module: dict[str, dict[str, Callable]] = {}
    for metadata in all_functions.values():
        virtual_module = metadata.registry.public_projection_module(metadata)
        if virtual_module is None:
            continue
        external_functions_by_module.setdefault(virtual_module, {})[
            metadata.func.__name__
        ] = metadata.func

    all_virtual_modules = {
        ".".join(parts[:index])
        for virtual_module in external_functions_by_module
        for parts in (virtual_module.split("."),)
        for index in range(2, len(parts) + 1)
    }
    created_modules = []
    with _registry_lock:
        for virtual_module, previous_names in _external_projection_exports.items():
            module = sys.modules.get(virtual_module)
            if module is None:
                continue
            desired_names = external_functions_by_module.get(virtual_module, {})
            for function_name in previous_names - desired_names.keys():
                vars(module).pop(function_name, None)

        for virtual_module in sorted(all_virtual_modules):
            if virtual_module in sys.modules:
                continue
            module = types.ModuleType(virtual_module)
            module.__doc__ = (
                "OpenHCS decorated callable projection for "
                f"{virtual_module.removeprefix('openhcs.')}"
            )
            if any(
                candidate.startswith(f"{virtual_module}.")
                for candidate in all_virtual_modules
            ):
                module.__path__ = []
            sys.modules[virtual_module] = module
            parent_name, _, child_name = virtual_module.rpartition(".")
            parent_module = sys.modules.get(parent_name)
            if parent_module is not None and child_name not in vars(parent_module):
                setattr(parent_module, child_name, module)
            _external_projection_modules.add(virtual_module)
            created_modules.append(virtual_module)

        for virtual_module, functions in external_functions_by_module.items():
            module = sys.modules[virtual_module]
            for function_name, func in functions.items():
                setattr(module, function_name, func)

        stale_modules = _external_projection_modules - all_virtual_modules
        for virtual_module in sorted(stale_modules, reverse=True):
            module = sys.modules.pop(virtual_module, None)
            parent_name, _, child_name = virtual_module.rpartition(".")
            parent_module = sys.modules.get(parent_name)
            if (
                parent_module is not None
                and vars(parent_module).get(child_name) is module
            ):
                vars(parent_module).pop(child_name, None)
            _external_projection_modules.discard(virtual_module)

        _external_projection_exports.clear()
        _external_projection_exports.update(
            {
                module_name: set(functions)
                for module_name, functions in external_functions_by_module.items()
            }
        )

    if created_modules:
        logger.info(
            "Created %d external callable modules",
            len(created_modules),
        )


def synchronize_custom_function_sources() -> None:
    """Reconcile persisted custom declarations with their runtime projection."""

    from openhcs.processing.custom_functions.manager import CustomFunctionManager
    from openhcs.processing.custom_functions.runtime_registry import (
        CustomFunctionRuntimeRegistry,
    )

    manager = CustomFunctionManager()
    source_revision = manager.source_revision()
    with _registry_lock:
        if source_revision == CustomFunctionRuntimeRegistry.source_revision():
            return

    loaded_count = manager.load_all_custom_functions()
    if loaded_count:
        logger.info(
            "Loaded %d custom function declaration(s)",
            loaded_count,
        )


def initialize_registry() -> None:
    """Prepare canonical metadata, custom sources, and public import projections."""

    global _registry_initialized
    with _registry_lock:
        if _registry_initialized:
            return

    from openhcs.processing.backends.lib_registry.registry_service import (
        RegistryService,
    )

    # Load the canonical projection first so custom name claims are checked
    # against proof already owned by the registry, without a copied sidecar.
    RegistryService.get_all_functions_with_metadata()
    synchronize_custom_function_sources()
    metadata = RegistryService.get_all_functions_with_metadata()
    _create_external_virtual_modules(metadata)

    with _registry_lock:
        _registry_initialized = True
    logger.info(
        "Function catalog initialized with %d canonical entries",
        len(metadata),
    )


def _auto_initialize_registry() -> None:
    """Compatibility entry point for explicit application startup owners."""

    initialize_registry()


def get_functions_by_memory_type(memory_type: str) -> list[Callable]:
    """Return canonical callables whose declared input role uses ``memory_type``."""

    if memory_type not in VALID_MEMORY_TYPES:
        raise ValueError(
            f"Invalid memory type: {memory_type}. "
            f"Valid types are: {', '.join(sorted(VALID_MEMORY_TYPES))}"
        )

    from openhcs.processing.backends.lib_registry.registry_service import (
        RegistryService,
    )

    functions: list[Callable] = []
    seen: set[int] = set()
    for metadata in RegistryService.get_all_functions_with_metadata().values():
        contract = CallableContract.from_callable(metadata.func)
        if contract.input_memory_type != memory_type:
            continue
        identity = id(metadata.func)
        if identity in seen:
            continue
        seen.add(identity)
        functions.append(metadata.func)
    return functions


def get_function_info(func: Callable) -> dict[str, Any]:
    """Return declaration-derived summary information for one callable."""

    contract = CallableContract.from_callable(func)
    if contract.input_memory_type is None or contract.output_memory_type is None:
        raise ValueError(
            f"Function {func.__name__!r} does not declare array memory boundaries"
        )
    return {
        "name": func.__name__,
        "input_memory_type": contract.input_memory_type,
        "output_memory_type": contract.output_memory_type,
        # Historical facade key, projected from the same input-memory declaration.
        "backend": contract.input_memory_type,
        "doc": func.__doc__,
    }


def is_registry_initialized() -> bool:
    """Return whether the application startup projection has completed."""

    with _registry_lock:
        return _registry_initialized


def get_valid_memory_types() -> set[str]:
    """Return the memory names declared by ArrayBridge."""

    return set(VALID_MEMORY_TYPES)


def get_function_by_name(
    function_name: str,
    memory_type: str,
) -> Callable | None:
    """Resolve a legacy name only when it identifies exactly one callable."""

    from openhcs.processing.backends.lib_registry.registry_service import (
        RegistryService,
    )

    matches = {
        function_id: metadata.func
        for function_id, metadata in RegistryService.get_all_functions_with_metadata().items()
        if CallableContract.from_callable(metadata.func).input_memory_type
        == memory_type
        and function_name in {metadata.display_name, metadata.func.__name__}
    }
    if not matches:
        return None
    if len(matches) > 1:
        raise LookupError(
            f"Function name {function_name!r} with input memory {memory_type!r} "
            "is ambiguous; use one of the canonical function IDs: "
            f"{tuple(sorted(matches))!r}."
        )
    return next(iter(matches.values()))


def get_function(function_id: str) -> Callable:
    """Return the callable owned by one exact canonical function ID."""

    from openhcs.processing.backends.lib_registry.registry_service import (
        RegistryService,
    )

    return RegistryService.metadata_for_canonical_key(function_id).func


def get_all_function_names(memory_type: str) -> list[str]:
    """Return canonical callable names for one declared input memory."""

    return [func.__name__ for func in get_functions_by_memory_type(memory_type)]
