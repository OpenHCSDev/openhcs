"""Registry discovery shared by the kernel families that domains extend.

A family root declares :func:`domain_registry_config` as its
``__registry_config__``. On first access its registry imports every module of
this package (the kernel's own members) and then the modules the active axis
family lists in ``extension_modules`` (the domain's members). The kernel never
names a domain module.
"""

from __future__ import annotations

from importlib import import_module
from typing import Any, Iterable

from metaclass_registry import LazyDiscoveryDict, RegistryConfig
from metaclass_registry.discovery import discover_registry_classes

from openhcs.core.axes import AxisFamily

_KERNEL_PACKAGE = __name__.rpartition(".")[0]
_domain_registries: list[LazyDiscoveryDict] = []


def load_domain_extensions() -> None:
    """Import the active family's registration modules (idempotent)."""

    for module_name in AxisFamily.active().extension_modules:
        import_module(module_name)


def _discover_kernel_and_domain(
    package_path: Iterable[str],
    package_prefix: str,
    base_class: type,
) -> None:
    discover_registry_classes(package_path, package_prefix, base_class)
    load_domain_extensions()


def domain_registry_config(
    *,
    key_attribute: str,
    registry_name: str,
    skip_if_no_key: bool = True,
    **kwargs: Any,
) -> RegistryConfig:
    """Registry configuration for a kernel family that domains extend."""

    registry = LazyDiscoveryDict(enable_cache=False)
    _domain_registries.append(registry)
    return RegistryConfig(
        registry_dict=registry,
        key_attribute=key_attribute,
        skip_if_no_key=skip_if_no_key,
        registry_name=registry_name,
        discovery_package=_KERNEL_PACKAGE,
        discovery_function=_discover_kernel_and_domain,
        **kwargs,
    )


def discover_domain_registries() -> None:
    """Complete every domain-extended family registry now, as first access would.

    A server calls this before it forks workers and reports ready, so neither
    it nor a worker imports kernel or domain members while serving a request.
    Discovery imports the family roots that were not yet defined, so the loop
    follows the list as it grows.
    """

    discovered = 0
    while discovered < len(_domain_registries):
        _domain_registries[discovered].values()
        discovered += 1


__all__ = [
    "discover_domain_registries",
    "domain_registry_config",
    "load_domain_extensions",
]
