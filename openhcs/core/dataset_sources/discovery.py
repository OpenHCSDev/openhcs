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

    return RegistryConfig(
        registry_dict=LazyDiscoveryDict(enable_cache=False),
        key_attribute=key_attribute,
        skip_if_no_key=skip_if_no_key,
        registry_name=registry_name,
        discovery_package=_KERNEL_PACKAGE,
        discovery_function=_discover_kernel_and_domain,
        **kwargs,
    )


__all__ = ["domain_registry_config", "load_domain_extensions"]
