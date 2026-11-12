"""
Build utilities for openhcs package.

This module provides shared utilities for build-time operations,
including ZeroC-Ice installation for OMERO integration.
"""

# Use relative imports to avoid circular dependency during build
from openhcs.build_utils.zeroc_ice_installer import (
    get_python_version,
    get_platform,
    get_wheel_url,
    download_wheel,
    install_wheel,
    verify_installation,
    install_zeroc_ice,
    ZEROC_ICE_BASE_URL,
    ZEROC_ICE_VERSION,
    SUPPORTED_PYTHON_VERSIONS,
)

__all__ = [
    "get_python_version",
    "get_platform",
    "get_wheel_url",
    "download_wheel",
    "install_wheel",
    "verify_installation",
    "install_zeroc_ice",
    "ZEROC_ICE_BASE_URL",
    "ZEROC_ICE_VERSION",
    "SUPPORTED_PYTHON_VERSIONS",
]
