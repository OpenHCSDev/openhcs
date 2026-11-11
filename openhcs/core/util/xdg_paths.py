"""
XDG Base Directory Specification utilities for OpenHCS.

Provides standardized paths following XDG Base Directory Specification:
- Data: ~/.local/share/openhcs/
- Cache: ~/.local/share/openhcs/cache/
- Config: ~/.local/share/openhcs/config/
"""

import os
from pathlib import Path


def get_openhcs_data_dir(*, create: bool = True) -> Path:
    """
    Get the OpenHCS data directory following XDG Base Directory Specification.

    Returns:
        Path to ~/.local/share/openhcs/
    """
    data_home = Path(os.environ.get("XDG_DATA_HOME", Path.home() / ".local" / "share"))
    data_dir = data_home / "openhcs"
    if create:
        data_dir.mkdir(parents=True, exist_ok=True)
    return data_dir


def get_openhcs_cache_dir() -> Path:
    """
    Get the OpenHCS cache directory following XDG Base Directory Specification.

    Returns:
        Path to ~/.local/share/openhcs/cache/
    """
    cache_dir = get_openhcs_data_dir() / "cache"
    cache_dir.mkdir(parents=True, exist_ok=True)
    return cache_dir


def get_openhcs_config_dir() -> Path:
    """
    Get the OpenHCS config directory following XDG Base Directory Specification.

    Returns:
        Path to ~/.local/share/openhcs/config/
    """
    config_dir = get_openhcs_data_dir() / "config"
    config_dir.mkdir(parents=True, exist_ok=True)
    return config_dir


def get_openhcs_log_dir(*, create: bool = True) -> Path:
    """Return the shared OpenHCS log directory without creating it."""

    return get_openhcs_data_dir(create=create) / "logs"


def get_cache_file_path(filename: str) -> Path:
    """Return the path of a cache file under the OpenHCS cache directory."""

    return get_openhcs_cache_dir() / filename


def get_config_file_path(filename: str) -> Path:
    """Return the path of a config file under the OpenHCS config directory."""

    return get_openhcs_config_dir() / filename


def get_data_file_path(filename: str, *, create: bool = True) -> Path:
    """Return the path of a data file under the OpenHCS data directory."""

    return get_openhcs_data_dir(create=create) / filename
