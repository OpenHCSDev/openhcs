"""Environment declarations shared by UI bridge producers and clients."""

from __future__ import annotations

from pathlib import Path
from typing import Mapping


class UIConfigCacheEnvironment:
    """Own the optional process-local UI configuration persistence boundary."""

    cache_file_path_key = "OPENHCS_UI_CONFIG_CACHE_FILE"

    @classmethod
    def child_process_environment_keys(cls) -> tuple[str, ...]:
        """Preserve the same configuration authority in child processes."""

        return (cls.cache_file_path_key,)

    @classmethod
    def cache_file_path(
        cls,
        environment: Mapping[str, str] | None = None,
    ) -> Path | None:
        """Resolve an explicitly isolated cache file, when one is declared."""

        import os

        values = os.environ if environment is None else environment
        raw_path = values.get(cls.cache_file_path_key)
        if raw_path is None:
            return None
        normalized = raw_path.strip()
        if not normalized:
            raise ValueError(f"{cls.cache_file_path_key} cannot be empty.")
        cache_file = Path(normalized).expanduser()
        if not cache_file.is_absolute():
            raise ValueError(f"{cls.cache_file_path_key} must be an absolute path.")
        return cache_file.resolve(strict=False)


class UiBridgeDescriptorEnvironment:
    """Own the environment selectors for one live UI bridge descriptor."""

    descriptor_file_path_key = "OPENHCS_UI_BRIDGE_DESCRIPTOR"
    descriptor_directory_path_key = "OPENHCS_UI_BRIDGE_DESCRIPTOR_DIR"

    @classmethod
    def child_process_environment_keys(cls) -> tuple[str, str]:
        """Return every selector required by a descriptor-consuming child."""

        return (
            cls.descriptor_file_path_key,
            cls.descriptor_directory_path_key,
        )
