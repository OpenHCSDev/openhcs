"""Simple metadata cache service for OpenHCS."""

import logging
import threading
from pathlib import Path
from typing import Dict, Optional

from openhcs.core.components.validation import convert_enum_by_value
from openhcs.constants.constants import AllComponents

logger = logging.getLogger(__name__)


class MetadataCache:
    """Stores component key→name mappings with basic invalidation and thread safety."""

    def __init__(self):
        self._cache: Dict["AllComponents", Dict[str, Optional[str]]] = {}
        self._metadata_file_mtimes: Dict[Path, float] = {}
        self._lock = threading.Lock()

    def cache_metadata(
        self, microscope_handler, plate_path: Path, component_keys_cache: Dict
    ) -> None:
        """Cache all metadata from metadata handler."""
        with self._lock:
            # Parse all metadata once
            metadata = microscope_handler.metadata_handler.parse_metadata(plate_path)
            logger.info(f"🔍 METADATA_CACHE: parse_metadata returned: {metadata}")

            # Initialize all components with keys mapped to None
            for component in AllComponents:
                component_keys = component_keys_cache.get(component, [])
                self._cache[component] = {key: None for key in component_keys}

            # Update with actual metadata where available
            for component_name, mapping in metadata.items():
                component = AllComponents(component_name)
                logger.info(
                    f"🔍 METADATA_CACHE: Caching {component_name} -> {component}: {mapping}"
                )
                if component in self._cache:
                    combined_cache = self._cache[component].copy()
                    for metadata_key in mapping.keys():
                        if metadata_key not in combined_cache:
                            combined_cache[metadata_key] = None
                    combined_cache.update(mapping)
                    self._cache[component] = combined_cache
                else:
                    self._cache[component] = mapping

            logger.info(f"🔍 METADATA_CACHE: Final cache state: {self._cache}")

            # Store metadata file mtime for invalidation
            metadata_file = microscope_handler.metadata_handler.find_metadata_file(
                plate_path
            )
            if metadata_file and metadata_file.exists():
                self._metadata_file_mtimes[metadata_file] = (
                    metadata_file.stat().st_mtime
                )

    def get_component_metadata(self, component, key: str) -> Optional[str]:
        """Get metadata display name for a component key. Accepts GroupBy or VariableComponents."""
        with self._lock:
            if not self._is_cache_valid():
                logger.warning(f"🔍 METADATA_CACHE: Cache invalid, clearing")
                self._cache.clear()
                return None

            # Convert GroupBy to AllComponents using OpenHCS generic utility
            component = convert_enum_by_value(component, AllComponents) or component
            component_cache = self._cache.get(component)
            if component_cache is None:
                logger.debug("🔍 METADATA_CACHE: component %s not cached", component)
                return None

            if key not in component_cache:
                logger.debug(
                    "🔍 METADATA_CACHE: key %r not cached for %s", key, component
                )
                return None

            return component_cache.get(key)

    def get_cached_metadata(
        self, component: "AllComponents"
    ) -> Optional[Dict[str, Optional[str]]]:
        """Get all cached metadata for a component."""
        with self._lock:
            if not self._is_cache_valid():
                self._cache.clear()
                return None
            return self._cache.get(component)

    def clear_cache(self) -> None:
        """Clear cached metadata."""
        with self._lock:
            self._cache.clear()
            self._metadata_file_mtimes.clear()

    def _is_cache_valid(self) -> bool:
        """Check if cache is valid by comparing file mtimes."""
        for metadata_file, cached_mtime in self._metadata_file_mtimes.items():
            if (
                not metadata_file.exists()
                or metadata_file.stat().st_mtime != cached_mtime
            ):
                return False
        return True


# Global cache instance
_global_metadata_cache: Optional[MetadataCache] = None


def get_metadata_cache() -> MetadataCache:
    """Get global metadata cache instance."""
    global _global_metadata_cache
    if _global_metadata_cache is None:
        _global_metadata_cache = MetadataCache()
    return _global_metadata_cache
