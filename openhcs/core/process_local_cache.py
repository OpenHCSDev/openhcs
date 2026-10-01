"""Shared bounded values and process-local cache lifetime policies."""

from __future__ import annotations

from collections import OrderedDict
from dataclasses import dataclass, field
from collections.abc import Sequence
from typing import Any, ClassVar, Generic, TypeVar
from threading import Lock
from _thread import LockType

from metaclass_registry import AutoRegisterMeta

CacheKey = TypeVar("CacheKey")
CachedValue = TypeVar("CachedValue")


def identity_owner_tuples_match(
    left: Sequence[object],
    right: Sequence[object],
) -> bool:
    """Return whether identity-keyed cache owners still reference the same objects."""
    return len(left) == len(right) and all(
        left_owner is right_owner
        for left_owner, right_owner in zip(left, right, strict=True)
    )


def named_identity_owner_tuples_match(
    left: Sequence[tuple[str, object]],
    right: Sequence[tuple[str, object]],
) -> bool:
    """Return whether named identity-keyed cache owners still match."""
    return len(left) == len(right) and all(
        left_name == right_name and left_owner is right_owner
        for (left_name, left_owner), (right_name, right_owner) in zip(
            left,
            right,
            strict=True,
        )
    )


@dataclass(slots=True)
class BoundedCache(Generic[CacheKey, CachedValue]):
    """Bounded LRU values with lifetime supplied by their owning consumer."""

    max_entries: int = 4096
    entries: OrderedDict[CacheKey, CachedValue] = field(default_factory=OrderedDict)

    def cached_value(self, key: CacheKey) -> CachedValue | None:
        if key not in self.entries:
            return None
        value = self.entries[key]
        self.entries.move_to_end(key)
        return value

    def store_value(self, key: CacheKey, value: CachedValue) -> CachedValue:
        self.entries[key] = value
        self.entries.move_to_end(key)
        while len(self.entries) > self.max_entries:
            self.entries.popitem(last=False)
        return value

    def clear(self) -> None:
        """Discard all values retained by this cache instance."""
        self.entries.clear()


@dataclass
class SynchronizedBoundedCache(BoundedCache[CacheKey, CachedValue]):
    """Bounded storage whose individual mutations share one instance lock."""

    _lock: LockType = field(default_factory=Lock, init=False, repr=False, compare=False)

    def cached_value(self, key: CacheKey) -> CachedValue | None:
        with self._lock:
            return super().cached_value(key)

    def store_value(self, key: CacheKey, value: CachedValue) -> CachedValue:
        with self._lock:
            return super().store_value(key, value)

    def clear(self) -> None:
        with self._lock:
            super().clear()


@dataclass(slots=True)
class ProcessLocalBoundedCache(BoundedCache[CacheKey, CachedValue]):
    """Bounded values with one process-local singleton per concrete subclass."""

    def __init_subclass__(cls, **kwargs) -> None:
        # slots=True replaces the dataclass; name its final class for cooperative super.
        super(ProcessLocalBoundedCache, cls).__init_subclass__(**kwargs)
        cls._process_cache = None
        cls._process_cache_lock = Lock()

    @classmethod
    def process_cache(cls) -> "ProcessLocalBoundedCache[CacheKey, CachedValue]":
        cache = cls._process_cache
        if cache is None:
            with cls._process_cache_lock:
                cache = cls._process_cache
                if cache is None:
                    cache = cls()
                    cls._process_cache = cache
        return cache

    @classmethod
    def clear_process_cache(cls) -> None:
        """Discard the singleton process-local cache for this concrete cache type."""
        cache = cls._process_cache
        if cache is not None:
            cache.clear()

    _process_cache: ClassVar["ProcessLocalBoundedCache[object, object] | None"] = None
    _process_cache_lock: ClassVar[LockType] = Lock()


@dataclass(slots=True)
class RegisteredProcessLocalBoundedCache(
    ProcessLocalBoundedCache[CacheKey, CachedValue],
    metaclass=AutoRegisterMeta,
):
    """Process-local cache whose concrete owners participate in runtime cleanup."""

    __registry_key__ = "__name__"
    __registry__: ClassVar[
        dict[str, type["RegisteredProcessLocalBoundedCache[Any, Any]"]]
    ] = {}

    @classmethod
    def clear_registered_process_caches(cls) -> None:
        """Clear all imported concrete cache families registered by inheritance."""
        for cache_type in tuple(cls.__registry__.values()):
            cache_type.clear_process_cache()


class IdentityBoundProcessCache(
    ProcessLocalBoundedCache[int, tuple[object, Any]],
    metaclass=AutoRegisterMeta,
):
    """Process-local cache whose keys are protected against id reuse."""

    __registry_key__ = "registry_key"
    __skip_if_no_key__ = True

    max_entries = 4096
    registry_key: ClassVar[str | None] = None

    @classmethod
    def clear_registered_process_caches(cls) -> None:
        """Clear all imported identity-bound cache families registered by inheritance."""
        for cache_type in tuple(cls.__registry__.values()):
            cache_type.clear_process_cache()

    def get_bound(
        self,
        owner: object,
    ) -> Any | None:
        cache_key = id(owner)
        cached = self.cached_value(cache_key)
        if cached is None:
            return None
        cached_owner, value = cached
        if cached_owner is not owner:
            del self.entries[cache_key]
            return None
        return value

    def put_bound(
        self,
        owner: object,
        value: Any,
    ) -> Any:
        return self.store_value(id(owner), (owner, value))[1]


def clear_registered_process_local_caches() -> None:
    """Clear all imported process-local runtime cache families."""
    RegisteredProcessLocalBoundedCache.clear_registered_process_caches()
    IdentityBoundProcessCache.clear_registered_process_caches()
