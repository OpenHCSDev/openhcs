from dataclasses import dataclass
from concurrent.futures import ThreadPoolExecutor
from threading import Barrier

import pytest

from openhcs.core.process_local_cache import (
    BoundedCache,
    IdentityBoundProcessCache,
    ProcessLocalBoundedCache,
    RegisteredProcessLocalBoundedCache,
    SynchronizedBoundedCache,
    clear_registered_process_local_caches,
)
from openhcs.core.measurement_feature_queries import (
    RuntimeObjectLabelMeasurementQueryCache,
)
from openhcs.core.runtime_artifact_queries import RuntimeMeasurementTablesQueryCache


@pytest.mark.parametrize(
    "base",
    (
        ProcessLocalBoundedCache,
        RegisteredProcessLocalBoundedCache,
        IdentityBoundProcessCache,
    ),
)
def test_warmed_parent_cache_does_not_become_child_singleton(base):
    @dataclass
    class ParentCache(base):
        max_entries: int = 2
        registry_key = "test_warmed_parent_cache"

    parent = ParentCache.process_cache()
    parent.store_value("parent", "parent-only")

    @dataclass(slots=True)
    class ChildCache(ParentCache):
        max_entries: int = 3
        registry_key = "test_warmed_child_cache"

    barrier = Barrier(8)

    def obtain_child(_index):
        barrier.wait(timeout=5)
        return ChildCache.process_cache()

    with ThreadPoolExecutor(max_workers=8) as pool:
        children = tuple(pool.map(obtain_child, range(8)))
    child = children[0]
    assert all(cache is child for cache in children)
    assert type(parent) is ParentCache
    assert type(child) is ChildCache
    assert child is not parent
    assert parent.max_entries == 2
    assert child.max_entries == 3
    assert child.cached_value("parent") is None
    child.store_value("child", "child-only")
    ChildCache.clear_process_cache()
    assert ChildCache.process_cache() is child
    assert child.cached_value("child") is None
    assert parent.cached_value("parent") == "parent-only"
    if base is not ProcessLocalBoundedCache:
        clear_registered_process_local_caches()
        assert parent.cached_value("parent") is None


def test_warmed_diamond_cache_preserves_synchronization_lru_and_cleanup():
    @dataclass
    class ParentDiamondCache(
        SynchronizedBoundedCache[str, str],
        RegisteredProcessLocalBoundedCache[str, str],
    ):
        max_entries: int = 2

    parent = ParentDiamondCache.process_cache()
    parent.store_value("parent", "parent-only")

    class LeftDiamondCache(ParentDiamondCache):
        pass

    left = LeftDiamondCache.process_cache()
    left.store_value("left", "left-only")

    class RightDiamondCache(ParentDiamondCache):
        pass

    right = RightDiamondCache.process_cache()
    right.store_value("right", "right-only")

    class DiamondCache(LeftDiamondCache, RightDiamondCache):
        pass

    diamond = DiamondCache.process_cache()
    assert tuple(type(cache) for cache in (parent, left, right, diamond)) == (
        ParentDiamondCache,
        LeftDiamondCache,
        RightDiamondCache,
        DiamondCache,
    )
    assert len({id(cache) for cache in (parent, left, right, diamond)}) == 4
    assert len({id(cache._lock) for cache in (parent, left, right, diamond)}) == 4
    assert (
        len(
            {
                id(cls._process_cache_lock)
                for cls in (
                    ParentDiamondCache,
                    LeftDiamondCache,
                    RightDiamondCache,
                    DiamondCache,
                )
            }
        )
        == 4
    )
    assert all(diamond.cached_value(key) is None for key in ("parent", "left", "right"))
    diamond.store_value("oldest", "first")
    diamond.store_value("middle", "second")
    assert diamond.cached_value("oldest") == "first"
    diamond.store_value("newest", "third")
    assert diamond.cached_value("middle") is None
    assert all(
        RegisteredProcessLocalBoundedCache.__registry__[type(cache).__name__]
        is type(cache)
        for cache in (parent, left, right, diamond)
    )
    clear_registered_process_local_caches()
    assert all(not cache.entries for cache in (parent, left, right, diamond))


def test_process_cache_class_hook_cooperates_with_other_base():
    observed = []

    class HookObserver:
        def __init_subclass__(cls, *, marker, **kwargs):
            super().__init_subclass__(**kwargs)
            observed.append((cls, marker))

    class CooperativeCache(ProcessLocalBoundedCache, HookObserver, marker="owner"):
        pass

    assert observed == [(CooperativeCache, "owner")]
    assert type(CooperativeCache.process_cache()) is CooperativeCache


def test_store_query_domains_use_bounded_values_without_process_singletons():
    for cache_type in (
        RuntimeObjectLabelMeasurementQueryCache,
        RuntimeMeasurementTablesQueryCache,
    ):
        assert issubclass(cache_type, BoundedCache)
        assert not issubclass(cache_type, ProcessLocalBoundedCache)


def test_registered_process_local_cache_cleanup_clears_cache_instance():
    class TestRegisteredProcessLocalCleanupCache(
        RegisteredProcessLocalBoundedCache[str, str]
    ):
        max_entries = 2

    cache = TestRegisteredProcessLocalCleanupCache.process_cache()
    cache.store_value("source", "payload")

    assert cache.cached_value("source") == "payload"

    clear_registered_process_local_caches()

    assert cache.cached_value("source") is None


def test_identity_bound_process_cache_cleanup_clears_cache_instance():
    class TestIdentityBoundProcessLocalCleanupCache(IdentityBoundProcessCache):
        registry_key = "test_identity_bound_process_local_cleanup"

    owner = object()
    cache = TestIdentityBoundProcessLocalCleanupCache.process_cache()
    cache.put_bound(owner, "payload")

    assert cache.get_bound(owner) == "payload"

    clear_registered_process_local_caches()

    assert cache.get_bound(owner) is None


def test_synchronized_process_cache_preserves_lru_and_concurrent_singleton():
    @dataclass
    class TestSynchronizedProcessCache(
        SynchronizedBoundedCache[str, str],
        RegisteredProcessLocalBoundedCache[str, str],
    ):
        max_entries: int = 2

    barrier = Barrier(8)

    def obtain_cache(_index):
        barrier.wait(timeout=5)
        return TestSynchronizedProcessCache.process_cache()

    with ThreadPoolExecutor(max_workers=8) as pool:
        caches = tuple(pool.map(obtain_cache, range(8)))
    cache = caches[0]
    assert all(value is cache for value in caches)
    assert cache.max_entries == 2
    cache.store_value("oldest", "first")
    cache.store_value("middle", "second")
    assert cache.cached_value("oldest") == "first"
    cache.store_value("newest", "third")
    assert cache.cached_value("middle") is None
    assert cache.cached_value("oldest") == "first"
    assert cache.cached_value("newest") == "third"
    clear_registered_process_local_caches()
    assert cache.cached_value("oldest") is None
    assert cache.cached_value("newest") is None


def test_numerical_cache_domains_keep_capacity_and_join_registered_cleanup():
    from openhcs.processing.backends.cellprofiler.granularity import (
        GranularityImageSeriesCache,
    )
    from openhcs.processing.backends.cellprofiler.image_quality import (
        RadialSpectrumGeometryCache,
    )
    from openhcs.processing.backends.cellprofiler.intensity_distribution import (
        RadialLabelGeometryCache,
    )
    from openhcs.processing.backends.cellprofiler.zernike import (
        ZernikeLabelGeometryCache,
    )

    cache_types = (
        GranularityImageSeriesCache,
        RadialSpectrumGeometryCache,
        RadialLabelGeometryCache,
        ZernikeLabelGeometryCache,
    )
    caches = tuple(cls.process_cache() for cls in cache_types)
    assert len({id(cache) for cache in caches}) == 4
    for cls, cache in zip(cache_types, caches, strict=True):
        assert cache.max_entries == 16
        assert RegisteredProcessLocalBoundedCache.__registry__[cls.__name__] is cls
    clear_registered_process_local_caches()
    assert all(not cache.entries for cache in caches)
