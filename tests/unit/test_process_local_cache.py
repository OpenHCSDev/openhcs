from openhcs.core.process_local_cache import (
    BoundedCache,
    IdentityBoundProcessCache,
    ProcessLocalBoundedCache,
    RegisteredProcessLocalBoundedCache,
    clear_registered_process_local_caches,
)
from openhcs.core.measurement_feature_queries import RuntimeObjectLabelMeasurementQueryCache
from openhcs.core.runtime_artifact_queries import RuntimeMeasurementTablesQueryCache


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
    from concurrent.futures import ThreadPoolExecutor
    from dataclasses import dataclass
    from threading import Barrier

    from openhcs.core.process_local_cache import SynchronizedBoundedCache

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
