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
