"""OpenHCS cache domains are members of metaclass-registry's cache families.

The cache mechanisms themselves are tested in metaclass-registry; this checks
which OpenHCS domains join which family.
"""

from metaclass_registry.caches import BoundedCache, ProcessLocalBoundedCache

from openhcs.core.callable_contract import CallableContractRuntimeCache
from openhcs.core.measurement_feature_queries import (
    RuntimeObjectLabelMeasurementQueryCache,
)
from openhcs.core.measurement_lookup_dialect import RuntimeMeasurementLookupAliasCache
from openhcs.core.runtime_artifact_queries import RuntimeMeasurementTablesQueryCache
from openhcs.processing.backends.cellprofiler.granularity import (
    GranularityImageSeriesCache,
)
from openhcs.processing.backends.cellprofiler.image_quality import (
    RadialSpectrumGeometryCache,
)
from openhcs.processing.backends.cellprofiler.intensity_distribution import (
    RadialLabelGeometryCache,
)
from openhcs.processing.backends.cellprofiler.zernike import ZernikeLabelGeometryCache


def test_process_local_domains_join_family_cleanup_and_store_queries_do_not():
    numerical = (
        GranularityImageSeriesCache,
        RadialSpectrumGeometryCache,
        RadialLabelGeometryCache,
        ZernikeLabelGeometryCache,
    )
    process_local = (
        *numerical,
        RuntimeMeasurementLookupAliasCache,
        CallableContractRuntimeCache,
    )
    caches = tuple(cache_type.process_cache() for cache_type in process_local)
    assert len({id(cache) for cache in caches}) == len(process_local)
    assert all(cache.max_entries == 16 for cache in caches[: len(numerical)])
    for cache_type in process_local:
        assert ProcessLocalBoundedCache.__registry__[cache_type.process_cache_key] is cache_type

    owner = object()
    for cache in caches[:-1]:
        cache.store_value(("probe",), "value")
    caches[-1].put_bound(owner, "callable")
    ProcessLocalBoundedCache.clear_process_caches()
    assert all(not cache.entries for cache in caches)

    for cache_type in (
        RuntimeObjectLabelMeasurementQueryCache,
        RuntimeMeasurementTablesQueryCache,
    ):
        assert issubclass(cache_type, BoundedCache)
        assert not issubclass(cache_type, ProcessLocalBoundedCache)
