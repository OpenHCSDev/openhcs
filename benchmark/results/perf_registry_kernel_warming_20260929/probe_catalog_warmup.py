import json
import time
from pathlib import Path

from numba import config

from openhcs.agent.services.function_catalog_service import FunctionCatalogService
from openhcs.processing.backends.lib_registry.registry_service import RegistryService
from openhcs.runtime.function_catalog_preparation import FunctionCatalogPreparation

service = FunctionCatalogService()
# Establish the actual metadata hit before asking the production Future to warm kernels.
started = time.perf_counter()
metadata = RegistryService._load_valid_persistent_catalog()
print(
    json.dumps(
        {
            "phase": "existing_metadata",
            "seconds": time.perf_counter() - started,
            "valid": metadata is not None,
            "numba_cache": config.CACHE_DIR,
            "nbi_before": len(list(Path(config.CACHE_DIR).rglob("*.nbi"))),
        }
    ),
    flush=True,
)
started = time.perf_counter()
preparation = FunctionCatalogPreparation(service)
preparation.wait_until_ready(
    lambda status: print(json.dumps({"status": status.message}), flush=True),
    observation_interval_seconds=5,
)
print(
    json.dumps(
        {
            "phase": "production_catalog_warmup",
            "seconds": time.perf_counter() - started,
            "nbi_after": len(list(Path(config.CACHE_DIR).rglob("*.nbi"))),
            "functions": len(service.catalog(compact_signatures=True).items),
        }
    ),
    flush=True,
)
preparation.cancel_and_join()
