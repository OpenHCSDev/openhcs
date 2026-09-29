"""Global pytest configuration for OpenHCS integration tests."""

import os

from openhcs._source_dependencies import ensure_source_checkout_external_paths

ensure_source_checkout_external_paths()

import pytest

from tests.fiji_test_environment import configure_fiji_test_environment

# Configure before test collection imports any ImageJ runtime. Tests may change
# XDG_CACHE_HOME later; the immutable bundle must not follow those run caches.
configure_fiji_test_environment()

# Conditionally import pytest-qt only when not in CPU-only mode
CPU_ONLY_MODE = os.getenv("OPENHCS_CPU_ONLY", "false").lower() == "true"
if not CPU_ONLY_MODE:
    pytest_plugins = ["pytestqt"]
else:
    pytest_plugins = []


@pytest.fixture(autouse=True)
def cleanup_test_runtime_resources():
    """Release connection and process resources after every test."""

    from polystore import cleanup_backend_connections
    from zmqruntime import ViewerStateManager

    resolve_viewer_manager = ViewerStateManager.get_instance
    yield

    try:
        resolve_viewer_manager().stop_all_viewers()
    finally:
        cleanup_backend_connections(include_process_resources=True)
