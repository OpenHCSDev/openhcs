"""Pytest's process-wide Fiji policy, independent of disposable fixture caches."""

import os
from collections.abc import MutableMapping

from polystore.imagej_distribution import (
    FijiArchiveDistribution,
    ImageJArchiveDownloadPolicy,
)


def configure_fiji_test_environment(
    environment: MutableMapping[str, str] | None = None,
) -> None:
    """Pin existing bundle storage and deny implicit provisioning in tests.

    Explicit PolyStore settings remain authoritative, including an intentional
    download opt-in for provisioning. Children inherit the same two selectors.
    No bundle is materialized and no JVM is started here.
    """
    values = os.environ if environment is None else environment
    root = FijiArchiveDistribution.cache_root_from_environment(values)
    if root is None:
        # Default path policy belongs to the distribution, not to this harness.
        root = FijiArchiveDistribution.default_cache_root()
    values[FijiArchiveDistribution.cache_root_environment_key] = str(root)
    values.setdefault(ImageJArchiveDownloadPolicy.allow_download_environment_key, "false")
    ImageJArchiveDownloadPolicy.from_environment(values)
