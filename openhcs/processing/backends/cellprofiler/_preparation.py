"""Declared persistent kernel work shared by registry and callable preparation."""

from __future__ import annotations

from openhcs.core.processing_preparation import RegisteredNumbaKernelPreparation
from openhcs.processing.backends.cellprofiler.perf_fixtures import capture_enabled


class CellProfilerCallableKernelPreparation(RegisteredNumbaKernelPreparation):
    """Keep CellProfiler fixture capture in the parent processing hook."""

    @classmethod
    def can_prepare_in_child(cls) -> bool:
        """Keep opt-in fixture writes out of cache-only children."""
        if capture_enabled():
            return False
        return super().can_prepare_in_child()

    @classmethod
    def prepare_registered_family(cls) -> None:
        if capture_enabled():
            return
        super().prepare_registered_family()
