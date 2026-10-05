"""Exact reconciliation tests for generated function import projections."""

from __future__ import annotations

import sys
from types import ModuleType, SimpleNamespace

import pytest

import openhcs.processing.func_registry as func_registry
from openhcs.core.memory import numpy
from openhcs.processing.backends.lib_registry.registry_service import RegistryService
from openhcs.processing.backends.lib_registry.openhcs_registry import OpenHCSRegistry
from openhcs.processing.backends.lib_registry.unified_registry import FunctionMetadata, ProcessingContract


class _ExternalProjectionOwner:
    def public_projection_module(self, metadata):
        return metadata.public_module


@pytest.mark.parametrize(
    ("source", "expected"),
    (
        ("from openhcs.core.config import PipelineConfig", False),
        ("from openhcs.processing.backends.cellprofiler.crop import crop", False),
        ("from openhcs.skimage.filters import gaussian", True),
        ("from openhcs import skimage", True),
        ("importlib.import_module('openhcs.skimage.filters')", True),
        ("importlib.import_module(module_name)", True),
    ),
)
def test_pipeline_source_requires_only_missing_virtual_import_projection(
    source: str, expected: bool
) -> None:
    assert func_registry.pipeline_source_requires_import_projection(source) is expected


def test_partial_virtual_module_does_not_prove_projection_complete(monkeypatch) -> None:
    monkeypatch.setitem(
        sys.modules, "openhcs.codex_virtual", ModuleType("openhcs.codex_virtual")
    )

    assert func_registry.pipeline_source_requires_import_projection(
        "from openhcs.codex_virtual.filters import noop"
    )


def test_external_projection_removes_stale_exports_and_modules(monkeypatch) -> None:
    module_name = "openhcs.codex_external.filters"

    def transient_filter(image):
        return image

    metadata = SimpleNamespace(
        func=transient_filter,
        registry=_ExternalProjectionOwner(),
        public_module=module_name,
    )
    monkeypatch.setattr(func_registry, "_external_projection_exports", {})
    monkeypatch.setattr(func_registry, "_external_projection_modules", set())

    func_registry._create_external_virtual_modules({"external:filter": metadata})
    assert sys.modules[module_name].transient_filter is transient_filter

    func_registry._create_external_virtual_modules({})
    assert module_name not in sys.modules
    assert "openhcs.codex_external" not in sys.modules


def test_legacy_name_lookup_fails_with_canonical_candidates(monkeypatch) -> None:
    @numpy
    def first_crop(image):
        return image

    @numpy
    def second_crop(image):
        return image

    metadata = {
        "openhcs:numpy_crop": FunctionMetadata(
            name="numpy_crop", func=first_crop, original_name="crop",
            registry=OpenHCSRegistry(), contract=ProcessingContract.FLEXIBLE,
        ),
        "openhcs:cellprofiler_crop": FunctionMetadata(
            name="cellprofiler_crop", func=second_crop, original_name="crop",
            registry=OpenHCSRegistry(), contract=ProcessingContract.FLEXIBLE,
        ),
    }
    monkeypatch.setattr(
        RegistryService,
        "get_all_functions_with_metadata",
        classmethod(lambda cls: metadata),
    )

    with pytest.raises(LookupError, match="canonical function IDs"):
        func_registry.get_function_by_name("crop", "numpy")
    assert func_registry.get_function("openhcs:numpy_crop") is first_crop
