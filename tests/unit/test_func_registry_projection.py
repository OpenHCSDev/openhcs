"""Exact reconciliation tests for generated function import projections."""

from __future__ import annotations

import sys
from types import ModuleType, SimpleNamespace

import pytest

import openhcs.processing.func_registry as func_registry


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
