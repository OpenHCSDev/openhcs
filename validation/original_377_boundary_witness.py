"""Original source-owner regressions; no remote/runtime/scientific execution."""

import pytest

from openhcs.agent.dto.knowledge import KnowledgeBaseDocumentRequest
from openhcs.agent.services.knowledge_base_service import KnowledgeBaseService
from openhcs.core.memory import numpy
from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.processing.backends.lib_registry.registry_service import RegistryService
from openhcs.processing.custom_functions.runtime_registry import (
    CustomFunctionLifetime,
    CustomFunctionRuntimeRegistry,
    project_custom_function,
)
from openhcs.processing.func_registry import get_function


def test_selected_source_lookup_does_not_discover_unrelated_declarations(monkeypatch):
    registry = CellProfilerModule.__registry__
    original_discover = registry._discover

    def forbid_unrelated_discovery():
        if not registry._discovered:
            raise AssertionError("Selected source requested complete backend discovery")
        return original_discover()

    monkeypatch.setattr(registry, "_discover", forbid_unrelated_discovery)
    document = KnowledgeBaseService().get_document(
        KnowledgeBaseDocumentRequest.from_fields(
            document_id="openhcs_official30_benchmark_recipes",
            section_id="cp-tutorial-pixel-based-classification-openhcs-python",
            max_chars=50000,
        )
    )
    assert not document.errors, document.errors
    assert "pipeline_steps" in document.content


def test_canonical_custom_lookup_uses_published_source_owner(monkeypatch):
    # An independent custom declaration: no fixture or scientific callable runs.
    @numpy
    def independent_knowledge_source_probe(image):
        raise AssertionError("lookup must never execute scientific work")

    monkeypatch.setattr(RegistryService, "_metadata_cache", {})
    metadata = project_custom_function(independent_knowledge_source_probe)
    CustomFunctionRuntimeRegistry.publish(metadata, CustomFunctionLifetime.EPHEMERAL)
    try:
        assert get_function(metadata.composite_key) is metadata.func
        with pytest.raises(KeyError, match="Unknown canonical function ID"):
            get_function("openhcs:unknown_knowledge_probe")
    finally:
        CustomFunctionRuntimeRegistry.remove(metadata.original_name)
