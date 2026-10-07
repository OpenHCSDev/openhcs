"""Canonical lookup uses original declarations, not a prepared catalog's age."""

from __future__ import annotations

import inspect
from textwrap import dedent

import pytest

import openhcs.processing.custom_functions as custom_functions
from openhcs.core.memory import numpy
from openhcs.processing.backends.lib_registry.openhcs_registry import OpenHCSRegistry
from openhcs.processing.backends.lib_registry.registry_service import RegistryService
from openhcs.processing.backends.lib_registry.unified_registry import (
    FunctionMetadata,
    LibraryRegistryBase,
    ProcessingContract,
)
from openhcs.processing.custom_functions.manager import CustomFunctionManager
from openhcs.processing.custom_functions.runtime_registry import (
    CustomFunctionRuntimeRegistry,
)
from openhcs.processing.custom_functions.validation import ValidationError
from openhcs.processing.func_registry import get_function


@pytest.fixture
def source_owner(monkeypatch, tmp_path):
    store = tmp_path / "custom_functions"
    store.mkdir()
    monkeypatch.setattr(CustomFunctionManager, "default_storage_directory", classmethod(lambda cls: store))
    monkeypatch.setattr(CustomFunctionRuntimeRegistry, "_declarations_by_name", {})
    monkeypatch.setattr(CustomFunctionRuntimeRegistry, "_published_exports", {})
    monkeypatch.setattr(CustomFunctionRuntimeRegistry, "_preparation_outcomes", {})
    monkeypatch.setattr(CustomFunctionRuntimeRegistry, "_preparation_threads", {})
    monkeypatch.setattr(CustomFunctionRuntimeRegistry, "_source_revision", None)
    monkeypatch.setattr(RegistryService, "_metadata_cache", {})
    monkeypatch.setattr(RegistryService, "_resolved_reference_callables", {})
    yield store
    CustomFunctionRuntimeRegistry.clear()


def source(name: str, expression: str = "image") -> str:
    return f"@numpy\ndef {name}(image):\n    return {expression}\n"


def forbid_catalog(monkeypatch) -> None:
    def forbidden(cls, **kwargs):
        pytest.fail("a selected custom source must not prepare the global catalog")
    monkeypatch.setattr(RegistryService, "get_all_functions_with_metadata", classmethod(forbidden))


@pytest.mark.parametrize("cache", [None, {}])
def test_persisted_lookup_loads_only_exact_source_and_reuses_original_owner(source_owner, monkeypatch, cache):
    name = "canonical_selected_source"
    (source_owner / f"{name}.py").write_text(source(name), encoding="utf-8")
    (source_owner / "unrelated_invalid.py").write_text("invalid source !!!", encoding="utf-8")
    monkeypatch.setattr(RegistryService, "_metadata_cache", cache)
    forbid_catalog(monkeypatch)
    function = get_function(f"openhcs:{name}")
    metadata = CustomFunctionRuntimeRegistry.metadata_by_name()[name]
    assert function is metadata.func is vars(custom_functions)[name]
    assert get_function(metadata.composite_key) is function
    assert RegistryService._metadata_cache is cache
    assert tuple(CustomFunctionRuntimeRegistry.metadata_by_name()) == (name,)
    assert metadata.import_identity.import_path == f"openhcs.processing.custom_functions.{name}"


@pytest.mark.parametrize("persist", [False, True])
def test_published_lookup_does_not_reexecute_declaration_or_warm_catalog(source_owner, monkeypatch, persist):
    [function] = CustomFunctionManager().register_from_code(source("canonical_published"), persist=persist)
    monkeypatch.setattr(RegistryService, "_metadata_cache", None)
    monkeypatch.setattr(CustomFunctionManager, "_prepare_source", lambda *a: pytest.fail("reexecuted source"))
    forbid_catalog(monkeypatch)
    assert get_function("openhcs:canonical_published") is function


@pytest.mark.parametrize("mutation", ["source_changed", "source_removed", "export_displaced", "declaration_removed"])
def test_cached_custom_claim_never_rescues_stale_source(source_owner, monkeypatch, mutation):
    manager = CustomFunctionManager()
    name = "canonical_stale"
    manager.register_from_code(source(name))
    metadata = CustomFunctionRuntimeRegistry.metadata_by_name()[name]
    monkeypatch.setattr(RegistryService, "_metadata_cache", {metadata.composite_key: metadata})
    with monkeypatch.context() as mutation_patch:
        if mutation == "source_changed":
            (source_owner / f"{name}.py").write_text(source(name, "image + 1"), encoding="utf-8")
        elif mutation == "source_removed":
            (source_owner / f"{name}.py").unlink()
        elif mutation == "export_displaced":
            mutation_patch.setattr(custom_functions, name, object())
        else:
            manager.delete_custom_function(name)
            mutation_patch.setattr(RegistryService, "_metadata_cache", {metadata.composite_key: metadata})
        with pytest.raises(RuntimeError, match="changed; recompile"):
            get_function(metadata.composite_key)
        assert RegistryService._metadata_cache[metadata.composite_key] is metadata


@pytest.mark.parametrize("name", ["missing_canonical", "bad:name", "_private", "../outside"])
def test_missing_or_noncanonical_source_is_rejected(source_owner, name):
    with pytest.raises(KeyError, match="Unknown canonical function ID"):
        get_function(f"openhcs:{name}")
    assert not tuple(source_owner.iterdir())
    assert not CustomFunctionRuntimeRegistry.metadata_by_name()


def test_filename_declaration_mismatch_is_not_accepted(source_owner):
    (source_owner / "canonical_mismatch.py").write_text(source("other_declaration"), encoding="utf-8")
    with pytest.raises(ValidationError, match="filename and declaration name must match"):
        get_function("openhcs:canonical_mismatch")
    assert not CustomFunctionRuntimeRegistry.metadata_by_name()


def test_public_canonical_source_evaluation_and_render_roundtrip_use_selected_owner(source_owner, monkeypatch):
    from openhcs.core.pipeline_document import PipelineDocumentAuthority
    from openhcs.core.function_reference import FunctionReferenceTransportAuthority

    name = "canonical_roundtrip_source"
    (source_owner / f"{name}.py").write_text(source(name), encoding="utf-8")
    monkeypatch.setattr(RegistryService, "_metadata_cache", None)
    forbid_catalog(monkeypatch)
    document = PipelineDocumentAuthority.from_source(
        "from openhcs.processing.func_registry import get_function\n"
        "from openhcs.core.steps.function_step import FunctionStep\n"
        f"pipeline_steps = [FunctionStep(func=get_function('openhcs:{name}'), name='probe')]\n"
    )
    function = CustomFunctionRuntimeRegistry.metadata_by_name()[name].func
    assert document.pipeline_steps[0].func is function
    assert FunctionReferenceTransportAuthority.function_reference(function).resolve() is function
    rendered = PipelineDocumentAuthority.render(document)
    assert f"from openhcs.processing.custom_functions import {name}" in rendered
    assert "get_function" not in rendered
    restored = PipelineDocumentAuthority.from_source(rendered)
    assert restored.pipeline_steps[0].func is function
    reference = FunctionReferenceTransportAuthority.function_reference(function)
    from openhcs.core.function_reference import ModuleExportRegistryFunctionReference
    assert isinstance(reference, ModuleExportRegistryFunctionReference)
    assert reference.composite_key == f"openhcs:{name}"
    assert reference.resolve() is function
    namespace = {}
    exec(compile(rendered, '<direct-custom-source>', 'exec'), namespace)
    assert namespace['pipeline_steps'][0].func is function


def test_catalog_key_cannot_contradict_original_metadata_identity(source_owner, monkeypatch):
    @numpy
    def independent_identity(image):
        raise AssertionError("lookup must not execute processing")

    metadata = FunctionMetadata(
        name="actual_declared_name", func=independent_identity,
        contract=ProcessingContract.FLEXIBLE, registry=OpenHCSRegistry(),
    )
    monkeypatch.setattr(RegistryService, "_metadata_cache", {"openhcs:wrong_name": metadata})
    with pytest.raises(ValueError, match="contradicts declaration"):
        get_function("openhcs:wrong_name")


def test_cached_native_collision_rejects_ambiguous_current_custom_owner(source_owner, monkeypatch):
    name = "canonical_ambiguous"
    CustomFunctionManager().register_from_code(source(name), persist=False)
    custom = CustomFunctionRuntimeRegistry.metadata_by_name()[name]

    @numpy
    def independent_native(image):
        raise AssertionError("lookup must not execute processing")

    native = FunctionMetadata(
        name=name, func=independent_native, contract=ProcessingContract.FLEXIBLE,
        registry=OpenHCSRegistry(), original_name="independent_native", module=__name__,
    )
    monkeypatch.setattr(RegistryService, "_metadata_cache", {custom.composite_key: native})
    with pytest.raises(ValueError, match="ambiguous owners"):
        get_function(custom.composite_key)


def test_new_nominal_registry_and_independent_capabilities_use_real_cooperative_mro(source_owner):
    events = []

    class TraceClaims:
        @classmethod
        def _canonical_metadata_claims(cls, function_id, **kwargs):
            events.append("trace-enter")
            yield from super()._canonical_metadata_claims(function_id, **kwargs)
            events.append("trace-exit")

    class DeclaredClaims:
        @classmethod
        def _canonical_metadata_claims(cls, function_id, **kwargs):
            events.append("declaration")
            if function_id == cls.probe.composite_key:
                yield cls.probe
            yield from super()._canonical_metadata_claims(function_id, **kwargs)

    class IndependentCanonicalRegistry(TraceClaims, DeclaredClaims, OpenHCSRegistry):
        _registry_name = "independent_canonical_probe"

        def __init__(self):
            LibraryRegistryBase.__init__(self, self._registry_name)

    @numpy
    def independently_declared(image):
        raise AssertionError("canonical resolution must not execute scientific work")

    try:
        registry = IndependentCanonicalRegistry()
        registry_type = type(registry)
        registry_type.probe = FunctionMetadata(
            name="independently_declared", func=independently_declared,
            contract=ProcessingContract.FLEXIBLE, registry=registry,
            original_name="independently_declared", module=__name__,
        )
        assert get_function(registry_type.probe.composite_key) is independently_declared
        assert events == ["trace-enter", "declaration", "trace-exit"]
        assert registry_type.__mro__.index(TraceClaims) < registry_type.__mro__.index(DeclaredClaims)
        assert registry_type.__mro__.index(OpenHCSRegistry) < registry_type.__mro__.index(LibraryRegistryBase)
        events.clear()
        with pytest.raises(KeyError, match="Unknown canonical function ID"):
            get_function(f"{registry.library_name}:missing")
        assert events == ["trace-enter", "declaration", "trace-exit"]
    finally:
        dict.pop(LibraryRegistryBase.__registry__, IndependentCanonicalRegistry._registry_name, None)


def test_shared_consumer_has_no_concrete_owner_dispatch():
    import ast

    for method in (get_function, RegistryService.metadata_for_canonical_key):
        syntax = ast.parse(dedent(inspect.getsource(method)))
        assert not any(isinstance(node, ast.Match) for node in ast.walk(syntax))
        assert not any(
            isinstance(node, ast.Name) and node.id in {"OpenHCSRegistry", "CustomFunctionRuntimeRegistry"}
            for node in ast.walk(syntax)
        )
    assert "get_all_functions_with_metadata" not in inspect.getsource(get_function)
