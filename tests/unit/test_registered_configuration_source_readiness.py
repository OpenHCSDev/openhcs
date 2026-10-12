"""Configuration source preparation precedes registry readiness."""

from dataclasses import dataclass, field
from types import SimpleNamespace

import objectstate.lazy_factory as lazy_factory
from python_introspect import SignatureAnalyzer

from openhcs.processing.backends.lib_registry.registry_service import RegistryService


def test_registry_prepares_current_configuration_declarations_before_ready(monkeypatch):
    events = []
    factories = []

    def default_value():
        factories.append("evaluated")
        return 3

    @dataclass
    class PublicConfig:
        value: int = field(default_factory=default_value)

    @dataclass
    class LazyConfig:
        value: int | None = None

    @dataclass
    class LaterPublicConfig:
        value: int = field(default_factory=default_value)

    @dataclass
    class LaterLazyConfig:
        value: int | None = None

    def raw(image):
        return image

    metadata = {"raw": SimpleNamespace(func=raw)}
    monkeypatch.setattr(RegistryService, "_metadata_cache", metadata)
    monkeypatch.setattr(lazy_factory, "_lazy_type_registry", {})
    monkeypatch.setattr(lazy_factory, "_base_to_lazy_registry", {})
    # Record each declaration the preparation pass actually prepares.
    original = SignatureAnalyzer._extract_inline_field_docs

    def declaration(config_type):
        events.append(config_type)
        return original(config_type)

    monkeypatch.setattr(SignatureAnalyzer, "_extract_inline_field_docs", declaration)
    # The registry admits types that are not dataclasses; readiness filters them.
    lazy_factory.register_lazy_type_mapping(dict, list)
    lazy_factory.register_lazy_type_mapping(LazyConfig, PublicConfig)
    assert RegistryService.prepare_in_current_process(status_callback=events.append) is metadata
    assert factories == []
    first_ready = next(i for i, item in enumerate(events) if isinstance(item, str) and "catalog ready" in item)
    assert events.index(LazyConfig) < first_ready
    assert events.index(PublicConfig) < first_ready
    assert LaterPublicConfig not in events and dict not in events and list not in events
    events.clear()
    # An already loaded callable catalog must not freeze the configuration roster.
    lazy_factory.register_lazy_type_mapping(LaterLazyConfig, LaterPublicConfig)
    RegistryService.prepare_in_current_process(status_callback=events.append)
    second_ready = next(i for i, item in enumerate(events) if isinstance(item, str) and "catalog ready" in item)
    for config_type in (LazyConfig, PublicConfig, LaterLazyConfig, LaterPublicConfig):
        assert events.count(config_type) == 1
        assert events.index(config_type) < second_ready
    assert factories == []
