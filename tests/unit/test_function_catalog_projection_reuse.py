"""One changed custom function costs one projection; the rest are reused."""

import pytest

# Activate the source owner's declared externals before dependency imports.
import openhcs  # noqa: F401
import openhcs.processing.custom_functions.manager as manager_module
from openhcs.agent.services.function_catalog_service import FunctionCatalogService
from openhcs.core.processing_contracts import FlexibleContract
from openhcs.processing.backends.lib_registry.openhcs_registry import OpenHCSRegistry
from openhcs.processing.backends.lib_registry.registry_service import RegistryService
from openhcs.processing.backends.lib_registry.unified_registry import FunctionMetadata
from openhcs.processing.custom_functions.manager import CustomFunctionManager
from openhcs.processing.custom_functions.runtime_registry import (
    CustomFunctionRuntimeRegistry,
)

LIBRARY_FUNCTION_NAMES = ("library_first", "library_second", "library_third")


def library_function(image, gain: float = 1.0):
    """A library function that is only described, never called."""
    raise AssertionError("projecting a function must not call it")


def _source(name: str, expression: str = "image") -> str:
    return f"@numpy\ndef {name}(image):\n    return {expression}\n"


def _loaded_library() -> OpenHCSRegistry:
    """A registry that has loaded a three-function library, as from its disk cache."""
    registry = OpenHCSRegistry()
    registry._prepare_cached_function_inventory()
    registry._remember_function_metadata(
        {
            name: FunctionMetadata(
                name=name,
                func=library_function,
                contract=FlexibleContract,
                registry=registry,
                module=__name__,
                doc=library_function.__doc__,
            )
            for name in LIBRARY_FUNCTION_NAMES
        }
    )
    return registry


@pytest.fixture
def projected_catalogue(monkeypatch, tmp_path):
    storage_dir = tmp_path / "custom_functions"
    storage_dir.mkdir()
    monkeypatch.setattr(
        manager_module, "get_data_file_path", lambda _name, *, create=True: storage_dir
    )
    for name in (
        "_declarations_by_name", "_published_exports",
        "_preparation_outcomes", "_preparation_threads",
    ):
        monkeypatch.setattr(CustomFunctionRuntimeRegistry, name, {})
    monkeypatch.setattr(CustomFunctionRuntimeRegistry, "_source_revision", None)
    # Discovering the libraries again loads them again: new metadata objects.
    monkeypatch.setattr(
        RegistryService,
        "_discover_available_registry_instances",
        classmethod(lambda cls: [_loaded_library()]),
    )
    monkeypatch.setattr(RegistryService, "_registry_instances", None)
    monkeypatch.setattr(RegistryService, "_metadata_cache", None)
    monkeypatch.setattr(RegistryService, "_resolved_reference_callables", {})

    service = FunctionCatalogService()
    projected: list[str] = []
    project_entry = service._entry

    def counted_entry(function_id, *args, **kwargs):
        projected.append(function_id)
        return project_entry(function_id, *args, **kwargs)

    monkeypatch.setattr(service, "_entry", counted_entry)
    service.prepare_projections()
    assert sorted(projected) == [f"openhcs:{name}" for name in LIBRARY_FUNCTION_NAMES]
    projected.clear()
    yield service, CustomFunctionManager(), projected
    CustomFunctionRuntimeRegistry.clear()


def _projections_by_id(service: FunctionCatalogService):
    service.prepare_projections()
    assert service.projections_current()
    return {
        projection.entry.function_id: projection
        for projection in service._projections
    }


def test_one_changed_custom_function_projects_one_entry(projected_catalogue):
    service, manager, projected = projected_catalogue
    library = _projections_by_id(service)
    assert projected == []

    manager.register_from_code(_source("reuse_probe"), persist=True)
    registered = _projections_by_id(service)
    assert projected == ["openhcs:reuse_probe"]
    assert registered.keys() == library.keys() | {"openhcs:reuse_probe"}
    assert all(registered[function_id] is library[function_id] for function_id in library)

    projected.clear()
    manager.register_from_code(_source("reuse_neighbour"), persist=True)
    with_neighbour = _projections_by_id(service)
    assert projected == ["openhcs:reuse_neighbour"]
    assert all(
        with_neighbour[function_id] is registered[function_id]
        for function_id in registered
    )

    projected.clear()
    manager.update_custom_function("reuse_probe", _source("reuse_probe", "image + 1"))
    edited = _projections_by_id(service)
    assert projected == ["openhcs:reuse_probe"]
    assert edited.keys() == with_neighbour.keys()
    assert edited["openhcs:reuse_probe"] is not with_neighbour["openhcs:reuse_probe"]
    assert all(
        edited[function_id] is with_neighbour[function_id]
        for function_id in with_neighbour
        if function_id != "openhcs:reuse_probe"
    )

    projected.clear()
    assert manager.delete_custom_function("reuse_probe")
    deleted = _projections_by_id(service)
    assert projected == []
    assert deleted.keys() == library.keys() | {"openhcs:reuse_neighbour"}
    assert all(deleted[function_id] is edited[function_id] for function_id in deleted)
    assert "reuse_probe" not in {entry.name for entry in service.catalog().items}
