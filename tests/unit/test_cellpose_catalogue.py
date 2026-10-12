"""The derived Cellpose functions as the catalogue, workers, agents and code see them."""

import inspect

import pytest

pytest.importorskip("cellpose", reason="Cellpose is an optional dependency")

from openhcs.agent.services.function_catalog_service import (  # noqa: E402
    FunctionCatalogService,
)
from openhcs.core.function_reference import (  # noqa: E402
    FunctionReferenceTransportAuthority,
)
from openhcs.core.function_step_document import FunctionStepDocumentCodec  # noqa: E402
from openhcs.core.steps.function_step import FunctionStep  # noqa: E402
from openhcs.processing.backends.lib_registry.cellpose_registry import (  # noqa: E402
    CellposeRegistry,
)
from openhcs.processing.backends.lib_registry.derived import (  # noqa: E402
    cellpose as derived,
)
from openhcs.processing.backends.lib_registry.registry_service import (  # noqa: E402
    RegistryService,
)
from openhcs.utils.environment import OpenHCSProcessEnvironment  # noqa: E402

NAMES = sorted(derived.library.functions)


@pytest.fixture
def catalogue(monkeypatch):
    """A process whose loaded catalogue holds the Cellpose functions."""

    functions = {
        metadata.composite_key: metadata
        for metadata in CellposeRegistry().discover_functions().values()
    }
    monkeypatch.setattr(RegistryService, "_metadata_cache", functions)
    monkeypatch.setattr(RegistryService, "_resolved_reference_callables", {})
    return functions


def test_registry_is_in_the_catalogue_unless_the_process_is_cpu_only(monkeypatch):
    monkeypatch.setattr(RegistryService, "_registry_instances", None)
    monkeypatch.delenv(OpenHCSProcessEnvironment.cpu_only_key, raising=False)
    names = {r.library_name for r in RegistryService._available_registry_instances()}
    assert "cellpose" in names

    monkeypatch.setattr(RegistryService, "_registry_instances", None)
    monkeypatch.setenv(OpenHCSProcessEnvironment.cpu_only_key, "1")
    names = {r.library_name for r in RegistryService._available_registry_instances()}
    assert "cellpose" not in names
    assert not CellposeRegistry.supports_cpu_only()


def test_functions_survive_a_cache_save_and_reload(tmp_path):
    def registry() -> CellposeRegistry:
        instance = CellposeRegistry()
        instance._cache_path = tmp_path / "cellpose_function_metadata.json"
        return instance

    discovered = registry().load_or_discover_functions()
    reloaded = registry().load_cached_functions()
    assert sorted(discovered) == sorted(reloaded) == NAMES
    for name in NAMES:
        assert reloaded[name].composite_key == f"cellpose:{name}"
        assert reloaded[name].func is discovered[name].func
        assert inspect.unwrap(reloaded[name].func) is inspect.unwrap(
            getattr(derived, name)
        )
        assert reloaded[name].doc == discovered[name].doc


@pytest.mark.parametrize("name", NAMES)
def test_a_function_reference_resolves_the_way_a_worker_resolves_it(
    name, catalogue, monkeypatch
):
    function = catalogue[f"cellpose:{name}"].func
    reference = FunctionReferenceTransportAuthority.function_reference(function)
    assert reference.composite_key == f"cellpose:{name}"
    assert reference.resolve() is function
    # A worker has no loaded catalogue: it imports the module and asks the registry.
    monkeypatch.setattr(RegistryService, "_metadata_cache", None)
    monkeypatch.setattr(RegistryService, "_resolved_reference_callables", {})
    assert reference.resolve() is function


@pytest.mark.parametrize("name", NAMES)
def test_agent_catalogue_lists_every_control_with_type_default_and_description(
    name, catalogue, monkeypatch
):
    monkeypatch.setattr(
        FunctionCatalogService, "_all_metadata", lambda self, **kwargs: catalogue
    )
    detail = FunctionCatalogService().get(f"cellpose:{name}", max_doc_chars=None)
    described = {parameter.name: parameter for parameter in detail.parameters}
    controls = derived.library._declared[name][0].controls
    assert controls
    for control in controls:
        parameter = described[control.name]
        assert parameter.annotation and "Any" not in parameter.annotation
        assert parameter.default_repr in (repr(control.default), str(control.default))
        assert not parameter.required
        if control.text:
            assert control.text.startswith((parameter.description or "\0")[:40])
    models = (
        derived.RestorationModel if name == "restore" else derived.SegmentationModel
    )
    assert list(described["model_type"].enum_values) == [m.value for m in models]


def test_generated_pipeline_code_executes_back_to_an_equal_step(catalogue):
    kwargs = {
        "model_type": derived.SegmentationModel.NUCLEI,
        "normalize": derived.NormalizeOptions(percentile=(2.0, 98.0), norm3D=False),
        "diameter": 12.0,
    }
    step = FunctionStep(func=(catalogue["cellpose:segment"].func, kwargs), name="segment")
    source = FunctionStepDocumentCodec.render(
        FunctionStepDocumentCodec.from_value(step), clean_mode=True
    )
    assert "SegmentationModel.NUCLEI" in source and "NormalizeOptions(" in source
    rebuilt = FunctionStepDocumentCodec.from_source(source).step
    assert rebuilt.func[0] is catalogue["cellpose:segment"].func
    assert rebuilt.func[1] == kwargs
    assert rebuilt.name == step.name
