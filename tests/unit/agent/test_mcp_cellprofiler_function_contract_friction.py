from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from openhcs.agent.dto.functions import FunctionParameterSource
from openhcs.agent.services.function_catalog_service import FunctionCatalogService
from openhcs.processing.backends.cellprofiler.feature_enhancement import (
    enhance_or_suppress_features,
)
from openhcs.processing.backends.cellprofiler.primary_objects import (
    identify_primary_objects,
)
from openhcs.processing.backends.cellprofiler.skeleton import measure_object_skeleton
from openhcs.processing.backends.cellprofiler.intensity import (
    MeasureObjectIntensityModule,
    measure_object_intensity,
)
from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.interop.cellprofiler.settings_binder import SettingToKeywordBinding
from openhcs.core.artifacts import ObjectLabelsArtifactType


@dataclass(frozen=True)
class _Metadata:
    func: Callable
    tags: tuple[str, ...]
    library: str = "openhcs"

    @property
    def original_name(self) -> str:
        return self.func.__name__

    @property
    def name(self) -> str:
        return self.func.__name__

    @property
    def display_name(self) -> str:
        return self.func.__name__

    @property
    def module(self) -> str:
        return self.func.__module__

    @property
    def doc(self) -> str:
        return self.func.__doc__ or ""

    def get_registry_name(self) -> str:
        return self.library


def _catalog(monkeypatch, function_id: str, func: Callable) -> FunctionCatalogService:
    monkeypatch.setattr(
        FunctionCatalogService,
        "_all_metadata",
        lambda self, **_kwargs: {
            function_id: _Metadata(func=func, tags=("openhcs", "cellprofiler"))
        },
    )
    return FunctionCatalogService()


def test_library_selector_accepts_declaration_owned_backend_tag(monkeypatch):
    catalog = _catalog(
        monkeypatch,
        "openhcs:cellprofiler_identify_primary_objects",
        identify_primary_objects,
    )

    by_registry = catalog.search(library="openhcs")
    by_backend_tag = catalog.search(library="cellprofiler")

    assert by_registry.total == 1
    assert by_backend_tag.total == 1
    assert by_backend_tag.items[0].backend_tags == ("openhcs", "cellprofiler")


def test_function_parameters_project_enum_import_members_and_values(monkeypatch):
    catalog = _catalog(
        monkeypatch,
        "openhcs:cellprofiler_enhance_or_suppress_features",
        enhance_or_suppress_features,
    )

    detail = catalog.get("openhcs:cellprofiler_enhance_or_suppress_features")
    parameters = {parameter.name: parameter for parameter in detail.parameters}
    neurite_method = parameters["neurite_method"]

    assert neurite_method.enum_import_path == (
        "openhcs.processing.backends.cellprofiler.feature_enhancement.NeuriteMethod"
    )
    assert neurite_method.enum_members == ("GRADIENT", "TUBENESS")
    assert neurite_method.enum_values == ("Line structures", "Tubeness")


def test_function_search_indexes_declared_parameter_and_enum_vocabulary(monkeypatch):
    catalog = _catalog(
        monkeypatch,
        "openhcs:cellprofiler_enhance_or_suppress_features",
        enhance_or_suppress_features,
    )

    by_parameter = catalog.search(query="neurite", library="cellprofiler")
    by_enum_value = catalog.search(query="tubeness", library="cellprofiler")

    assert tuple(item.function_id for item in by_parameter.items) == (
        "openhcs:cellprofiler_enhance_or_suppress_features",
    )
    assert tuple(item.function_id for item in by_enum_value.items) == (
        "openhcs:cellprofiler_enhance_or_suppress_features",
    )


def test_cellprofiler_detail_distinguishes_static_and_compiled_artifacts(monkeypatch):
    catalog = _catalog(
        monkeypatch,
        "openhcs:cellprofiler_identify_primary_objects",
        identify_primary_objects,
    )

    detail = catalog.get("openhcs:cellprofiler_identify_primary_objects")

    assert detail.runtime_contract is not None
    runtime_contract = detail.runtime_contract
    assert runtime_contract.artifact_inputs == ()
    assert runtime_contract.artifact_outputs == ()
    assert runtime_contract.cellprofiler_module is not None
    module = runtime_contract.cellprofiler_module
    assert module.exact_artifact_contract_requires_compilation is True
    assert {
        (binding.direction, binding.kind) for binding in module.artifact_bindings
    } >= {
        ("input", "image"),
        ("output", "object_labels"),
    }
    assert runtime_contract.source_binding_rule is not None
    assert "Callable-level artifact arrays can therefore be empty" in (
        runtime_contract.source_binding_rule
    )
    assert runtime_contract.pattern_compatibility_rule is not None
    assert "may intentionally cover only a subset" in (
        runtime_contract.pattern_compatibility_rule
    )


def test_function_detail_classifies_normalized_artifact_fed_parameter(monkeypatch):
    catalog = _catalog(
        monkeypatch,
        "openhcs:cellprofiler_measure_object_skeleton",
        measure_object_skeleton,
    )

    detail = catalog.get("openhcs:cellprofiler_measure_object_skeleton")
    parameters = {parameter.name: parameter for parameter in detail.parameters}

    assert "seed_labels" not in detail.entry.signature
    assert (
        parameters["seed_labels"].supplied_by is FunctionParameterSource.ARTIFACT_INPUT
    )
    assert parameters["seed_labels"].required is False
    assert "do not pass this as a function kwarg" in (
        parameters["seed_labels"].description or ""
    )


def test_catalog_exposes_declared_exact_object_selector_and_authoring_guidance(
    monkeypatch,
):
    catalog = _catalog(
        monkeypatch,
        "openhcs:cellprofiler_measure_object_intensity",
        measure_object_intensity,
    )
    detail = catalog.get("openhcs:cellprofiler_measure_object_intensity")
    contract = detail.runtime_contract
    assert contract is not None
    assert contract.cellprofiler_module is not None
    (selector,) = (
        binding
        for binding in contract.cellprofiler_module.artifact_bindings
        if binding.runtime_parameter_name == "labels"
    )
    owner = MeasureObjectIntensityModule.object_measurement_binding
    assert owner.parameter_name is None
    assert selector.parameter_name == owner.require_parameter_name()
    assert selector.parameter_name == "select_object_sets_to_measure"
    assert selector.repeated is True
    assert contract.source_binding_rule is not None
    assert "one-element tuple selects one producer" in contract.source_binding_rule
    assert "do not pass labels" in contract.source_binding_rule
    parameters = {parameter.name: parameter for parameter in detail.parameters}
    assert parameters["labels"].supplied_by is FunctionParameterSource.ARTIFACT_INPUT


def test_catalog_projects_registered_and_new_binding_declarations_without_a_roster():
    from openhcs.agent.services.function_catalog_service import (
        _cellprofiler_artifact_binding_summary,
    )

    registered = tuple(
        binding
        for module in CellProfilerModule.__registry__.values()
        for binding in module.declared_artifact_bindings()
    )
    assert registered
    new_bindings = (
        SettingToKeywordBinding.input(
            "Select future object cohort",
            ObjectLabelsArtifactType,
            runtime_parameter_name="labels",
            repeated=True,
        ),
        SettingToKeywordBinding.output(
            "Name future object cohort",
            ObjectLabelsArtifactType,
            parameter_name="exact_future_output",
        ),
    )
    for binding in (*registered, *new_bindings):
        summary = _cellprofiler_artifact_binding_summary(binding)
        assert summary.parameter_name == binding.require_parameter_name()
        assert summary.runtime_parameter_name == binding.runtime_parameter_name
        assert summary.repeated is binding.repeated
        assert summary.kind == binding.require_artifact_type().require_value()
