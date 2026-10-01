"""Declaration help crosses the real catalog DTO without running analysis."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Annotated

from pyqt_reactive.services.help_document import HelpDocument
from pyqt_reactive.services.parameter_help_service import docstring_info_for_target

from openhcs.agent.services.function_catalog_service import (
    FunctionCatalogService,
    PARAMETER_DOCUMENTATION_POLICY,
    ParameterDocumentationPolicy,
)
from openhcs.processing.backends.analysis.neurite_outgrowth import (
    MetaXpressCellBodySettings,
    MetaXpressNuclearSettings,
    MetaXpressOutgrowthSettings,
    neurite_outgrowth_metaxpress,
)
from openhcs.serialization.json import to_jsonable


@dataclass(frozen=True)
class TimeControls:
    """Independent time capability."""

    duration: float = 1.0
    """Acquisition duration in seconds."""


@dataclass(frozen=True)
class DistanceControls:
    """Independent distance capability."""

    radius: float = 1.0
    """Search radius in millimeters."""


@dataclass(frozen=True)
class IndependentControls(TimeControls, DistanceControls):
    """Combined controls; field ownership follows the declared MRO."""


def independent_probe(
    image,
    controls: Annotated[IndependentControls | None, "probe"] = None,
    gain: float = 1.0,
):
    """A declaration-only authoring probe.

    Args:
        image: Input image.
        controls: Optional acquisition controls.
        gain: Multiplicative gain; preserves the declared intensity scale.
    """
    raise AssertionError("help must not execute a processing callable")


def test_actual_neurite_parameters_include_original_field_units_and_inherited_help():
    specs = {
        spec.name: spec
        for spec in PARAMETER_DOCUMENTATION_POLICY.parameter_specs(
            neurite_outgrowth_metaxpress
        )
    }
    for name, declaration in (
        ("cell_body", MetaXpressCellBodySettings),
        ("outgrowth", MetaXpressOutgrowthSettings),
        ("nuclear_stain", MetaXpressNuclearSettings),
    ):
        document = HelpDocument.from_docstring_info(
            docstring_info_for_target(declaration)
        )
        assert document.content in specs[name].description
    assert "square micrometers" in specs["cell_body"].description
    assert (
        "Scoring-only total outgrowth threshold in micrometers"
        in specs["outgrowth"].description
    )
    assert "micrometers" in specs["nuclear_stain"].description
    assert (
        "Minimum absolute intensity difference from local background"
        in specs["outgrowth"].description
    )


def test_new_declaration_projects_composed_inherited_fields_and_preserves_plain_help():
    specs = {
        spec.name: spec
        for spec in PARAMETER_DOCUMENTATION_POLICY.parameter_specs(independent_probe)
    }
    description = specs["controls"].description
    assert description.startswith("Optional acquisition controls.")
    assert "Acquisition duration in seconds" in description
    assert "Search radius in millimeters" in description
    assert (
        specs["gain"].description
        == docstring_info_for_target(independent_probe).parameters["gain"]
    )
    assert "FunctionStep input image payload" in specs["image"].description


def test_real_catalog_detail_and_json_project_the_same_parameter_document(monkeypatch):
    from openhcs.processing.backends.lib_registry.openhcs_registry import (
        OpenHCSRegistry,
    )
    from openhcs.processing.backends.lib_registry.unified_registry import (
        FunctionMetadata,
        ProcessingContract,
    )

    metadata = FunctionMetadata(
        name="independent_probe",
        func=independent_probe,
        contract=ProcessingContract.FLEXIBLE,
        registry=OpenHCSRegistry(),
        module=__name__,
        doc=independent_probe.__doc__,
    )
    function_id = metadata.composite_key
    monkeypatch.setattr(FunctionCatalogService, "_metadata", lambda self, key: metadata)
    detail = FunctionCatalogService().get(function_id)
    description = next(
        parameter.description
        for parameter in detail.parameters
        if parameter.name == "controls"
    )
    wire = to_jsonable(detail)
    assert (
        next(
            parameter["description"]
            for parameter in wire["parameters"]
            if parameter["name"] == "controls"
        )
        == description
    )
    assert "Acquisition duration in seconds" in description


class AnnotationAuditPolicy(ParameterDocumentationPolicy):
    """Independent annotation observation capability using the original hook."""

    def __init__(self):
        self.annotations = []
        super().__init__()

    def parameter_description(self, authored_description, supplier, *, annotation):
        self.annotations.append(annotation)
        return super().parameter_description(
            authored_description, supplier, annotation=annotation
        )


class SupplierAuditPolicy(ParameterDocumentationPolicy):
    """Independent runtime-supplier observation through the same cooperative hook."""

    def __init__(self):
        self.suppliers = []
        super().__init__()

    def parameter_description(self, authored_description, supplier, *, annotation):
        self.suppliers.append(supplier)
        return super().parameter_description(
            authored_description, supplier, annotation=annotation
        )


class AuditedPolicy(AnnotationAuditPolicy, SupplierAuditPolicy):
    """Declared MRO composes both capabilities without replacing the algorithm."""


def test_policy_consumer_executes_cooperative_hooks_once_in_declared_mro():
    from pyqt_reactive.services.parameter_help_service import (
        dataclass_type_from_annotation,
    )
    from openhcs.agent.dto.functions import FunctionParameterSource

    policy = AuditedPolicy()
    specs = policy.parameter_specs(independent_probe)
    assert len(policy.annotations) == len(policy.suppliers) == len(specs)
    controls_index = next(
        index for index, spec in enumerate(specs) if spec.name == "controls"
    )
    assert (
        dataclass_type_from_annotation(policy.annotations[controls_index])
        is IndependentControls
    )
    assert policy.suppliers[controls_index] is FunctionParameterSource.AGENT
    assert policy.suppliers[0] is FunctionParameterSource.PRIMARY_INPUT
    assert "Acquisition duration in seconds" in specs[controls_index].description
    assert "Search radius in millimeters" in specs[controls_index].description


def test_registered_neurite_metadata_preserves_declared_field_help(
    monkeypatch, tmp_path
):
    import inspect
    import subprocess
    from python_introspect import UnifiedParameterAnalyzer, signature_analysis_target
    from openhcs.processing.backends.lib_registry.openhcs_registry import (
        OpenHCSRegistry,
    )
    from openhcs.processing.backends.lib_registry.registry_service import (
        RegistryService,
    )
    from openhcs.processing.backends.lib_registry.unified_registry import (
        FunctionMetadata,
    )
    from openhcs.processing.custom_functions.manager import CustomFunctionManager
    from openhcs.processing.func_registry import synchronize_custom_function_sources

    def denied_preparation(*args, **kwargs):
        raise AssertionError(
            "registered-help source check must not launch catalog preparation"
        )

    monkeypatch.setattr(subprocess, "Popen", denied_preparation)
    monkeypatch.setattr(
        RegistryService, "prepare_persistent_catalog", classmethod(denied_preparation)
    )
    monkeypatch.setattr(
        RegistryService, "prepare_in_current_process", classmethod(denied_preparation)
    )
    monkeypatch.setattr(
        CustomFunctionManager,
        "default_storage_directory",
        classmethod(lambda cls: tmp_path / "custom_functions"),
    )
    # Establish the real empty-store source revision before seeding the prepared
    # registry snapshot. Synchronization may invalidate a stale snapshot once.
    synchronize_custom_function_sources()

    registry = OpenHCSRegistry()
    metadata = registry._catalog_metadata_for_function(
        neurite_outgrowth_metaxpress.__name__,
        neurite_outgrowth_metaxpress,
        neurite_outgrowth_metaxpress.__module__,
    )
    assert isinstance(metadata, FunctionMetadata)
    assert (
        metadata.composite_key
        == "openhcs:analysis_neurite_outgrowth_neurite_outgrowth_metaxpress"
    )
    assert metadata.func is not neurite_outgrowth_metaxpress
    monkeypatch.setattr(
        RegistryService, "_metadata_cache", {metadata.composite_key: metadata}
    )
    # Original catalog lookup uses its original registry-owned metadata store.
    detail = FunctionCatalogService().get(
        metadata.composite_key, compact_signature=False, max_doc_chars=20000
    )
    projected = {parameter.name: parameter for parameter in detail.parameters}
    analyzed = UnifiedParameterAnalyzer.analyze(metadata.func)
    target = signature_analysis_target(metadata.func)
    print("Registered callable:", metadata.func, inspect.signature(metadata.func))
    print("Analysis target:", target, inspect.signature(target))
    print(
        "Analyzed annotations:",
        {name: info.param_type for name, info in analyzed.items()},
    )
    assert "square micrometers" in projected["cell_body"].description
    assert (
        "Scoring-only total outgrowth threshold in micrometers"
        in projected["outgrowth"].description
    )
    assert "micrometers" in projected["nuclear_stain"].description
