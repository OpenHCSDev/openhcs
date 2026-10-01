"""Declaration help crosses the real catalog DTO without running analysis."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Annotated

from pyqt_reactive.services.help_document import HelpDocument
from pyqt_reactive.services.parameter_help_service import docstring_info_for_target

from openhcs.agent.services.function_catalog_service import (
    FunctionCatalogService,
    PARAMETER_DOCUMENTATION_POLICY,
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


def independent_probe(image, controls: Annotated[IndependentControls | None, "probe"] = None,
                      gain: float = 1.0):
    """A declaration-only authoring probe.

    Args:
        image: Input image.
        controls: Optional acquisition controls.
        gain: Multiplicative gain; preserves the declared intensity scale.
    """
    raise AssertionError("help must not execute a processing callable")


def test_actual_neurite_parameters_include_original_field_units_and_inherited_help():
    specs = {spec.name: spec for spec in PARAMETER_DOCUMENTATION_POLICY.parameter_specs(
        neurite_outgrowth_metaxpress
    )}
    for name, declaration in (
        ("cell_body", MetaXpressCellBodySettings),
        ("outgrowth", MetaXpressOutgrowthSettings),
        ("nuclear_stain", MetaXpressNuclearSettings),
    ):
        document = HelpDocument.from_docstring_info(docstring_info_for_target(declaration))
        assert document.content in specs[name].description
    assert "square micrometers" in specs["cell_body"].description
    assert "Scoring-only total outgrowth threshold in micrometers" in specs["outgrowth"].description
    assert "micrometers" in specs["nuclear_stain"].description
    assert "Minimum absolute intensity difference from local background" in specs["outgrowth"].description


def test_new_declaration_projects_composed_inherited_fields_and_preserves_plain_help():
    specs = {spec.name: spec for spec in PARAMETER_DOCUMENTATION_POLICY.parameter_specs(
        independent_probe
    )}
    description = specs["controls"].description
    assert description.startswith("Optional acquisition controls.")
    assert "Acquisition duration in seconds" in description
    assert "Search radius in millimeters" in description
    assert specs["gain"].description == docstring_info_for_target(independent_probe).parameters["gain"]
    assert "FunctionStep input image payload" in specs["image"].description


def test_real_catalog_detail_and_json_project_the_same_parameter_document(monkeypatch):
    from openhcs.processing.backends.lib_registry.openhcs_registry import OpenHCSRegistry
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
    description = next(parameter.description for parameter in detail.parameters if parameter.name == "controls")
    wire = to_jsonable(detail)
    assert next(parameter["description"] for parameter in wire["parameters"] if parameter["name"] == "controls") == description
    assert "Acquisition duration in seconds" in description
