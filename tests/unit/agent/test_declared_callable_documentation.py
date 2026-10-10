"""Catalog prose follows semantic declarations, not copied runtime-wrapper docs."""

from __future__ import annotations

import ast
import inspect
from dataclasses import dataclass

import numpy as np
import pytest

from openhcs.agent.dto.functions import FunctionParameterSource
from openhcs.agent.services.function_catalog_service import (
    FunctionCatalogService,
    PARAMETER_DOCUMENTATION_POLICY,
)
from openhcs.core.callable_contract import CallableContract, callable_request
from openhcs.core.memory import numpy as numpy_contract
from openhcs.processing.backends.lib_registry.openhcs_registry import OpenHCSRegistry
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.processing.backends.processors.numpy_processor import (
    non_local_means_denoise_planes,
)


def _catalog(monkeypatch, declaration):
    metadata = OpenHCSRegistry.metadata_for_declared_callable(declaration)
    assert metadata is not None
    monkeypatch.setattr(
        FunctionCatalogService,
        "_all_metadata",
        lambda self, **kwargs: {metadata.composite_key: metadata},
    )
    return FunctionCatalogService(), metadata


def test_installed_witness_declaration_doc_and_parameter_contract_agree(monkeypatch):
    catalog, metadata = _catalog(monkeypatch, non_local_means_denoise_planes)
    # The actual dependency still generates this valid-for-ArrayBridge text.
    assert "Additional Parameters" in inspect.getdoc(metadata.func)
    detail = catalog.get(metadata.composite_key, max_doc_chars=None)
    raw = CallableContract.from_callable(metadata.func).resolve_raw_runtime_callable()
    assert detail.doc == inspect.getdoc(raw)
    assert "Added by the numpy memory decorator" not in detail.doc
    assert "slice_by_slice" not in {parameter.name for parameter in detail.parameters}
    assert "preserve_range" in {parameter.name for parameter in detail.parameters}
    assert catalog.search(query="contamination").total == 0
    assert catalog.search(query="independent grayscale planes").total == 1


@pytest.mark.parametrize("contract", (ProcessingContract.PURE_2D, ProcessingContract.PURE_3D))
def test_new_declaration_preserves_authored_prose_without_consumer_edits(monkeypatch, contract):
    @numpy_contract(contract=contract)
    def independent_doc_probe(image: np.ndarray, *, offset: float = 0.75) -> np.ndarray:
        """Authored plane/volume operation.

        Additional Parameters is an authored heading, not a generated marker.
        A discussion of slice_by_slice is legitimate prose and must survive.

        Args:
            offset: Declared intensity offset in original image units.

        Returns:
            Original geometry with an intensity offset.
        """
        return image + offset

    catalog, metadata = _catalog(monkeypatch, independent_doc_probe)
    detail = catalog.get(metadata.composite_key, max_doc_chars=None)
    assert detail.doc == inspect.getdoc(inspect.unwrap(independent_doc_probe))
    assert "Additional Parameters is an authored heading" in detail.doc
    assert "discussion of slice_by_slice" in detail.doc
    assert "slice_by_slice" not in {parameter.name for parameter in detail.parameters}
    offset = next(parameter for parameter in detail.parameters if parameter.name == "offset")
    assert offset.default_repr == "0.75"
    assert offset.supplied_by is FunctionParameterSource.AGENT
    assert offset.description == "Declared intensity offset in original image units."
    assert catalog.search(query="original image units").total == 1


def test_flexible_controls_remain_typed_and_existing_mro_behavior_is_unchanged(monkeypatch):
    seen = []

    @numpy_contract
    def independent_flexible_doc_probe(image: np.ndarray, *, offset: float = 0.5) -> np.ndarray:
        """Apply an offset with declaration-owned dimensional selection."""
        seen.append(image.shape)
        return image + offset

    catalog, metadata = _catalog(monkeypatch, independent_flexible_doc_probe)
    detail = catalog.get(metadata.composite_key, max_doc_chars=None)
    assert detail.doc == inspect.getdoc(inspect.unwrap(independent_flexible_doc_probe))
    parameters = {parameter.name: parameter for parameter in detail.parameters}
    assert parameters["slice_by_slice"].default_repr == "False"
    assert "Process 3D arrays slice-by-slice" in parameters["slice_by_slice"].description
    assert parameters["dtype_config"].supplied_by is FunctionParameterSource.RUNTIME_PARAMETER
    pixels = np.zeros((2, 4, 6))
    result = metadata.func(pixels, slice_by_slice=True)
    assert seen == [(4, 6), (4, 6)]
    np.testing.assert_array_equal(result.data, pixels + 0.5)
    seen.clear()
    result = metadata.func(pixels, slice_by_slice=False)
    assert seen == [(2, 4, 6)]
    np.testing.assert_array_equal(result.data, pixels + 0.5)


@dataclass(frozen=True)
class IndependentDocRequest:
    image: object
    offset: float = 0.5


def test_nominal_request_boundary_is_not_unwrapped_to_private_implementation(monkeypatch):
    @callable_request(IndependentDocRequest)
    def implementation(request: IndependentDocRequest):
        """Private implementation prose."""
        return request.image

    implementation.__doc__ = "Public request-binding declaration prose."
    declaration = numpy_contract(contract=ProcessingContract.PURE_2D)(implementation)
    catalog, metadata = _catalog(monkeypatch, declaration)
    detail = catalog.get(metadata.composite_key, max_doc_chars=None)
    assert detail.doc == "Public request-binding declaration prose."
    assert "offset" in {parameter.name for parameter in detail.parameters}
    assert "request" not in {parameter.name for parameter in detail.parameters}


def test_no_doc_metadata_and_empty_metadata_remain_external_optional_contracts():
    def no_doc(image):
        return image

    policy = PARAMETER_DOCUMENTATION_POLICY
    assert policy.detail_doc(no_doc, None) is None
    assert policy.detail_doc(no_doc, "   ") is None
    assert policy.detail_doc(no_doc, "External metadata documentation.") == "External metadata documentation."


def test_cellprofiler_setting_help_remains_on_final_typed_parameter_projection(monkeypatch):
    from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
    from openhcs.processing.backends.cellprofiler.classification import classify_objects_single_measurement

    module = CellProfilerModule.for_callable_contract(CallableContract.from_callable(classify_objects_single_measurement))
    assert module is not None
    implementation = module.require_callable()
    catalog, metadata = _catalog(monkeypatch, implementation)
    detail = catalog.get(metadata.composite_key, max_doc_chars=None)
    parameters = {parameter.name: parameter for parameter in detail.parameters}
    # These selectors have declaration-generated help, absent from authored prose.
    for binding in module.declared_setting_bindings():
        name = binding.require_parameter_name()
        if name in parameters:
            assert parameters[name].description
    assert "measurement_feature" in parameters
    assert parameters["measurement_feature"].description
    assert "Added by the numpy memory decorator" not in detail.doc


def test_doc_projection_has_no_leaf_control_dispatch_or_text_surgery():
    tree = ast.parse(inspect.getsource(type(PARAMETER_DOCUMENTATION_POLICY)))
    literals = {node.value for node in ast.walk(tree) if isinstance(node, ast.Constant) and isinstance(node.value, str)}
    assert {"slice_by_slice", "PURE_2D", "PURE_3D", "FLEXIBLE"}.isdisjoint(literals)
    assert "resolve_raw_runtime_callable" in inspect.getsource(type(PARAMETER_DOCUMENTATION_POLICY).detail_doc)
