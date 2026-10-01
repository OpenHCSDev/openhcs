"""Public paired-vector declaration reconstruction, not native acceptance."""

from __future__ import annotations

import inspect
import json
from dataclasses import replace

import numpy as np
import pytest

from openhcs.agent.dto.pipeline import FunctionSpecRef, FunctionStepSpec
from openhcs.agent.services.pipeline_authoring_service import PipelineAuthoringService
from openhcs.core.function_patterns import normalize_function_pattern
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.core.artifacts import ImageArtifactType
from openhcs.core.callable_contract import CallableContract
from openhcs.core.memory.decorators import numpy as numpy_function
from openhcs.core.measurement_row_materialization import (
    DataclassMeasurementColumnarRows,
)
from openhcs.core.pipeline.function_contracts import (
    runtime_bound_parameters,
    special_inputs,
)
from openhcs.interop.cellprofiler.setting_names import setting_values
from openhcs.processing.backends.cellprofiler.classification import (
    ClassificationMethod,
    ClassificationResult,
    ClassificationThresholdMethod,
    ClassifiedImageOutput,
    ClassifyObjectsSingleMeasurementModule,
    _ClassificationMeasurement1ValuesRuntimeParameter,
    _ClassificationMeasurement2ValuesRuntimeParameter,
    _ClassificationMeasurementValuesRuntimeParameter,
    _SingleClassifiedImageOutputRuntimeBinding,
    classify_objects_single_measurement,
    classify_objects_two_measurements,
)
from openhcs.processing.backends.lib_registry.registry_service import RegistryService
from tests.unit.agent.test_compile_selector_authoring import SelectedDeclarations
from tests.unit.test_cellprofiler_conditional_analysis_images import (
    _classification_context,
    _contract,
    _module_block,
    _public_function_step_contract,
)
from tests.unit.test_classification_interop_boundaries import _runtime_request


def paired_kwargs():
    return dict(
        select_the_object_to_be_classified="Cells",
        measurement1_feature="AreaShape_Area",
        measurement2_feature="AreaShape_Area",
        threshold1_method=ClassificationThresholdMethod.CUSTOM,
        threshold1_value=100.0,
        threshold2_method=ClassificationThresholdMethod.CUSTOM,
        threshold2_value=100.0,
    )


def test_public_paired_vector_kwargs_reconstruct_original_mode_without_extra_selector():
    contract = _public_function_step_contract(
        ClassifyObjectsSingleMeasurementModule,
        classify_objects_two_measurements,
        paired_kwargs(),
        _classification_context(),
    )
    assert contract.function_name == "classify_objects_two_measurements"
    assert contract.runtime_bound_parameters == (
        "measurement1_values",
        "measurement2_values",
    )


def test_original_parsed_pair_runtime_binds_only_its_declared_signature():
    module = _module_block(
        ClassifyObjectsSingleMeasurementModule,
        (
            (
                "Make each classification decision on how many measurements?",
                "Pair of measurements",
            ),
            ("Select the object to be classified", "Cells"),
            ("Select the first measurement", "AreaShape_Area"),
            ("Select the second measurement", "AreaShape_Area"),
            ("Retain an image of the classified objects?", "No"),
        ),
    )
    contract = _contract(
        ClassifyObjectsSingleMeasurementModule,
        module,
        classify_objects_two_measurements,
        _classification_context(),
    )
    kwargs = {
        name: value
        for name, value in paired_kwargs().items()
        if name != "select_the_object_to_be_classified"
    }
    request = _runtime_request(contract, kwargs)
    bound = ClassifyObjectsSingleMeasurementModule.bind_runtime_inputs(request)
    output, rows = inspect.unwrap(classify_objects_two_measurements)(
        request.current_image, **kwargs, **bound
    )
    assert set(bound) == {"labels", "measurement1_values", "measurement2_values"}
    labels = request.label_payload_for(request.object_inputs[0]).variant_data.labels
    np.testing.assert_array_equal(output, labels)
    assert rows.rows[0].total_objects == 2
    assert json.loads(rows.rows[0].object_classes) == {"1": "low_low", "2": "high_high"}


@pytest.mark.parametrize(
    "keyword",
    (
        "labels",
        "measurement1_values",
        "measurement2_values",
        "classified_image_rule_indices",
        "undeclared_selector",
    ),
)
def test_public_pair_rejects_unknown_and_runtime_owned_kwargs(keyword, monkeypatch):
    function_id, metadata = RegistryService.declared_metadata_for_callable(
        classify_objects_two_measurements
    )
    monkeypatch.setattr(RegistryService, "_metadata_cache", {function_id: metadata})
    monkeypatch.setattr(RegistryService, "_resolved_reference_callables", {})
    author = PipelineAuthoringService(function_catalog=SelectedDeclarations())
    ref = author.create_pipeline(
        steps=(
            FunctionStepSpec(
                "paired",
                "paired",
                (
                    FunctionSpecRef(
                        function_id, {**paired_kwargs(), keyword: "injected"}
                    ),
                ),
            ),
        )
    )
    result = author.validate(ref)
    assert not result.valid
    assert result.errors[0].code == "invalid_function_kwargs"
    assert keyword in result.errors[0].message
    with pytest.raises(ValueError, match="Invalid kwargs"):
        author.render_source(ref)


@pytest.mark.parametrize(
    "parameters",
    (
        (),
        (
            _ClassificationMeasurementValuesRuntimeParameter,
            _ClassificationMeasurement1ValuesRuntimeParameter,
        ),
    ),
)
def test_missing_and_conflicting_mode_declarations_fail_closed(parameters):
    contract = CallableContract.from_callable(classify_objects_two_measurements)
    contract = replace(
        contract,
        metadata=replace(contract.metadata, runtime_bound_parameters=parameters),
    )
    with pytest.raises(ValueError, match="one declared measurement-count mode"):
        ClassificationMethod.from_callable_contract(contract)


class _IndependentPairImageVectorParameter(
    _SingleClassifiedImageOutputRuntimeBinding,
    _ClassificationMeasurement1ValuesRuntimeParameter,
):
    """Independent image capability plus an inherited paired-vector declaration."""

    @classmethod
    def classified_image_output_binding(cls):
        return IndependentPairDeclarationModule.output_image_binding


class IndependentPairDeclarationModule(ClassifyObjectsSingleMeasurementModule):
    module_name = "IndependentPairDeclarationProbe"
    function_name = "independent_pair_declaration_callable"
    function_variants = ()
    aliases = ()

    @classmethod
    def _two_measurement_classified_image_outputs(cls, module):
        return tuple(
            ClassifiedImageOutput(index, name)
            for index, name in enumerate(
                setting_values(module, cls.output_image_setting)
            )
        )


@numpy_function
@special_inputs("labels")
@runtime_bound_parameters(
    _IndependentPairImageVectorParameter,
    _ClassificationMeasurement2ValuesRuntimeParameter,
)
def independent_pair_declaration_callable(
    image,
    labels,
    measurement1_feature="",
    measurement2_feature="",
    measurement1_values=None,
    measurement2_values=None,
    retained_image_name=None,
) -> tuple[np.ndarray, DataclassMeasurementColumnarRows]:
    assert retained_image_name == "IndependentPairImage"
    np.testing.assert_array_equal(measurement1_values, (9.0, 300.0))
    np.testing.assert_array_equal(measurement2_values, (9.0, 300.0))
    return image, ClassificationResult.columnar(
        ClassificationResult.empty(total_objects=2)
    )


def test_new_pair_declaration_reconstructs_and_cooperative_mro_binds_both_capabilities():
    declaration = IndependentPairDeclarationModule
    kwargs = {
        "select_the_object_to_be_classified": "Cells",
        "measurement1_feature": "AreaShape_Area",
        "measurement2_feature": "AreaShape_Area",
        "retained_image_name": "IndependentPairImage",
    }
    contract = _public_function_step_contract(
        declaration,
        independent_pair_declaration_callable,
        kwargs,
        _classification_context(),
    )
    assert contract.function_name == declaration.function_name
    assert contract.artifact_outputs.names_of_artifact_type(ImageArtifactType) == (
        "IndependentPairImage",
    )
    assert (
        ClassificationMethod.TWO_MEASUREMENTS.require_callable(declaration)
        is independent_pair_declaration_callable
    )
    runtime_kwargs = {
        key: kwargs[key] for key in ("measurement1_feature", "measurement2_feature")
    }
    request = _runtime_request(contract, runtime_kwargs)
    bound = declaration.bind_runtime_inputs(request)
    assert set(bound) == {
        "labels",
        "measurement1_values",
        "measurement2_values",
        "retained_image_name",
    }
    image, rows = inspect.unwrap(independent_pair_declaration_callable)(
        request.current_image, **runtime_kwargs, **bound
    )
    np.testing.assert_array_equal(image, request.current_image)
    assert rows.rows[0].total_objects == 2
    mro = _IndependentPairImageVectorParameter.__mro__
    assert mro.index(_SingleClassifiedImageOutputRuntimeBinding) < mro.index(
        _ClassificationMeasurement1ValuesRuntimeParameter
    )
    with pytest.raises(ValueError, match="requires one callable"):
        ClassificationMethod.SINGLE_MEASUREMENT.require_callable(declaration)


@pytest.mark.parametrize("clean", (False, True))
def test_paired_author_validate_render_parse_compile_and_original_runtime(
    clean, monkeypatch
):
    metadata = dict(
        RegistryService.declared_metadata_for_callable(func)
        for func in (
            classify_objects_single_measurement,
            classify_objects_two_measurements,
        )
    )
    monkeypatch.setattr(RegistryService, "_metadata_cache", metadata)
    monkeypatch.setattr(RegistryService, "_resolved_reference_callables", {})
    function_id, _metadata = RegistryService.declared_metadata_for_callable(
        classify_objects_two_measurements
    )
    author = PipelineAuthoringService(function_catalog=SelectedDeclarations())
    ref = author.create_pipeline(
        steps=(
            FunctionStepSpec(
                "paired", "paired", (FunctionSpecRef(function_id, paired_kwargs()),)
            ),
        )
    )
    assert author.validate(ref).valid
    restored = PipelineDocumentAuthority.from_source(
        author.render_source(ref, clean=clean).source
    )
    invocation = next(
        normalize_function_pattern(restored.pipeline_steps[0].func).iter_items()
    )
    contract = _public_function_step_contract(
        ClassifyObjectsSingleMeasurementModule,
        invocation.contract.func,
        invocation.kwargs_dict,
        _classification_context(),
    )
    kwargs = {
        name: value
        for name, value in invocation.kwargs_dict.items()
        if name != "select_the_object_to_be_classified"
    }
    request = _runtime_request(contract, kwargs)
    bound = ClassifyObjectsSingleMeasurementModule.bind_runtime_inputs(request)
    image, rows = inspect.unwrap(classify_objects_two_measurements)(
        request.current_image, **kwargs, **bound
    )
    assert image.shape == (8, 8)
    labels = request.label_payload_for(request.object_inputs[0]).variant_data.labels
    np.testing.assert_array_equal(image, labels)
    assert rows.rows[0].total_objects == 2
    assert json.loads(rows.rows[0].object_classes) == {"1": "low_low", "2": "high_high"}
