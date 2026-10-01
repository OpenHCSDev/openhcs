"""Public paired-vector declaration reconstruction, not native acceptance."""

from __future__ import annotations

import inspect
import json
import ast
import textwrap
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
from openhcs.interop.cellprofiler.parser import ModuleSetting
from openhcs.interop.cellprofiler.settings_binder import (
    SettingsBinder,
    coerce_cellprofiler_enum,
)
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
    _ClassificationMethodBehavior,
    _TwoMeasurementClassificationMethodBehavior,
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


@pytest.mark.parametrize(
    "projection",
    (
        "bind_settings",
        "classified_image_outputs",
        "finalize_module_blocks",
    ),
)
def test_original_mode_projections_have_no_case_dispatch(projection):
    """Seal the three exact IMPL-2/IMPL-5 sites, including subthreshold switches."""
    tree = ast.parse(
        textwrap.dedent(inspect.getsource(getattr(ClassificationMethod, projection)))
    )
    forbidden = tuple(
        node
        for node in ast.walk(tree)
        if isinstance(node, (ast.If, ast.IfExp, ast.Match, ast.Compare, ast.Dict))
    )
    assert not forbidden, (
        f"{projection} still decides case behavior: {[type(node).__name__ for node in forbidden]}"
    )
    member_names = frozenset(ClassificationMethod.__members__)
    assert not any(
        isinstance(node, ast.Attribute) and node.attr in member_names
        for node in ast.walk(tree)
    )
    assert not any(
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id in ("getattr", "hasattr", "isinstance", "type")
        for node in ast.walk(tree)
    )


class _IndependentModeProjectionCapability:
    """A real independent capability contributing to every mode projection."""

    def bind_settings(self, module_type, module, binder):
        return {
            **super().bind_settings(module_type, module, binder),
            "independent_mode": True,
        }

    def classified_image_outputs(self, module_type, module):
        return tuple(
            replace(output, rule_index=output.rule_index + 7)
            for output in super().classified_image_outputs(module_type, module)
        )

    def finalize_mode_blocks(self, module_type, blocks, invocation):
        inherited = super().finalize_mode_blocks(module_type, blocks, invocation)
        # The shared original enum template must run before this case-owned tail.
        assert all(
            setting_values(block, module_type.classification_decision_count_setting)
            == ("Independent measurement mode",)
            for block in inherited
        )
        return tuple(
            replace(
                block,
                setting_records=[
                    *block.iter_settings(),
                    ModuleSetting("Independent tail", "complete"),
                ],
            )
            for block in inherited
        )


class _IndependentModeBehavior(
    _IndependentModeProjectionCapability,
    _TwoMeasurementClassificationMethodBehavior,
):
    """A new case is only its capability composition and member declaration."""


def test_new_original_mode_member_owns_all_projections_and_cooperative_tail():
    # Python Enum preserves its original __new__ as _new_member_. Construct a
    # new original-typed declaration, without a second enum or registry mutation.
    member = ClassificationMethod._new_member_(
        ClassificationMethod,
        "independent_measurement_mode",
        _IndependentModeBehavior(),
        "Independent measurement mode",
    )
    assert isinstance(member, ClassificationMethod)
    assert member.value == "independent_measurement_mode"
    assert member.cellprofiler_literals == (
        "independent_measurement_mode",
        "Independent measurement mode",
    )
    module_type = IndependentPairDeclarationModule
    module = _module_block(
        module_type,
        (
            (
                module_type.classification_decision_count_setting.canonical,
                "Single measurement",
            ),
            (module_type.input_objects_setting.canonical, "Cells"),
            (module_type.first_measurement_feature_setting.canonical, "AreaShape_Area"),
            (
                module_type.second_measurement_feature_setting.canonical,
                "AreaShape_Area",
            ),
            (module_type.output_image_setting.canonical, "IndependentModeImage"),
        ),
    )
    bound = member.bind_settings(module_type, module, SettingsBinder())
    assert bound["independent_mode"] is True
    assert bound["measurement1_feature"] == "AreaShape_Area"
    assert bound["measurement2_feature"] == "AreaShape_Area"
    assert member.classified_image_outputs(module_type, module) == (
        ClassifiedImageOutput(7, "IndependentModeImage"),
    )
    invocation = next(
        normalize_function_pattern(independent_pair_declaration_callable).iter_items()
    )
    (finalized,) = member.finalize_module_blocks(module_type, (module,), invocation)
    assert setting_values(
        finalized, module_type.classification_decision_count_setting
    ) == ("Independent measurement mode",)
    assert setting_values(finalized, "Independent tail") == ("complete",)
    assert not setting_values(finalized, "Hidden")
    mro = _IndependentModeBehavior.__mro__
    assert mro.index(_IndependentModeProjectionCapability) < mro.index(
        _TwoMeasurementClassificationMethodBehavior
    )
    assert mro.index(_TwoMeasurementClassificationMethodBehavior) < mro.index(
        _ClassificationMethodBehavior
    )


@pytest.mark.parametrize(
    "member,value,literals",
    (
        (
            ClassificationMethod.SINGLE_MEASUREMENT,
            "single_measurement",
            ("single_measurement", "Single measurement"),
        ),
        (
            ClassificationMethod.TWO_MEASUREMENTS,
            "two_measurements",
            ("two_measurements", "Pair of measurements", "Two measurements"),
        ),
    ),
)
def test_original_mode_values_and_external_literals_remain_exact(
    member, value, literals
):
    assert member.value == value
    assert member.cellprofiler_literals == literals
    assert ClassificationMethod(value) is member
    assert all(
        coerce_cellprofiler_enum(ClassificationMethod, literal) is member
        for literal in literals
    )


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
    invocation = next(
        normalize_function_pattern(
            (classify_objects_two_measurements, paired_kwargs())
        ).iter_items()
    )
    blocks, _consumed = (
        ClassifyObjectsSingleMeasurementModule.module_blocks_for_invocation(
            invocation=invocation, step_context=_classification_context()
        )
    )
    assert setting_values(
        blocks[0],
        ClassifyObjectsSingleMeasurementModule.classification_decision_count_setting,
    ) == ("Pair of measurements",)
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


def test_unknown_external_parsed_mode_remains_rejected():
    declaration = ClassifyObjectsSingleMeasurementModule
    module = _module_block(
        declaration,
        (
            (
                declaration.classification_decision_count_setting.canonical,
                "Three unrelated vectors",
            ),
        ),
    )
    with pytest.raises(ValueError, match="cannot be coerced"):
        ClassificationMethod.from_module(declaration, module)


@pytest.mark.parametrize("rules", ((),))
def test_explicit_empty_rules_preserve_original_scalar_default(rules):
    kwargs = {
        "select_the_object_to_be_classified": "Cells",
        "measurement_feature": "AreaShape_Area",
        "classification_rules": rules,
    }
    contract = _public_function_step_contract(
        ClassifyObjectsSingleMeasurementModule,
        classify_objects_single_measurement,
        kwargs,
        _classification_context(),
    )
    request = _runtime_request(
        contract,
        {
            name: value
            for name, value in kwargs.items()
            if name != "select_the_object_to_be_classified"
        },
    )
    bound = ClassifyObjectsSingleMeasurementModule.bind_runtime_inputs(request)
    np.testing.assert_array_equal(bound["measurement_values"], (9.0, 300.0))
    assert "measurement_values_by_rule" not in bound
    image, rows = inspect.unwrap(classify_objects_single_measurement)(
        request.current_image,
        measurement_feature="AreaShape_Area",
        classification_rules=rules,
        **bound,
    )
    np.testing.assert_array_equal(
        image, request.label_payload_for(request.object_inputs[0]).variant_data.labels
    )
    assert rows.rows[0].total_objects == 2


@pytest.mark.parametrize("invalid_rules", ("raw", ("raw",)))
def test_untyped_rule_declarations_remain_rejected(invalid_rules):
    with pytest.raises(TypeError, match="tuple of SingleMeasurementClassificationRule"):
        _public_function_step_contract(
            ClassifyObjectsSingleMeasurementModule,
            classify_objects_single_measurement,
            {
                "select_the_object_to_be_classified": "Cells",
                "classification_rules": invalid_rules,
            },
            _classification_context(),
        )


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
