"""Context injection belongs to the captured callable declaration."""

import inspect
import pickle
from types import SimpleNamespace

import numpy as np
import pytest
from python_introspect import parameter_exclusions

from openhcs.core.callable_contract import (
    CallableContract,
    CallableMetadata,
    CallableProjection,
    prepare_processing_callable,
)
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.function_contract_metadata import FunctionContractAttribute
from openhcs.core.function_patterns import compile_function_pattern
from openhcs.core.function_reference import FunctionReferenceTransportAuthority
from openhcs.core.memory import numpy
from openhcs.core.pipeline.function_contracts import runtime_context_parameter
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_plane_projection import RuntimePlaneProjection
from openhcs.core.source_bindings import SourceBindingRuntimeContext
from openhcs.core.steps.function_runtime import (
    ComponentArtifactPlans,
    FunctionCoreExecutor,
    FunctionRuntimeScope,
)
from openhcs.processing.backends.cellprofiler.save_images import (
    save_images,
    save_images_with_measurements,
)
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract


def _inferred_context(image, *, context=None):
    return image, context


@runtime_context_parameter(None)
def _without_context(image, *, context=None):
    return image, context


@runtime_context_parameter("execution_context")
def _named_context(image, *, execution_context=None):
    return image, execution_context


def test_absent_declaration_retains_signature_inference():
    assert FunctionContractAttribute.runtime_context_parameter not in vars(
        _inferred_context
    )
    assert CallableContract.from_callable(_inferred_context).runtime_context_parameter == (
        "context"
    )


def test_none_declaration_preserves_callable_identity_and_public_signature():
    def process(image, *, context=None):
        return image, context

    signature = inspect.signature(process)
    assert runtime_context_parameter(None)(process) is process
    assert inspect.signature(process) == signature
    assert signature.parameters["context"].default is None
    assert CallableContract.from_callable(process).runtime_context_parameter is None
    marker = object()
    assert process(marker) == (marker, None)
    assert process(marker, context=marker) == (marker, marker)


@pytest.mark.parametrize(
    ("func", "expected"),
    [(_inferred_context, "context"), (_without_context, None),
     (_named_context, "execution_context")],
)
def test_namespace_reconstruction_retains_captured_selection(func, expected):
    metadata = CallableMetadata.from_callable(func)
    namespace = metadata.as_namespace()
    assert namespace[FunctionContractAttribute.runtime_context_parameter] == expected
    projection = CallableProjection(
        func=func, name=func.__name__, module_name=func.__module__, namespace=namespace
    )
    assert CallableMetadata.from_projection(projection).runtime_context_parameter == (
        expected
    )


@pytest.mark.parametrize("func", [_inferred_context, _without_context, _named_context])
def test_reference_and_pickle_reconstruction_retain_selection(func):
    expected = CallableContract.from_callable(func).runtime_context_parameter
    reference = FunctionReferenceTransportAuthority.function_reference(func)
    restored_reference = pickle.loads(pickle.dumps(reference))
    assert restored_reference.resolve() is func
    assert CallableContract.from_callable(restored_reference).runtime_context_parameter == (
        expected
    )
    contract = CallableContract.from_callable(restored_reference)
    assert pickle.loads(pickle.dumps(contract)).runtime_context_parameter == expected


def test_wrapper_preparation_does_not_resurrect_context_inference():
    @numpy(contract=ProcessingContract.PURE_2D)
    @runtime_context_parameter(None)
    def process(image, *, context=None):
        del context
        return image

    prepare_processing_callable(process)
    contract = CallableContract.from_callable(process)
    assert contract.runtime_context_parameter is None
    assert "context" not in contract.runtime_owned_parameter_names
    assert "context" not in parameter_exclusions(process)
    assert inspect.signature(contract.resolve_canonical_raw_callable()).parameters[
        "context"
    ].default is None


@pytest.mark.parametrize(
    ("func", "parameter"),
    [(_inferred_context, "context"), (_without_context, None),
     (_named_context, "execution_context")],
)
def test_runtime_binding_consumes_captured_selection(func, parameter):
    pattern = compile_function_pattern(func, {}, {})
    context = ProcessingContext(axis_id="A01")
    artifacts = ComponentArtifactPlans(inputs={}, outputs={})
    scope = FunctionRuntimeScope(
        context=context,
        execution_plan=CompiledStepPlan(
            step_index=0, step_name="Context", step_type="FunctionStep", axis_id="A01"
        ),
        compiled_group=pattern.default_group,
        artifacts=artifacts,
        source_binding_context=SourceBindingRuntimeContext.empty(),
        runtime_plane_index=0,
        runtime_plane_count=1,
    )
    executor = FunctionCoreExecutor(
        runtime_scope=scope,
        invocation=next(pattern.iter_invocations()),
        artifacts=artifacts,
        group_key=None,
        plane_projection=RuntimePlaneProjection(),
        main_data_arg=np.zeros((2, 3)),
        source_memory_type="numpy",
    )
    kwargs = {}
    executor.bind_runtime_owned_parameters(kwargs)
    assert kwargs == ({} if parameter is None else {parameter: context})


def test_save_images_variants_keep_independent_injection_declarations():
    plain = CallableContract.from_callable(save_images)
    measurements = CallableContract.from_callable(save_images_with_measurements)
    assert plain.runtime_context_parameter is None
    assert measurements.runtime_context_parameter == "context"
    for func in (save_images, save_images_with_measurements):
        reference = FunctionReferenceTransportAuthority.function_reference(func)
        expected = CallableContract.from_callable(func).runtime_context_parameter
        assert CallableContract.from_callable(reference).runtime_context_parameter == expected


def test_measurement_variant_keeps_real_axis_scoped_filename_context():
    context = ProcessingContext(axis_id="A01")
    context.execution_runtime = SimpleNamespace(execution_axis_values=("A01", "A02"))
    payload = ImagePayloadMetadata(source_path="/input/DNA.tif").payload_with(
        np.ones((2, 3), dtype=np.uint16)
    )
    contract = CallableContract.from_callable(save_images_with_measurements)
    primary, _saved, rows = contract.resolve_canonical_raw_callable()(
        payload, image_to_save=payload, saved_image_name="Saved", context=context
    )
    assert primary is payload
    values = {row.feature_name: row.result_value for row in rows.rows}
    assert values["PathName_Saved"] == "A01"
    assert values["FileName_Saved"] == "DNA.tiff"
    assert values["URL_Saved"] == "file:A01/DNA.tiff"


def test_named_context_declaration_does_not_resolve_unrelated_forward_references():
    namespace = {"runtime_context_parameter": runtime_context_parameter}
    exec(
        "@runtime_context_parameter('context')\n"
        "def process(image: 'DefinedAfterDeclaration', *, context=None):\n"
        "    return image, context\n"
        "class DefinedAfterDeclaration:\n"
        "    pass\n",
        namespace,
    )
    process = namespace["process"]
    assert inspect.signature(process).parameters["image"].annotation == (
        "DefinedAfterDeclaration"
    )
    assert vars(process)[FunctionContractAttribute.runtime_context_parameter] == "context"
    assert CallableMetadata.from_callable(process).runtime_context_parameter == "context"
    marker = namespace["DefinedAfterDeclaration"]()
    assert process(marker, context=marker) == (marker, marker)


def test_declaration_rejects_unknown_parameter_without_mutating_callable():
    before = dict(vars(_inferred_context))
    with pytest.raises(ValueError, match="does not declare parameter"):
        runtime_context_parameter("missing")(_inferred_context)
    assert vars(_inferred_context) == before


def test_declaration_rejects_non_string_parameter():
    with pytest.raises(TypeError, match="parameter name or None"):
        runtime_context_parameter(7)
