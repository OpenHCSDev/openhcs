"""Prepared canonical signatures survive compilation and worker transport."""

import inspect
import pickle
from types import SimpleNamespace
from dataclasses import replace
from functools import wraps
from unittest.mock import Mock
from typing import Any

import cloudpickle
import numpy as np
import pytest
from arraybridge import ArrayPayload

import openhcs.core.callable_contract as contract_module
from openhcs.core.callable_contract import (
    CallableContract, CallableImportIdentity, CallableMetadata, CallableProjection,
    attach_callable_contract_metadata, attach_processing_prepare,
)
from openhcs.core.function_contract_metadata import FunctionContractAttribute
from openhcs.core.function_patterns import NormalizedFunctionGroup
from openhcs.core.function_reference import ImportableFunctionReference
from openhcs.core.processing_preparation import CallablePreparation, PreparationCacheBatch
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.pipeline.function_contracts import composed_image_payload
from openhcs.processing.backends.lib_registry.registry_service import RegistryService
from openhcs.core.runtime_batch_contracts import (
    Pure2DSliceBatchExecutor, RuntimeBatchExecutionDomain,
    SerialPure2DSliceBatchExecutor, runtime_callable_defaults,
)
from openhcs.core.pipeline.function_contracts import resolved_callable_parameter
from openhcs.core.processing_contracts import (
    RuntimeCallablePolicy,
    SignatureFilteredKwargs,
)


def raw_numeric(image: np.ndarray, scale: float = 2.0) -> np.ndarray:
    return image * scale


@composed_image_payload
def unannotated_composed_echo(image):
    return image


@pytest.mark.parametrize(
    ("composed", "annotation", "retains_payload"),
    ((True, inspect.Parameter.empty, True),
     (False, inspect.Parameter.empty, False),
     (True, np.ndarray, False),
     (True, Any, False),
     (True, ArrayPayload, True)),
)
def test_composition_default_respects_explicit_raw_carrier_boundary(
    composed, annotation, retains_payload, fake_preparation,
):
    received = []
    def raw(image):
        received.append(image)
        return image
    if annotation is not inspect.Parameter.empty:
        raw.__annotations__["image"] = annotation
    if composed:
        composed_image_payload(raw)
    contract = CallableContract.from_prepared_callable(raw)
    pixels = np.arange(20, dtype=np.float32).reshape(1, 4, 5)
    mask = np.ones((1, 4, 5), dtype=bool)
    mask[0, 0, 0] = False
    source = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.SOURCE_BINDING,
        source_image_names=("FITC",),
    ).payload_with(pixels, mask)
    expected = source if retains_payload else pixels

    result = RuntimeCallablePolicy().contract_invocation(contract, raw, source, {}).call()

    assert result is expected
    assert received[0] is expected
    assert source.metadata.plane_axis is RuntimePlaneAxis.SOURCE_BINDING
    np.testing.assert_array_equal(source.mask, mask)


@pytest.mark.parametrize("serializer", (pickle, cloudpickle))
def test_prepared_composition_default_survives_transport_without_introspection(
    serializer, fake_preparation, monkeypatch,
):
    contract = CallableContract.from_prepared_callable(unannotated_composed_echo)
    reference = ImportableFunctionReference(
        import_identity=CallableImportIdentity.from_callable(unannotated_composed_echo),
        composite_key="test:unannotated_composed_echo", metadata=contract.metadata,
    )
    restored = CallableContract.from_callable(serializer.loads(serializer.dumps(reference)))
    def forbidden(*args, **kwargs):
        pytest.fail("Prepared composed ABI must not inspect live callable declarations")
    monkeypatch.setattr(contract_module, "get_type_hints", forbidden)
    monkeypatch.setattr(inspect, "signature", forbidden)
    payload = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.SOURCE_BINDING,
        source_image_names=("FITC",),
    ).payload_with(np.ones((1, 4, 5)), np.ones((1, 4, 5), dtype=bool))
    for _ in range(40):
        assert restored.raw_main_flow_call_argument(payload) is payload


@pytest.fixture
def fake_preparation(monkeypatch):
    prepare = Mock()
    monkeypatch.setattr(CallablePreparation, "prepare", prepare)
    monkeypatch.setattr(PreparationCacheBatch, "populate_child_caches", lambda *a, **k: None)
    return prepare


def test_registry_resolves_signatures_after_all_hooks_and_before_ready(monkeypatch):
    events = []

    def first(image: np.ndarray):
        return image

    def last(image: np.ndarray):
        return image

    first.__dict__[FunctionContractAttribute.raw_processing_function] = last
    metadata = {"first": SimpleNamespace(func=first), "alias": SimpleNamespace(func=first)}
    monkeypatch.setattr(RegistryService, "_metadata_cache", metadata)
    monkeypatch.setattr(PreparationCacheBatch, "populate_child_caches", lambda *a, **k: None)

    def prepare(owner):
        events.append(("prepare", owner.projection.func))
        if owner.projection.func is last:
            last.__annotations__["image"] = ArrayPayload

    original_hints = contract_module.get_type_hints

    def hints(func, **kwargs):
        events.append(("signature", func))
        return original_hints(func, **kwargs)

    monkeypatch.setattr(CallablePreparation, "prepare", prepare)
    monkeypatch.setattr(contract_module, "get_type_hints", hints)
    assert RegistryService.prepare_in_current_process(status_callback=events.append) is metadata
    preparations = [i for i, item in enumerate(events) if isinstance(item, tuple) and item[0] == "prepare"]
    signatures = [i for i, item in enumerate(events) if isinstance(item, tuple) and item[0] == "signature"]
    assert len(preparations) == 2
    assert max(preparations) < min(signatures)
    assert max(signatures) < next(i for i, item in enumerate(events) if isinstance(item, str) and "kernels ready" in item)
    assert CallableContract.from_callable(first).canonical_parameter_annotations["image"] is ArrayPayload
    assert CallableContract.from_callable(last).canonical_parameter_annotations["image"] is ArrayPayload


def test_explicit_library_rewarm_refreshes_new_contract_not_existing_snapshot(monkeypatch, fake_preparation):
    def raw(image: np.ndarray):
        return image

    metadata = {"raw": SimpleNamespace(func=raw)}
    monkeypatch.setattr(RegistryService, "_metadata_cache", metadata)
    RegistryService.prepare_in_current_process()
    first = CallableContract.from_callable(raw)
    raw.__annotations__["image"] = ArrayPayload
    assert CallableContract.from_callable(raw).canonical_parameter_annotations["image"] is np.ndarray
    RegistryService.prepare_in_current_process()
    second = CallableContract.from_callable(raw)
    assert first.canonical_parameter_annotations["image"] is np.ndarray
    assert second.canonical_parameter_annotations["image"] is ArrayPayload


def test_authored_compilation_prepares_before_signature_and_refreshes_each_compilation(monkeypatch):
    def raw(image: np.ndarray, scale=2):
        return image

    desired_annotations = [ArrayPayload, np.ndarray]

    def prepare(owner):
        raw.__annotations__["image"] = desired_annotations.pop(0)

    monkeypatch.setattr(CallablePreparation, "prepare", prepare)
    first = NormalizedFunctionGroup.from_pattern("group", raw).items[0].contract
    second = NormalizedFunctionGroup.from_pattern("group", raw).items[0].contract
    assert first.canonical_parameter_annotations["image"] is ArrayPayload
    assert second.canonical_parameter_annotations["image"] is np.ndarray
    assert FunctionContractAttribute.canonical_signature not in vars(raw)


def test_authored_preparation_precedes_metadata_validation(monkeypatch):
    def raw(image: np.ndarray):
        return image
    events = []
    original = CallableMetadata.from_projection.__func__

    def validate(cls, projection):
        assert events == ["prepared"]
        return original(cls, projection)

    monkeypatch.setattr(CallablePreparation, "prepare", lambda self: events.append("prepared"))
    monkeypatch.setattr(CallableMetadata, "from_projection", classmethod(validate))
    contract = CallableContract.from_prepared_callable(raw)
    assert contract.canonical_parameter_annotations["image"] is np.ndarray


def test_unprepared_function_reference_compilation_reads_prepared_live_declaration(monkeypatch, fake_preparation):
    reference = ImportableFunctionReference(
        import_identity=CallableImportIdentity.from_callable(raw_numeric),
        composite_key="test:raw_numeric",
    )
    contract = NormalizedFunctionGroup.from_pattern("group", reference).items[0].contract
    assert contract.func is reference
    assert contract.canonical_parameter_annotations["image"] is np.ndarray
    assert fake_preparation.call_count == 1


@pytest.mark.parametrize("serializer", [pickle, cloudpickle])
def test_prepared_signature_metadata_namespace_and_reference_transport(serializer, fake_preparation):
    contract = CallableContract.from_prepared_callable(raw_numeric)
    metadata = contract.metadata

    def proxy(image):
        return image

    proxy.__dict__.update(metadata.as_namespace())
    assert CallableMetadata.from_callable(proxy).canonical_signature == metadata.canonical_signature
    reference = ImportableFunctionReference(
        import_identity=CallableImportIdentity.from_callable(raw_numeric),
        composite_key="test:raw_numeric", metadata=metadata,
    )
    restored = serializer.loads(serializer.dumps(reference))
    assert restored.metadata.canonical_signature == metadata.canonical_signature
    restored_contract = CallableContract.from_callable(restored)
    assert restored_contract.canonical_parameter_annotations["image"] is np.ndarray
    assert restored_contract.canonical_signature.parameters["scale"].default == 2.0
    assert restored_contract.canonical_signature.return_annotation is np.ndarray


def test_compiled_raw_projection_never_queries_signature_or_annotations(monkeypatch, fake_preparation):
    contract = CallableContract.from_prepared_callable(raw_numeric)
    reference = ImportableFunctionReference(
        import_identity=CallableImportIdentity.from_callable(raw_numeric),
        composite_key="test:raw_numeric", metadata=contract.metadata,
    )
    restored = CallableContract.from_callable(pickle.loads(pickle.dumps(reference)))
    def forbidden(*args, **kwargs):
        raise AssertionError("Compiled runtime queried a live signature")
    monkeypatch.setattr(contract_module, "get_type_hints", forbidden)
    monkeypatch.setattr(inspect, "signature", forbidden)
    payload = ImagePayloadMetadata(source_image_names=("DNA",)).payload_with(np.ones((2, 3)), None)
    for _ in range(40):
        assert restored.raw_main_flow_call_argument(payload) is payload.data
        assert restored.primary_input_parameter_name == "image"
        assert restored.canonical_parameter_annotations["image"] is np.ndarray


def test_custom_signature_and_mutable_default_are_retained_until_recompilation(monkeypatch, fake_preparation):
    default = []
    def raw(image, values=None):
        return image
    raw.__signature__ = inspect.Signature([
        inspect.Parameter("image", inspect.Parameter.POSITIONAL_ONLY, annotation=ArrayPayload),
        inspect.Parameter("values", inspect.Parameter.KEYWORD_ONLY, default=default),
    ])
    first = CallableContract.from_prepared_callable(raw)
    assert first.canonical_signature.parameters["values"].default is default
    raw.__signature__ = raw.__signature__.replace(parameters=[
        inspect.Parameter("image", inspect.Parameter.POSITIONAL_ONLY, annotation=np.ndarray),
    ])
    second = CallableContract.from_prepared_callable(raw)
    assert first.canonical_parameter_annotations["image"] is ArrayPayload
    assert second.canonical_parameter_annotations["image"] is np.ndarray


@pytest.mark.parametrize("mutation", [
    lambda func: attach_processing_prepare(func, lambda: None),
    lambda func: attach_callable_contract_metadata(func, raw_processing_function=raw_numeric),
])
def test_supported_declaration_changes_invalidate_published_signature(mutation):
    def raw(image: np.ndarray):
        return image
    CallableProjection.from_callable(raw).warm_canonical_signature()
    assert FunctionContractAttribute.canonical_signature in vars(raw)
    mutation(raw)
    assert FunctionContractAttribute.canonical_signature not in vars(raw)


def test_malformed_signature_declaration_is_rejected():
    def raw(image):
        return image
    raw.__dict__[FunctionContractAttribute.canonical_signature] = "not a signature"
    with pytest.raises(TypeError, match="inspect.Signature"):
        CallableMetadata.from_callable(raw)


def test_exact_raw_default_filter_and_type_views_refresh_with_library_snapshot():
    def raw(image: np.ndarray, scale: float = 2):
        return image * scale
    CallableProjection.from_callable(raw).warm_canonical_signature()
    policy = RuntimeCallablePolicy(kwarg_policy=SignatureFilteredKwargs)
    assert runtime_callable_defaults(raw)["scale"] == 2
    assert resolved_callable_parameter(raw, "scale").annotation is float
    assert policy.invocation(raw, (np.ones((2, 3)),), {"scale":3, "unknown":9}).call()[0,0] == 3
    raw.__defaults__ = (4,)
    raw.__annotations__["scale"] = int
    assert runtime_callable_defaults(raw)["scale"] == 2
    assert resolved_callable_parameter(raw, "scale").annotation is float
    CallableProjection.from_callable(raw).warm_canonical_signature()
    assert runtime_callable_defaults(raw)["scale"] == 4
    assert resolved_callable_parameter(raw, "scale").annotation is int


def test_different_wrapper_signature_remains_live_for_default_filter_and_parameter_queries():
    def raw(image: np.ndarray, private: int = 8):
        return image
    def wrapper(image: np.ndarray, public: int = 2):
        return image * public
    wrapper.__dict__[FunctionContractAttribute.raw_processing_function] = raw
    CallableProjection.from_callable(wrapper).warm_canonical_signature()
    assert runtime_callable_defaults(wrapper) == {"public":2}
    assert resolved_callable_parameter(wrapper, "public").annotation is int
    policy = RuntimeCallablePolicy(kwarg_policy=SignatureFilteredKwargs)
    assert policy.invocation(wrapper, (np.ones((2, 3)),), {"public":3, "private":99}).call()[0,0] == 3
    wrapper.__defaults__ = (5,)
    assert runtime_callable_defaults(wrapper) == {"public":5}
    assert policy.invocation(wrapper, (np.ones((2, 3)),), {"private":99}).call()[0,0] == 5


def test_prepared_type_query_preserves_legacy_nested_annotation_stripping():
    from typing import Annotated, get_type_hints
    def raw(image, labels):
        return image
    raw.__annotations__ = {"image":Annotated[np.ndarray,"image"],"labels":tuple[Annotated[int,"id"],...],"return":Annotated[np.ndarray,"result"]}
    expected = get_type_hints(raw)
    CallableProjection.from_callable(raw).warm_canonical_signature()
    assert resolved_callable_parameter(raw,"image").annotation == expected["image"]
    assert resolved_callable_parameter(raw,"labels").annotation == expected["labels"]
    assert CallableContract.from_callable(raw).canonical_parameter_annotations["labels"] == raw.__annotations__["labels"]


def test_distinct_authored_runtime_signature_transport_and_new_compilation_refresh(fake_preparation):
    def raw(image: np.ndarray, scale: int = 2) -> np.ndarray:
        return image * scale
    @wraps(raw)
    def wrapper(*args, **kwargs):
        return raw(*args, **kwargs)
    wrapper.__signature__ = inspect.signature(raw).replace(parameters=[
        *inspect.signature(raw).parameters.values(),
        inspect.Parameter("injected",inspect.Parameter.KEYWORD_ONLY,default=False),
    ])
    first = CallableContract.from_prepared_callable(wrapper)
    assert "injected" in first.canonical_signature.parameters
    assert "injected" not in first.raw_runtime_signature.parameters
    assert first.metadata.raw_runtime_signature is not None
    restored = pickle.loads(pickle.dumps(first.metadata))
    assert restored.raw_runtime_signature == first.raw_runtime_signature
    assert restored.as_namespace()[FunctionContractAttribute.raw_runtime_signature] == first.raw_runtime_signature
    assert FunctionContractAttribute.canonical_signature not in vars(raw)
    assert FunctionContractAttribute.canonical_signature not in vars(wrapper)
    raw.__defaults__ = (4,)
    raw.__annotations__["scale"] = float
    second = CallableContract.from_prepared_callable(wrapper)
    assert first.raw_runtime_signature.parameters["scale"].default == 2
    assert second.raw_runtime_signature.parameters["scale"].default == 4
    assert second.raw_runtime_signature.parameters["scale"].annotation is float


def test_distinct_targets_own_signatures_even_when_layouts_match_without_comparing_defaults(fake_preparation):
    class RejectEquality:
        def __eq__(self, other):
            raise AssertionError("Signature reuse compared a mutable default")
    default = RejectEquality()
    def raw(image: np.ndarray, values=default) -> np.ndarray:
        return image
    @wraps(raw)
    def wrapper(*args, **kwargs):
        return raw(*args, **kwargs)
    contract = CallableContract.from_prepared_callable(wrapper)
    assert contract.metadata.raw_runtime_signature is not None
    assert contract.raw_runtime_signature is not contract.canonical_signature
    assert contract.raw_runtime_signature.parameters["values"].default is default
    raw.__defaults__ = ("new raw default",)
    second = CallableContract.from_prepared_callable(wrapper)
    assert second.raw_runtime_signature.parameters["values"].default == "new raw default"
    assert contract.raw_runtime_signature.parameters["values"].default is default


def test_same_actual_target_shares_canonical_signature(fake_preparation):
    contract = CallableContract.from_prepared_callable(raw_numeric)
    assert contract.metadata.raw_runtime_signature is None
    assert contract.raw_runtime_signature is contract.canonical_signature


@pytest.mark.parametrize("executors", (None, {}, {RuntimeBatchExecutionDomain.PURE_2D_SLICES: None}))
def test_pure_2d_executor_selection_retains_serial_fallback(executors):
    assert isinstance(Pure2DSliceBatchExecutor.from_executors(executors), SerialPure2DSliceBatchExecutor)


def test_pure_2d_executor_selection_retains_exact_declared_executor():
    def declared(*args, **kwargs):
        raise AssertionError("Selecting an executor must not execute it")

    selected = Pure2DSliceBatchExecutor.from_executors({
        RuntimeBatchExecutionDomain.PURE_2D_SLICES: declared,
    })
    assert selected is declared


def test_compiled_input_places_named_bundle_once_before_cpu_identity_shortcut(monkeypatch):
    from openhcs.core.aligned_image_payload import (
        AlignedImageSliceContext, ImageOutputBundle,
    )
    from openhcs.core.function_patterns import compile_function_pattern
    from openhcs.processing.backends.processors.numpy_processor import gaussian_blur

    pixels = tuple(np.full((3, 4), value, dtype=np.float32) for value in (0.25, 0.75))
    masks = tuple(np.full((3, 4), value, dtype=bool) for value in (True, False))
    source = ImageOutputBundle(
        tuple(ImagePayloadMetadata().payload_with(data, mask)
              for data, mask in zip(pixels, masks, strict=True)),
        tuple(AlignedImageSliceContext.independent_main_flow(name)
              for name in ("DNA", "Membrane")),
    )
    calls = []
    original = ImageOutputBundle.compose

    def observed(value, **destination):
        calls.append(destination)
        return original(value, **destination)

    monkeypatch.setattr(ImageOutputBundle, "compose", observed)
    invocation = compile_function_pattern(gaussian_blur, {}, {}).default_group.invocations[0]
    placed = invocation.convert_input(source, "numpy")
    invocation.main_flow_call_argument(placed)
    placed.data
    placed.mask

    assert calls == [{"memory_type": "numpy", "device_id": None}]
    np.testing.assert_array_equal(placed.data, np.stack(pixels))
    assert placed.data.shape == (2, 3, 4)
    assert placed.mask.shape == (2, 3, 4)
    assert placed.metadata.source_image_names == ("DNA", "Membrane")
    np.testing.assert_array_equal(placed.mask, np.stack(masks))


def test_compiled_input_reuses_produced_stack_realization_without_copy():
    from openhcs.core.aligned_image_payload import (
        AlignedImageSliceContext, ProducedImageStack,
    )
    from openhcs.core.function_patterns import compile_function_pattern
    from openhcs.processing.backends.processors.numpy_processor import gaussian_blur

    source = ProducedImageStack(
        tuple(np.full((3, 4), value, dtype=np.float32) for value in (1, 2)),
        memory_type="numpy", plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    )
    invocation = compile_function_pattern(gaussian_blur, {}, {}).default_group.invocations[0]
    placed = invocation.convert_input(source, "numpy")
    assert invocation.convert_input(source, "numpy") is placed
    assert placed.data is source.data
    assert np.shares_memory(source.slices[0], placed.data)
