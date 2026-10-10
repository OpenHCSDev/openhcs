"""Focused tests for the CellProfiler mode/processing-contract boundary."""

from __future__ import annotations

from collections.abc import Callable, Sequence
from dataclasses import dataclass, replace
from functools import wraps
import inspect
from typing import Annotated, Any, Union

import numpy as np
import pytest
from arraybridge import ArrayPayload
import openhcs.core.callable_contract as callable_contract_module

from openhcs.core.aligned_image_payload import (
    AlignedImageStack,
    ImageOutputBundle,
    ImagePayloadExecutionMode,
    compose_aligned_image_payload,
)
from openhcs.core.artifacts import (
    ArtifactSpec,
    ImageArtifactType,
    MeasurementsArtifactType,
)
from openhcs.core.callable_contract import (
    CallableContract,
    CallableMetadata,
    CallableProjection,
    callable_request,
)
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisValueProjection,
)
from openhcs.core.runtime_slice_alignment import RuntimeSliceAlignedValues
from openhcs.core.runtime_slice_projection import RuntimeSliceProjectionDeclarationError
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_array_values import RuntimeArrayData
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.interop.cellprofiler.runtime.function_contract_execution import (
    CellProfilerFunctionContractExecutor,
)
from openhcs.interop.cellprofiler.runtime.adapter import CellProfilerRuntimeAdapter
from openhcs.processing.backends.cellprofiler.alignment import AlignShiftMeasurement
from openhcs.processing.backends.cellprofiler.morphology import (
    MorphOperation,
    morph,
    morphologicalskeleton,
)
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.processing.backends.lib_registry.unified_registry import (
    RuntimeCallablePolicy, RuntimeInvocationKwargPolicy,
)


def _compiled_contract(
    func: Callable[..., object],
    processing_contract: ProcessingContract,
    *,
    artifact_inputs: tuple[ArtifactSpec, ...] = (),
    artifact_outputs: tuple[ArtifactSpec, ...] = (),
) -> CallableContract:
    return CallableContract(
        func=func,
        function_name="dispatch_probe",
        module_name="DispatchProbeModule",
        metadata=CallableMetadata(
            processing_contract=processing_contract,
            artifact_inputs=artifact_inputs,
            artifact_outputs=artifact_outputs,
        ),
    ).with_prepared_signature()


def test_morphological_skeleton_executes_one_planar_runtime_image() -> None:
    callable_contract = CallableContract.from_callable(morphologicalskeleton)
    raw_callable = callable_contract.resolve_canonical_raw_callable()
    image = np.zeros((7, 7), dtype=np.float32)
    image[2:5, 3] = 1.0

    result = CellProfilerFunctionContractExecutor().execute(
        callable_contract,
        raw_callable,
        image,
        {},
        execution_mode=ImagePayloadExecutionMode.NATURAL,
    )

    assert callable_contract.processing_contract is ProcessingContract.PURE_2D
    assert result.data.shape == image.shape


def test_registered_morph_distance_projects_raw_abi_and_retains_source_context() -> None:
    contract = CallableContract.from_callable(morph)
    contract = replace(
        contract,
        metadata=replace(
            contract.metadata,
            runtime_adapter=CellProfilerRuntimeAdapter.runtime_adapter_spec(),
            artifact_outputs=(ArtifactSpec.output("Distance", ImageArtifactType),),
        ),
    )
    pixels = np.zeros((1, 7, 7), dtype=np.float32)
    pixels[:, 2:5, 2:5] = 1
    mask = np.ones_like(pixels, dtype=bool)
    source = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_image_names=("SavedLabels",),
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/tmp/saved-labels.tif",),
            component_metadata=({"channel": "2", "well": "A01"},),
        ),
    ).payload_with(pixels, mask)
    expected = contract.resolve_raw_runtime_callable()(
        pixels[0], operation=MorphOperation.DISTANCE
    )

    result = CellProfilerFunctionContractExecutor().execute(
        contract,
        contract.resolve_canonical_raw_callable(),
        source,
        {"operation": MorphOperation.DISTANCE},
        execution_mode=ImagePayloadExecutionMode.NATURAL,
        plane_projection=RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE, axis_size=1,
        ),
    )

    np.testing.assert_array_equal(result.data, expected[None])
    np.testing.assert_array_equal(result.mask, mask)
    metadata = result.metadata
    assert metadata.plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
    assert metadata.source_image_names == ("SavedLabels",)
    assert metadata.source_image_provenance_planes.paths == ("/tmp/saved-labels.tif",)
    assert metadata.source_image_provenance_planes.component_metadata == (
        {"channel": "2", "well": "A01"},
    )


@pytest.mark.parametrize("payload_annotation", (False, True))
def test_raw_slice_abi_retains_declared_payloads_and_projects_kwargs(
    payload_annotation: bool,
) -> None:
    seen = []

    def array_raw(image: np.ndarray, *, labels: np.ndarray) -> np.ndarray:
        assert isinstance(image, np.ndarray)
        seen.append((image, labels))
        return image + labels

    def payload_raw(image: ArrayPayload, *, labels: np.ndarray) -> ArrayPayload:
        assert isinstance(image, ArrayPayload)
        seen.append((image, labels))
        return image.metadata.payload_with(
            image.data + labels, image.mask,
        )

    raw = payload_raw if payload_annotation else array_raw
    contract = _compiled_contract(raw, ProcessingContract.PURE_2D)
    contract = replace(
        contract,
        metadata=replace(
            contract.metadata,
            runtime_adapter=CellProfilerRuntimeAdapter.runtime_adapter_spec(),
        ),
    )
    source = ImagePayloadMetadata(source_image_names=("DNA",)).payload_with(
        np.ones((3, 4), dtype=np.float32), np.ones((3, 4), dtype=bool),
    )
    selected_labels = np.full((3, 4), 5, dtype=np.float32)
    executor = CellProfilerFunctionContractExecutor(
        plane_projection=RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE, axis_size=2,
        ),
    )

    assert contract.runtime_main_flow_call_argument(source) is source
    result = executor.execute_pure_2d_slice(
        contract, raw, source,
        {"labels": RuntimeSliceAlignedValues(slices=(np.zeros((3, 4)), selected_labels)),
         "adapter_only_control": 1},
        1, 2,
    )

    assert seen[0][0] is (source if payload_annotation else source.data)
    assert seen[0][1] is selected_labels
    np.testing.assert_array_equal(result.data, np.full((3, 4), 6))
    np.testing.assert_array_equal(result.mask, source.mask)
    assert result.metadata.source_image_names == ("DNA",)


def test_raw_slice_abi_does_not_relax_output_mask_shape_validation() -> None:
    def bad_shape(image: np.ndarray) -> np.ndarray:
        assert isinstance(image, np.ndarray)
        return image[:1]

    contract = _compiled_contract(bad_shape, ProcessingContract.PURE_2D)
    source = ImagePayloadMetadata(source_image_names=("DNA",)).payload_with(
        np.ones((3, 4)), np.ones((3, 4), dtype=bool),
    )
    executor = CellProfilerFunctionContractExecutor(
        plane_projection=RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE, axis_size=1,
        ),
    )
    with pytest.raises(ValueError, match="[Mm]ask.*shape|shape.*[Mm]ask"):
        executor.execute_pure_2d_slice(contract, bad_shape, source, {}, 0, 1)


@pytest.mark.parametrize("payload_annotation", (False, True))
@pytest.mark.parametrize(
    ("processing_contract", "execution_mode"),
    (
        (ProcessingContract.PURE_2D, ImagePayloadExecutionMode.NATURAL),
        (ProcessingContract.PURE_3D, ImagePayloadExecutionMode.NATURAL),
        (ProcessingContract.PURE_2D, ImagePayloadExecutionMode.FULL_STACK),
        (ProcessingContract.PURE_3D, ImagePayloadExecutionMode.FULL_STACK),
    ),
)
def test_raw_abi_projection_matches_declared_argument_in_single_and_full_stack_modes(
    payload_annotation: bool,
    processing_contract: ProcessingContract,
    execution_mode: ImagePayloadExecutionMode,
) -> None:
    seen = []

    def array_raw(image: np.ndarray) -> np.ndarray:
        assert isinstance(image, np.ndarray)
        seen.append(image)
        return image

    def payload_raw(image: ArrayPayload) -> ArrayPayload:
        assert isinstance(image, ArrayPayload)
        seen.append(image)
        return image

    raw = payload_raw if payload_annotation else array_raw
    contract = _compiled_contract(raw, processing_contract)
    contract = replace(
        contract,
        metadata=replace(
            contract.metadata,
            runtime_adapter=CellProfilerRuntimeAdapter.runtime_adapter_spec(),
            artifact_outputs=(ArtifactSpec.output("Result", ImageArtifactType),),
        ),
    )
    source = ImagePayloadMetadata(source_image_names=("DNA",)).payload_with(
        np.ones((3, 4)), None,
    )

    result = CellProfilerFunctionContractExecutor().execute(
        contract, raw, source, {}, execution_mode=execution_mode,
    )

    assert seen == [source if payload_annotation else source.data]
    assert seen[0] is (source if payload_annotation else source.data)
    assert result is seen[0]


@pytest.mark.parametrize(
    ("annotation", "retains_payload"),
    (
        (np.ndarray, False),
        (ArrayPayload, True),
        (RuntimeArrayData, True),
        (Union[ArrayPayload, np.ndarray], True),
        (Annotated[ArrayPayload, "source context"], True),
        (Annotated[RuntimeArrayData, "source context"], True),
        (Union[Annotated[ArrayPayload, "source context"], np.ndarray], True),
        (Union[Annotated[RuntimeArrayData, "source context"], None], True),
        (object, True),
        (Any, False),
        (inspect.Parameter.empty, False),
        (Sequence[ArrayPayload], False),
        (tuple[ArrayPayload, ...], False),
    ),
)
def test_canonical_argument_projection_uses_declared_nominal_annotation(
    annotation: object, retains_payload: bool,
) -> None:
    def raw(image):
        return image

    if annotation is not inspect.Parameter.empty:
        raw.__annotations__["image"] = annotation
    contract = _compiled_contract(raw, ProcessingContract.PURE_2D)
    source = ImagePayloadMetadata(source_image_names=("DNA",)).payload_with(
        np.ones((3, 4)), None,
    )
    expected = source if retains_payload else source.data

    assert contract.raw_main_flow_call_argument(source) is expected
    assert contract.runtime_main_flow_call_argument(source) is expected
    adapted = replace(
        contract,
        metadata=replace(
            contract.metadata,
            runtime_adapter=CellProfilerRuntimeAdapter.runtime_adapter_spec(),
        ),
    )
    assert adapted.raw_main_flow_call_argument(source) is expected
    assert adapted.runtime_main_flow_call_argument(source) is source


def test_raw_slice_argument_retains_buffer_identity_for_inplace_array_callable() -> None:
    def inplace(image: np.ndarray) -> np.ndarray:
        image[0, 0] = 7
        return image

    contract = _compiled_contract(inplace, ProcessingContract.PURE_2D)
    pixels = np.zeros((3, 4))
    source = ImagePayloadMetadata(source_image_names=("DNA",)).payload_with(
        pixels, None,
    )
    executor = CellProfilerFunctionContractExecutor(
        plane_projection=RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE, axis_size=1,
        ),
    )
    result = executor.execute_pure_2d_slice(contract, inplace, source, {}, 0, 1)

    assert result.data is pixels
    assert pixels[0, 0] == 7


def test_prepared_raw_abi_performs_no_introspection_until_explicit_refresh(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    seen = []

    def raw(image: np.ndarray) -> np.ndarray:
        seen.append(isinstance(image, ArrayPayload))
        return image

    contract = _compiled_contract(
        raw, ProcessingContract.PURE_2D,
        artifact_outputs=(ArtifactSpec.output("Result", ImageArtifactType),),
    )
    source = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE, source_image_names=("DNA",),
    ).payload_with(np.ones((12, 3, 4)), None)
    projection = RuntimePlaneAxisValueProjection.preserve(
        axis=RuntimePlaneAxis.RUNTIME_SLICE, axis_size=12,
    )
    executor = CellProfilerFunctionContractExecutor(plane_projection=projection)
    hints = []
    signatures = []
    original_hints = callable_contract_module.get_type_hints
    original_signature = inspect.signature

    def counted_hints(func, **kwargs):
        hints.append((func, kwargs))
        return original_hints(func, **kwargs)

    def counted_signature(func, **kwargs):
        caller = inspect.currentframe().f_back
        if caller.f_globals is callable_contract_module.__dict__:
            signatures.append(caller.f_code.co_name)
        return original_signature(func, **kwargs)

    monkeypatch.setattr(callable_contract_module, "get_type_hints", counted_hints)
    monkeypatch.setattr(inspect, "signature", counted_signature)

    for annotation in (np.ndarray, ArrayPayload):
        raw.__annotations__["image"] = annotation
        contract = contract.with_prepared_signature()
        result = executor.execute(
            contract, raw, source, {},
            execution_mode=ImagePayloadExecutionMode.NATURAL,
            plane_projection=projection,
        )
        np.testing.assert_array_equal(result.data, source.data)

    assert seen == [False] * 12 + [True] * 12
    assert hints == [(raw, {"include_extras": True})] * 2
    assert signatures == ["resolve_signature"] * 2
    assert not hasattr(executor, "_raw_argument_types")


def test_raw_abi_derivation_follows_existing_input_guards(monkeypatch) -> None:
    def raw(image: np.ndarray) -> np.ndarray:
        raise AssertionError("Invalid image reached raw execution")

    contract = _compiled_contract(raw, ProcessingContract.PURE_2D)

    def reject_premature_annotations(self):
        raise AssertionError("Input guard resolved the raw ABI prematurely")

    monkeypatch.setattr(
        CallableContract, "canonical_parameter_declarations",
        property(reject_premature_annotations),
    )
    with pytest.raises(TypeError, match="requires AlignedImageStack"):
        CellProfilerFunctionContractExecutor().execute(
            contract, raw, np.zeros((2, 3)), {},
            execution_mode=ImagePayloadExecutionMode.ALIGNED_MULTI_IMAGE_STACK,
        )
    projection = RuntimePlaneAxisValueProjection.preserve(
        axis=RuntimePlaneAxis.RUNTIME_SLICE, axis_size=2,
    )
    mismatched_image = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.SOURCE_BINDING,
    ).payload_with(np.zeros((2, 3, 4)), None)
    with pytest.raises(RuntimeSliceProjectionDeclarationError, match="conflicts"):
        CellProfilerFunctionContractExecutor().execute(
            contract, raw, mismatched_image, {},
            execution_mode=ImagePayloadExecutionMode.NATURAL,
            plane_projection=projection,
        )


def test_raw_abi_child_preserves_cooperative_executor_constructor_contract() -> None:
    constructed = []
    raw_calls = []

    class CooperativeExecutor(CellProfilerFunctionContractExecutor):
        def __init__(self, plane_projection=None):
            super().__init__(plane_projection=plane_projection)
            constructed.append(self)

        def execute_pure_2d_slice(self, *args, **kwargs):
            raw_calls.append(self)
            return super().execute_pure_2d_slice(*args, **kwargs)

    def raw(image: np.ndarray) -> np.ndarray:
        assert isinstance(image, np.ndarray)
        return image

    contract = _compiled_contract(
        raw, ProcessingContract.PURE_2D,
        artifact_outputs=(ArtifactSpec.output("Result", ImageArtifactType),),
    )
    source = ImagePayloadMetadata(plane_axis=RuntimePlaneAxis.RUNTIME_SLICE).payload_with(
        np.ones((2, 3, 4)), None,
    )
    executor = CooperativeExecutor()
    result = executor.execute(
        contract, raw, source, {}, execution_mode=ImagePayloadExecutionMode.NATURAL,
        plane_projection=RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE, axis_size=2,
        ),
    )

    assert len(constructed) == 2
    assert raw_calls == [constructed[1]] * 2
    assert not hasattr(executor, "_raw_argument_types")
    np.testing.assert_array_equal(result.data, source.data)

    def foreign_raw(image: ArrayPayload) -> ArrayPayload:
        assert isinstance(image, ArrayPayload)
        return image

    foreign_contract = _compiled_contract(foreign_raw, ProcessingContract.PURE_2D)
    child = constructed[1]
    policy = RuntimeCallablePolicy(kwarg_policy=RuntimeInvocationKwargPolicy.SIGNATURE_FILTERED)
    assert policy.contract_invocation(foreign_contract, foreign_raw, source, {}).call() is source
    assert not hasattr(child, "_scope_contract")


def test_actual_prepared_executor_planes_make_no_signature_or_hint_queries(monkeypatch) -> None:
    calls = []
    def raw(image: np.ndarray, scale: int = 2) -> np.ndarray:
        calls.append(image.shape)
        return image * scale
    CallableProjection.from_callable(raw).warm_canonical_signature()
    contract = _compiled_contract(
        raw, ProcessingContract.PURE_2D,
        artifact_outputs=(ArtifactSpec.output("Result",ImageArtifactType),),
    )
    source = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,source_image_names=("DNA",),
    ).payload_with(np.ones((12,3,4)),None)
    projection = RuntimePlaneAxisValueProjection.preserve(axis=RuntimePlaneAxis.RUNTIME_SLICE,axis_size=12)
    def forbidden(*args, **kwargs):
        raise AssertionError("Prepared execution introspected a live callable")
    monkeypatch.setattr(inspect,"signature",forbidden)
    monkeypatch.setattr(callable_contract_module,"get_type_hints",forbidden)
    result = CellProfilerFunctionContractExecutor().execute(
        contract,raw,source,{},execution_mode=ImagePayloadExecutionMode.NATURAL,
        plane_projection=projection,
    )
    np.testing.assert_array_equal(result.data,np.full((12,3,4),2))
    assert calls == [(3,4)]*12


def test_authored_distinct_raw_abi_batch_has_no_runtime_queries_and_filters_controls(monkeypatch) -> None:
    from openhcs.core.processing_preparation import CallablePreparation
    calls = []
    def raw(image: np.ndarray, scale: int = 2) -> np.ndarray:
        calls.append(image.shape)
        return image * scale
    @wraps(raw)
    def wrapper(*args, **kwargs):
        return raw(*args, **kwargs)
    wrapper.__signature__ = inspect.signature(raw).replace(parameters=[
        *inspect.signature(raw).parameters.values(),
        inspect.Parameter("injected",inspect.Parameter.KEYWORD_ONLY,default=False),
    ])
    monkeypatch.setattr(CallablePreparation,"prepare",lambda self:None)
    contract = CallableContract.from_prepared_callable(wrapper)
    contract = replace(contract,metadata=replace(
        contract.metadata,processing_contract=ProcessingContract.PURE_2D,
        artifact_outputs=(ArtifactSpec.output("Result",ImageArtifactType),),
    ))
    source = ImagePayloadMetadata(plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,source_image_names=("DNA",)).payload_with(np.ones((12,3,4)),None)
    projection = RuntimePlaneAxisValueProjection.preserve(axis=RuntimePlaneAxis.RUNTIME_SLICE,axis_size=12)
    def forbidden(*args, **kwargs):
        raise AssertionError("Prepared authored raw target queried a live signature")
    monkeypatch.setattr(inspect,"signature",forbidden)
    monkeypatch.setattr(callable_contract_module,"get_type_hints",forbidden)
    result = CellProfilerFunctionContractExecutor().execute(
        contract,wrapper,source,{"injected":True},
        execution_mode=ImagePayloadExecutionMode.NATURAL,plane_projection=projection,
    )
    np.testing.assert_array_equal(result.data,np.full((12,3,4),2))
    assert calls == [(3,4)]*12


def test_compiled_slice_execution_resolves_raw_target_once_and_preserves_request_binding(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    @dataclass(frozen=True, slots=True)
    class ScaleRequest:
        image: object
        scale: int

    seen: list[tuple[int, ...]] = []

    @callable_request(ScaleRequest)
    def request_bound(request: ScaleRequest) -> object:
        data = request.image.data
        seen.append(data.shape)
        return data * request.scale

    @wraps(request_bound)
    def decorated(*args: object, **kwargs: object) -> object:
        raise AssertionError("CellProfiler invoked an outer runtime wrapper")

    contract = CallableContract.from_callable(decorated).with_prepared_signature()
    contract = replace(
        contract,
        metadata=replace(
            contract.metadata,
            processing_contract=ProcessingContract.PURE_2D,
        ),
    )
    raw_target = contract.resolve_canonical_raw_callable()
    resolve_raw = CallableContract.resolve_raw_runtime_callable
    resolutions: list[CallableContract] = []

    def resolve_once(self: CallableContract) -> Callable[..., object]:
        resolutions.append(self)
        return resolve_raw(self)

    def reject_reconstruction(*args: object, **kwargs: object) -> CallableContract:
        raise AssertionError("Runtime execution rebuilt its compiled contract")

    monkeypatch.setattr(CallableContract, "resolve_raw_runtime_callable", resolve_once)
    monkeypatch.setattr(CallableContract, "from_callable", reject_reconstruction)
    image = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE
    ).payload_with(np.ones((3, 4, 5), dtype=np.float32), None)

    result = CellProfilerFunctionContractExecutor().execute(
        contract,
        raw_target,
        image,
        {"scale": 4, "adapter_control": 17},
        execution_mode=ImagePayloadExecutionMode.NATURAL,
        plane_projection=RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE,
            axis_size=3,
        ),
    )

    assert resolutions == [contract]
    assert seen == [(4, 5)] * 3
    assert isinstance(result, RuntimeSliceAlignedValues)
    np.testing.assert_array_equal(
        np.stack(tuple(value.data for value in result.slices)),
        np.full((3, 4, 5), 4.0),
    )


@pytest.mark.parametrize("canonical_default", (False, True))
def test_flexible_dispatch_preserves_canonical_signature_control_defaults(
    canonical_default: bool,
) -> None:
    seen: list[tuple[tuple[int, ...], bool]] = []

    def raw(image: np.ndarray, *, slice_by_slice: bool = False) -> np.ndarray:
        seen.append((image.shape, slice_by_slice))
        return image

    @wraps(raw)
    def decorated(*args: object, **kwargs: object) -> object:
        raise AssertionError("CellProfiler invoked an outer runtime wrapper")

    signature = inspect.signature(raw)
    decorated.__signature__ = signature.replace(
        parameters=(
            parameter.replace(default=canonical_default)
            if parameter.name == "slice_by_slice"
            else parameter
            for parameter in signature.parameters.values()
        )
    )
    contract = _compiled_contract(decorated, ProcessingContract.FLEXIBLE)
    image = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE
    ).payload_with(np.ones((3, 4, 5), dtype=np.float32), None)

    CellProfilerFunctionContractExecutor().execute(
        contract,
        decorated,
        image,
        {},
        execution_mode=ImagePayloadExecutionMode.NATURAL,
        plane_projection=RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE,
            axis_size=3,
        ),
    )

    assert seen == (
        [((4, 5), True)] * 3
        if canonical_default
        else [((3, 4, 5), False)]
    )


@pytest.mark.parametrize("processing_contract", tuple(ProcessingContract))
@pytest.mark.parametrize(
    ("image_mode", "expected_call_count"),
    (
        (ImagePayloadExecutionMode.NATURAL, 1),
        (ImagePayloadExecutionMode.FULL_STACK, 1),
        (ImagePayloadExecutionMode.ALIGNED_MULTI_IMAGE_STACK, 2),
    ),
)
def test_executor_owns_the_closed_mode_processing_contract_matrix(
    processing_contract: ProcessingContract,
    image_mode: ImagePayloadExecutionMode,
    expected_call_count: int,
) -> None:
    calls: list[tuple[int, ...]] = []

    def dispatch_probe(image: np.ndarray) -> np.ndarray:
        calls.append(image.shape)
        if processing_contract is ProcessingContract.VOLUMETRIC_TO_SLICE:
            return image[0]
        return image

    callable_contract = _compiled_contract(dispatch_probe, processing_contract)
    image = (
        AlignedImageStack(
            slices=(
                np.zeros((2, 3), dtype=np.float32),
                np.ones((2, 3), dtype=np.float32),
            )
        )
        if image_mode is ImagePayloadExecutionMode.ALIGNED_MULTI_IMAGE_STACK
        else (
            ImagePayloadMetadata(
                plane_axis=RuntimePlaneAxis.RUNTIME_SLICE
            ).payload_with(np.zeros((2, 2, 3), dtype=np.float32), None)
            if processing_contract is ProcessingContract.VOLUMETRIC_TO_SLICE
            else np.zeros((2, 3), dtype=np.float32)
        )
    )

    if (
        image_mode is ImagePayloadExecutionMode.ALIGNED_MULTI_IMAGE_STACK
        and processing_contract is ProcessingContract.PURE_3D
    ):
        with pytest.raises(
            ValueError,
            match=(
                "DispatchProbeModule.*dispatch_probe.*"
                "PURE_3D.*RuntimePlaneAxis.SOURCE_BINDING"
            ),
        ):
            CellProfilerFunctionContractExecutor().execute(
                callable_contract,
                dispatch_probe,
                image,
                {},
                execution_mode=image_mode,
                plane_projection=RuntimePlaneAxisValueProjection.preserve(
                    axis=RuntimePlaneAxis.RUNTIME_SLICE,
                    axis_size=2,
                ),
            )
        assert calls == []
        return

    CellProfilerFunctionContractExecutor().execute(
        callable_contract,
        dispatch_probe,
        image,
        {},
        execution_mode=image_mode,
        plane_projection=(
            RuntimePlaneAxisValueProjection.preserve(
                axis=RuntimePlaneAxis.RUNTIME_SLICE,
                axis_size=2,
            )
            if image_mode is ImagePayloadExecutionMode.ALIGNED_MULTI_IMAGE_STACK
            else None
        ),
    )

    assert len(calls) == expected_call_count


def test_aligned_pure_2d_consumes_unique_declared_source_binding_plane() -> None:
    calls: list[tuple[int, ...]] = []

    def dispatch_probe(image: np.ndarray) -> np.ndarray:
        calls.append(image.shape)
        return image

    image_spec = ArtifactSpec.input("DNA", ImageArtifactType)
    callable_contract = _compiled_contract(
        dispatch_probe,
        ProcessingContract.PURE_2D,
        artifact_inputs=(image_spec,),
    )
    source_stack = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/tmp/site-1.tif", "/tmp/site-2.tif"),
            component_metadata=(({"site": "1"}), ({"site": "2"})),
        ),
    ).payload_with(
        np.stack(
            (
                np.zeros((2, 3), dtype=np.float32),
                np.ones((2, 3), dtype=np.float32),
            )
        ),
        None,
    )
    composition = compose_aligned_image_payload(
        "DispatchProbeModule image inputs ('DNA',)",
        (source_stack,),
    )

    CellProfilerFunctionContractExecutor().execute(
        callable_contract,
        dispatch_probe,
        composition.payload,
        {},
        execution_mode=composition.execution_mode,
        plane_projection=RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE,
            axis_size=2,
        ),
    )

    assert calls == [(2, 3), (2, 3)]


def test_declared_unaligned_input_joins_runtime_slices_before_pure_2d_execution() -> (
    None
):
    calls: list[tuple[int, ...]] = []

    def dispatch_probe(image: object) -> np.ndarray:
        data = np.asarray(image.data)
        calls.append(data.shape)
        return data[0] - data[1]

    spatial_domain = SourceSpatialDomain(source_shape_yx=(2, 3))
    source_stack = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_spatial_domain=spatial_domain,
        source_image_names=("Raw", "Raw"),
    ).payload_with(
        np.stack(
            (
                np.full((2, 3), 11, dtype=np.float32),
                np.full((2, 3), 22, dtype=np.float32),
            )
        ),
        None,
    )
    illumination = ImagePayloadMetadata(
        source_spatial_domain=spatial_domain,
        source_image_names=("Illum",),
    ).payload_with(np.full((2, 3), 3, dtype=np.float32), None)

    with pytest.raises(ValueError, match="explicit runtime-slice owner"):
        compose_aligned_image_payload(
            "DispatchProbeModule image inputs ('Raw', 'Illum')",
            (source_stack, illumination),
        )

    composition = compose_aligned_image_payload(
        "DispatchProbeModule image inputs ('Raw', 'Illum')",
        (source_stack, illumination),
        stack_broadcast_source_indices=(None, 0),
    )
    output_spec = ArtifactSpec.output("Corrected", ImageArtifactType)
    callable_contract = _compiled_contract(
        dispatch_probe,
        ProcessingContract.PURE_2D,
        artifact_outputs=(output_spec,),
    )
    projection = RuntimePlaneAxisValueProjection.preserve(
        axis=RuntimePlaneAxis.RUNTIME_SLICE,
        axis_size=2,
        source_aliases=("Raw", "Illum"),
    )

    result = CellProfilerFunctionContractExecutor().execute(
        callable_contract,
        dispatch_probe,
        composition.payload,
        {},
        execution_mode=composition.execution_mode,
        plane_projection=projection,
    )

    assert calls == [(2, 2, 3), (2, 2, 3)]
    np.testing.assert_array_equal(
        result.data,
        np.stack(
            (
                np.full((2, 3), 8, dtype=np.float32),
                np.full((2, 3), 19, dtype=np.float32),
            )
        ),
    )


@pytest.mark.parametrize(
    "processing_contract",
    (ProcessingContract.PURE_2D, ProcessingContract.PURE_3D),
)
def test_aligned_execution_preserves_each_slice_inner_source_binding_axis(
    processing_contract: ProcessingContract,
) -> None:
    calls: list[tuple[int, ...]] = []

    def dispatch_probe(image: np.ndarray) -> np.ndarray:
        calls.append(image.shape)
        return image[0]

    pair = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.SOURCE_BINDING,
        source_image_names=("Orig", "Illum"),
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/tmp/orig.tif", "/tmp/illum.pkl"),
        ),
    ).payload_with(np.zeros((2, 2, 3), dtype=np.float32), None)
    callable_contract = _compiled_contract(
        dispatch_probe,
        processing_contract,
    )

    CellProfilerFunctionContractExecutor().execute(
        callable_contract,
        dispatch_probe,
        AlignedImageStack(slices=(pair, pair)),
        {},
        execution_mode=ImagePayloadExecutionMode.ALIGNED_MULTI_IMAGE_STACK,
        plane_projection=RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE,
            axis_size=2,
        ),
    )

    assert calls == [(2, 2, 3), (2, 2, 3)]


def test_aligned_stack_type_mismatch_fails_before_raw_invocation() -> None:
    calls = 0

    def dispatch_probe(image: np.ndarray) -> np.ndarray:
        nonlocal calls
        calls += 1
        return image

    callable_contract = _compiled_contract(
        dispatch_probe,
        ProcessingContract.PURE_2D,
    )

    with pytest.raises(
        TypeError,
        match="DispatchProbeModule.*dispatch_probe.*AlignedImageStack.*ndarray",
    ):
        CellProfilerFunctionContractExecutor().execute(
            callable_contract,
            dispatch_probe,
            np.zeros((2, 3), dtype=np.float32),
            {},
            execution_mode=ImagePayloadExecutionMode.ALIGNED_MULTI_IMAGE_STACK,
            plane_projection=RuntimePlaneAxisValueProjection.preserve(
                axis=RuntimePlaneAxis.RUNTIME_SLICE,
                axis_size=2,
            ),
        )

    assert calls == 0


def test_aligned_stack_requires_exact_compiled_runtime_slice_projection() -> None:
    calls = 0

    def dispatch_probe(image: np.ndarray) -> np.ndarray:
        nonlocal calls
        calls += 1
        return image

    callable_contract = _compiled_contract(
        dispatch_probe,
        ProcessingContract.PURE_2D,
    )
    image = AlignedImageStack(
        slices=(
            np.zeros((2, 3), dtype=np.float32),
            np.ones((2, 3), dtype=np.float32),
        )
    )

    with pytest.raises(
        ValueError,
        match="compiled runtime-slice projection",
    ):
        CellProfilerFunctionContractExecutor().execute(
            callable_contract,
            dispatch_probe,
            image,
            {},
            execution_mode=ImagePayloadExecutionMode.ALIGNED_MULTI_IMAGE_STACK,
        )

    with pytest.raises(
        ValueError,
        match="cardinality.*2 != 3",
    ):
        CellProfilerFunctionContractExecutor().execute(
            callable_contract,
            dispatch_probe,
            image,
            {},
            execution_mode=ImagePayloadExecutionMode.ALIGNED_MULTI_IMAGE_STACK,
            plane_projection=RuntimePlaneAxisValueProjection.preserve(
                axis=RuntimePlaneAxis.RUNTIME_SLICE,
                axis_size=3,
            ),
        )

    assert calls == 0


def test_aligned_stack_projects_runtime_plane_projection_kwarg_nominally() -> None:
    received: list[RuntimePlaneAxisValueProjection] = []

    def dispatch_probe(
        image: np.ndarray,
        *,
        runtime_plane_projection: RuntimePlaneAxisValueProjection,
    ) -> np.ndarray:
        received.append(runtime_plane_projection)
        return image

    callable_contract = _compiled_contract(
        dispatch_probe,
        ProcessingContract.PURE_2D,
    )
    preserved = RuntimePlaneAxisValueProjection.preserve(
        axis=RuntimePlaneAxis.RUNTIME_SLICE,
        axis_size=2,
    )

    CellProfilerFunctionContractExecutor().execute(
        callable_contract,
        dispatch_probe,
        AlignedImageStack(
            slices=(
                np.zeros((2, 3), dtype=np.float32),
                np.ones((2, 3), dtype=np.float32),
            )
        ),
        {"runtime_plane_projection": preserved},
        execution_mode=ImagePayloadExecutionMode.ALIGNED_MULTI_IMAGE_STACK,
        plane_projection=preserved,
    )

    assert received == [preserved.selected_plane(0), preserved.selected_plane(1)]


@pytest.mark.parametrize(
    "execution_mode",
    (ImagePayloadExecutionMode.NATURAL, ImagePayloadExecutionMode.FULL_STACK),
)
def test_declared_output_axis_contextualizes_multiple_canonical_outputs(
    execution_mode: ImagePayloadExecutionMode,
) -> None:
    trailing = (
        AlignShiftMeasurement(
            slice_index=0,
            output_index=0,
            x_shift=1.0,
            y_shift=2.0,
        ),
    )

    def dispatch_probe(
        image: np.ndarray,
    ) -> tuple[object, tuple[AlignShiftMeasurement, ...]]:
        outputs = np.stack((np.asarray(image) + 1, np.asarray(image) + 2))
        return (
            ImagePayloadMetadata(
                plane_axis=RuntimePlaneAxis.RUNTIME_SLICE
            ).payload_with(outputs, None),
            trailing,
        )

    callable_contract = _compiled_contract(
        dispatch_probe,
        ProcessingContract.PURE_3D,
        artifact_outputs=(
            ArtifactSpec.output("First", ImageArtifactType),
            ArtifactSpec.output("Second", ImageArtifactType),
            ArtifactSpec.output("Measurements", MeasurementsArtifactType),
        ),
    )
    source = np.arange(6, dtype=np.float32).reshape((2, 3))

    result = CellProfilerFunctionContractExecutor().execute(
        callable_contract,
        dispatch_probe,
        source,
        {},
        execution_mode=execution_mode,
        plane_projection=RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE,
            axis_size=2,
        ),
    )

    assert isinstance(result, tuple)
    outputs, returned_trailing = result
    assert isinstance(outputs, ImageOutputBundle)
    assert tuple(context.output_key for context in outputs.slice_contexts) == (
        "First",
        "Second",
    )
    np.testing.assert_array_equal(outputs.slices[0].data, source + 1)
    np.testing.assert_array_equal(outputs.slices[1].data, source + 2)
    assert returned_trailing == trailing


def test_multi_canonical_output_rejects_undeclared_array_axis() -> None:
    def dispatch_probe(image: np.ndarray) -> np.ndarray:
        return np.stack((np.asarray(image) + 1, np.asarray(image) + 2))

    callable_contract = _compiled_contract(
        dispatch_probe,
        ProcessingContract.PURE_3D,
        artifact_outputs=(
            ArtifactSpec.output("First", ImageArtifactType),
            ArtifactSpec.output("Second", ImageArtifactType),
        ),
    )

    with pytest.raises(
        RuntimeSliceProjectionDeclarationError,
        match="returned payload does not declare the compiled 'runtime_slice' plane axis",
    ):
        CellProfilerFunctionContractExecutor().execute(
            callable_contract,
            dispatch_probe,
            np.zeros((2, 3), dtype=np.float32),
            {},
            execution_mode=ImagePayloadExecutionMode.FULL_STACK,
            plane_projection=RuntimePlaneAxisValueProjection.preserve(
                axis=RuntimePlaneAxis.RUNTIME_SLICE,
                axis_size=2,
            ),
        )


def test_multi_canonical_output_requires_exact_projection_cardinality() -> None:
    def dispatch_probe(image: np.ndarray) -> object:
        outputs = np.stack(
            tuple(np.asarray(image) + output_index for output_index in range(3))
        )
        return ImagePayloadMetadata(
            plane_axis=RuntimePlaneAxis.RUNTIME_SLICE
        ).payload_with(outputs, None)

    callable_contract = _compiled_contract(
        dispatch_probe,
        ProcessingContract.PURE_3D,
        artifact_outputs=(
            ArtifactSpec.output("First", ImageArtifactType),
            ArtifactSpec.output("Second", ImageArtifactType),
        ),
    )

    with pytest.raises(
        ValueError,
        match="declares 2 canonical outputs.*projection declares 3 value",
    ):
        CellProfilerFunctionContractExecutor().execute(
            callable_contract,
            dispatch_probe,
            np.zeros((2, 3), dtype=np.float32),
            {},
            execution_mode=ImagePayloadExecutionMode.FULL_STACK,
            plane_projection=RuntimePlaneAxisValueProjection.preserve(
                axis=RuntimePlaneAxis.RUNTIME_SLICE,
                axis_size=3,
            ),
        )


@pytest.mark.parametrize("runtime_slice_count", (1, 2))
def test_aligned_stack_transposes_multiple_canonical_outputs_across_runtime_slices(
    runtime_slice_count: int,
) -> None:
    def dispatch_probe(
        image: np.ndarray,
    ) -> tuple[AlignedImageStack, tuple[AlignShiftMeasurement, ...]]:
        return (
            AlignedImageStack(
                tuple(np.asarray(image) + output_index for output_index in range(3))
            ),
            (
                AlignShiftMeasurement(
                    slice_index=0,
                    output_index=0,
                    x_shift=float(np.asarray(image)[0, 0]),
                    y_shift=0.0,
                ),
            ),
        )

    output_specs = (
        *(
            ArtifactSpec.output(f"Aligned{index}", ImageArtifactType)
            for index in range(3)
        ),
        ArtifactSpec.output("Measurements", MeasurementsArtifactType),
    )
    callable_contract = _compiled_contract(
        dispatch_probe,
        ProcessingContract.PURE_2D,
        artifact_outputs=output_specs,
    )
    runtime_slices = tuple(
        np.full((2, 3), slice_index * 10, dtype=np.float32)
        for slice_index in range(runtime_slice_count)
    )

    result = CellProfilerFunctionContractExecutor().execute(
        callable_contract,
        dispatch_probe,
        AlignedImageStack(runtime_slices),
        {},
        execution_mode=ImagePayloadExecutionMode.ALIGNED_MULTI_IMAGE_STACK,
        plane_projection=RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE,
            axis_size=runtime_slice_count,
        ),
    )

    assert isinstance(result, tuple)
    aligned_outputs = result[0]
    assert isinstance(aligned_outputs, AlignedImageStack)
    assert len(aligned_outputs.slices) == 3
    for output_index, output in enumerate(aligned_outputs.slices):
        expected = tuple(value + output_index for value in runtime_slices)
        np.testing.assert_array_equal(output.data, np.stack(expected))


def test_aligned_stack_preserves_one_scalar_output_per_declared_surface() -> None:
    def dispatch_probe(image: np.ndarray) -> np.ndarray:
        return np.asarray(image) + 1

    output_specs = tuple(
        ArtifactSpec.output(f"Corrected{index}", ImageArtifactType)
        for index in range(2)
    )
    callable_contract = _compiled_contract(
        dispatch_probe,
        ProcessingContract.PURE_2D,
        artifact_outputs=output_specs,
    )
    input_surfaces = (
        np.zeros((2, 3), dtype=np.float32),
        np.full((2, 3), 10, dtype=np.float32),
    )

    result = CellProfilerFunctionContractExecutor().execute(
        callable_contract,
        dispatch_probe,
        AlignedImageStack(input_surfaces),
        {},
        execution_mode=ImagePayloadExecutionMode.ALIGNED_MULTI_IMAGE_STACK,
        plane_projection=RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE,
            axis_size=2,
        ),
    )

    assert isinstance(result, AlignedImageStack)
    assert len(result.slices) == 2
    for output, source in zip(result.slices, input_surfaces, strict=True):
        np.testing.assert_array_equal(output.data, source + 1)


def test_aligned_stack_aggregates_one_canonical_output_for_one_runtime_slice() -> None:
    def dispatch_probe(image: np.ndarray) -> np.ndarray:
        return np.asarray(image)[0] + np.asarray(image)[1]

    callable_contract = _compiled_contract(
        dispatch_probe,
        ProcessingContract.PURE_2D,
        artifact_outputs=(ArtifactSpec.output("Combined", ImageArtifactType),),
    )
    first = np.full((2, 3), 2, dtype=np.float32)
    second = np.full((2, 3), 3, dtype=np.float32)

    result = CellProfilerFunctionContractExecutor().execute(
        callable_contract,
        dispatch_probe,
        AlignedImageStack((np.stack((first, second)),)),
        {},
        execution_mode=ImagePayloadExecutionMode.ALIGNED_MULTI_IMAGE_STACK,
        plane_projection=RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE,
            axis_size=1,
        ),
    )

    assert not isinstance(result, AlignedImageStack)
    np.testing.assert_array_equal(
        result.data,
        np.full((1, 2, 3), 5, dtype=np.float32),
    )


def test_aligned_stack_unwraps_one_declared_surface_after_slice_transpose() -> None:
    def dispatch_probe(image: np.ndarray) -> AlignedImageStack:
        return AlignedImageStack((np.asarray(image) + 1,))

    callable_contract = _compiled_contract(
        dispatch_probe,
        ProcessingContract.PURE_2D,
        artifact_outputs=(ArtifactSpec.output("Corrected", ImageArtifactType),),
    )
    runtime_slices = (
        np.zeros((2, 3), dtype=np.float32),
        np.full((2, 3), 10, dtype=np.float32),
    )

    result = CellProfilerFunctionContractExecutor().execute(
        callable_contract,
        dispatch_probe,
        AlignedImageStack(runtime_slices),
        {},
        execution_mode=ImagePayloadExecutionMode.ALIGNED_MULTI_IMAGE_STACK,
        plane_projection=RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE,
            axis_size=2,
        ),
    )

    assert not isinstance(result, AlignedImageStack)
    np.testing.assert_array_equal(
        result.data,
        np.stack(tuple(value + 1 for value in runtime_slices)),
    )


def test_aligned_stack_rejects_canonical_output_surface_count_mismatch() -> None:
    def dispatch_probe(image: np.ndarray) -> AlignedImageStack:
        return AlignedImageStack((np.asarray(image), np.asarray(image)))

    output_specs = tuple(
        ArtifactSpec.output(f"Aligned{index}", ImageArtifactType) for index in range(3)
    )
    callable_contract = _compiled_contract(
        dispatch_probe,
        ProcessingContract.PURE_2D,
        artifact_outputs=output_specs,
    )

    with pytest.raises(
        ValueError,
        match="dispatch_probe produced 2 aligned main-flow value.*3 declared output",
    ):
        CellProfilerFunctionContractExecutor().execute(
            callable_contract,
            dispatch_probe,
            AlignedImageStack((np.zeros((2, 3), dtype=np.float32),)),
            {},
            execution_mode=ImagePayloadExecutionMode.ALIGNED_MULTI_IMAGE_STACK,
            plane_projection=RuntimePlaneAxisValueProjection.preserve(
                axis=RuntimePlaneAxis.RUNTIME_SLICE,
                axis_size=1,
            ),
        )


def test_raw_callable_mismatch_fails_before_invocation() -> None:
    calls = 0

    def compiled_probe(image: np.ndarray) -> np.ndarray:
        return image

    def substituted_probe(image: np.ndarray) -> np.ndarray:
        nonlocal calls
        calls += 1
        return image

    callable_contract = _compiled_contract(
        compiled_probe,
        ProcessingContract.PURE_2D,
    )

    with pytest.raises(
        ValueError,
        match="DispatchProbeModule.*dispatch_probe",
    ):
        CellProfilerFunctionContractExecutor().execute(
            callable_contract,
            substituted_probe,
            np.zeros((2, 3), dtype=np.float32),
            {},
            execution_mode=ImagePayloadExecutionMode.NATURAL,
        )

    assert calls == 0


def test_full_stack_pure_3d_rejects_slice_aligned_kwargs_before_invocation() -> None:
    calls = 0

    def dispatch_probe(image: np.ndarray, *, labels: object) -> np.ndarray:
        nonlocal calls
        calls += 1
        del labels
        return image

    callable_contract = _compiled_contract(
        dispatch_probe,
        ProcessingContract.PURE_3D,
    )

    with pytest.raises(
        ValueError,
        match=(
            "DispatchProbeModule.*dispatch_probe.*PURE_3D.*"
            "runtime-slice-aligned kwargs.*labels"
        ),
    ):
        CellProfilerFunctionContractExecutor().execute(
            callable_contract,
            dispatch_probe,
            np.zeros((2, 3), dtype=np.float32),
            {"labels": RuntimeSliceAlignedValues(slices=(1, 2))},
            execution_mode=ImagePayloadExecutionMode.FULL_STACK,
        )

    assert calls == 0
