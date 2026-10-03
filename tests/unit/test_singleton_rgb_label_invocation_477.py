"""Scalar RGB invocations consume only an explicitly declared singleton root."""
import numpy as np
import pytest

from openhcs.core.artifacts import ArtifactSpec, ImageArtifactType, ObjectLabelsArtifactType
from openhcs.core.aligned_image_payload import ImagePayloadExecutionMode
from openhcs.core.function_contract_metadata import FunctionContractAttribute
from openhcs.core.pipeline.function_contracts import ObjectLabelInputExecutionMode
from openhcs.core.runtime_image_values import ImageMetadataPayload, ImagePayloadMetadata
from openhcs.core.runtime_object_label_domains import ObjectLabelDomain, ObjectLabelDomainScope
from openhcs.core.runtime_object_labels import ObjectLabelSet, ObjectLabelVariantData, object_label_dense_array
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis, RuntimePlaneProjection
from openhcs.core.runtime_slice_projection import RuntimeSliceProjectionDeclarationError
from openhcs.interop.cellprofiler.runtime.function_contract_execution import CellProfilerFunctionContractExecutor
from openhcs.processing.backends.cellprofiler.outlines import OverlayOutlinesModule
from tests.unit.test_cellprofiler_module_execution import (
    _FakeCellProfilerRuntime,
    _artifact_input_edge_for_test,
    _compiled_callable_contract,
    _module_executor,
)


def _invocation_case(*, root_count=1, label_count=1):
    image_spec = ArtifactSpec.input('GFPandDNA', ImageArtifactType)
    labels_spec = ArtifactSpec.input('Nuclei', ObjectLabelsArtifactType)
    raw = OverlayOutlinesModule.require_callable()
    contract = _compiled_callable_contract(raw, artifact_inputs=(image_spec, labels_spec))
    data = np.linspace(0, 1, 8 * 9 * 3, dtype=np.float32).reshape(8, 9, 3)
    image = ImageMetadataPayload(data, ImagePayloadMetadata(source_channel_axis=2, source_image_names=('GFPandDNA',)))
    label_data = np.zeros((label_count, 8, 9), dtype=np.int32)
    label_data[:, 2:5, 3:6] = 1
    labels = ObjectLabelSet(
        name='Nuclei', variant_data=ObjectLabelVariantData(labels=label_data),
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        domain=ObjectLabelDomain(declared_object_id_domains=((1,),) * label_count, scope=ObjectLabelDomainScope.PLANE),
    )
    adapter = _FakeCellProfilerRuntime(
        {'GFPandDNA': image}, objects={'Nuclei': labels}, callable_contract=contract,
        artifact_input_edges=tuple(_artifact_input_edge_for_test(spec) for spec in (image_spec, labels_spec)),
        plane_projection=RuntimePlaneProjection.stack(root_count),
    )
    executor = _module_executor(contract)
    request = executor._image_request(image, adapter, module_type=OverlayOutlinesModule, active_input_specs=(image_spec, labels_spec))
    return raw, contract, image, labels, adapter, executor, request


def _bind(case):
    raw, contract, image, labels, adapter, executor, request = case
    return executor._invocation_request(
        image_request=request, adapter=adapter, current_image=image,
        kwargs={'outline_colors': ('#21FFFF',)}, module_type=OverlayOutlinesModule,
    )


def _execute(case, invocation):
    raw, contract, *_ = case
    return CellProfilerFunctionContractExecutor().execute(
        contract, raw, invocation.payload, invocation.kwargs,
        execution_mode=invocation.execution_mode, plane_projection=invocation.plane_projection,
    )


def test_match_image_labels_consume_declared_singleton_root_for_scalar_rgb():
    case = _invocation_case()
    raw, contract, image, labels, *_ = case
    image_before = image.data.copy()
    labels_before = object_label_dense_array(labels).copy()
    invocation = _bind(case)
    selected = invocation.kwargs['object_labels'][0]
    assert invocation.execution_mode is ImagePayloadExecutionMode.NATURAL
    assert invocation.plane_projection is None
    assert invocation.payload.metadata.source_channel_axis == 2
    assert selected.plane_axis is None
    assert object_label_dense_array(selected).shape == (8, 9)
    output = _execute(case, invocation)
    scalar_labels = ObjectLabelSet(name='Nuclei', variant_data=ObjectLabelVariantData(labels=labels_before[0]), domain=ObjectLabelDomain(declared_object_ids=(1,), scope=ObjectLabelDomainScope.PAYLOAD))
    expected = raw(image, object_labels=(scalar_labels,), outline_colors=('#21FFFF',))
    np.testing.assert_array_equal(output.data, expected.data)
    np.testing.assert_array_equal(image.data, image_before)
    np.testing.assert_array_equal(object_label_dense_array(labels), labels_before)
    assert labels.plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
    assert image.metadata.plane_axis is None


@pytest.mark.parametrize('root_count', (None, 2))
def test_scalar_rgb_cannot_authorize_unknown_or_multiple_root_planes(root_count):
    case = _invocation_case(root_count=root_count)
    invocation = _bind(case)
    assert invocation.kwargs['object_labels'][0].plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
    with pytest.raises(RuntimeSliceProjectionDeclarationError, match='Kwargs cannot create image-axis execution semantics'):
        _execute(case, invocation)


def test_explicit_full_stack_label_contract_preserves_scalar_boundary_refusal(monkeypatch):
    raw = OverlayOutlinesModule.require_callable()
    monkeypatch.setattr(raw, FunctionContractAttribute.object_label_input_execution_mode, ObjectLabelInputExecutionMode.FULL_STACK)
    case = _invocation_case()
    invocation = _bind(case)
    assert invocation.kwargs['object_labels'][0].plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
    with pytest.raises(RuntimeSliceProjectionDeclarationError, match='Kwargs cannot create image-axis execution semantics'):
        _execute(case, invocation)


def test_declared_singleton_root_refuses_mismatched_label_cardinality():
    case = _invocation_case(label_count=2)
    with pytest.raises(ValueError, match='Object-label runtime plane-axis cardinality mismatch'):
        _bind(case)


def test_final_module_mode_sees_full_labels_before_scalar_projection(monkeypatch):
    case = _invocation_case()
    def mode(cls, default, *, image, kwargs, variable_components):
        assert kwargs['object_labels'][0].plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
        assert object_label_dense_array(kwargs['object_labels'][0]).shape == (1, 8, 9)
        return ImagePayloadExecutionMode.FULL_STACK
    monkeypatch.setattr(OverlayOutlinesModule, 'execution_mode', classmethod(mode))
    invocation = _bind(case)
    assert invocation.execution_mode is ImagePayloadExecutionMode.FULL_STACK
    assert invocation.kwargs['object_labels'][0].plane_axis is RuntimePlaneAxis.RUNTIME_SLICE


def test_module_mode_failure_precedes_projection_guard(monkeypatch):
    case = _invocation_case(label_count=2)
    error = RuntimeError('module image-domain selection failed')
    def mode(cls, default, *, image, kwargs, variable_components):
        raise error
    monkeypatch.setattr(OverlayOutlinesModule, 'execution_mode', classmethod(mode))
    with pytest.raises(RuntimeError) as caught:
        _bind(case)
    assert caught.value is error
