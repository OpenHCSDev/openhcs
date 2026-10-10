"""Synthetic public RescaleIntensity declaration -> producer -> native binding."""

from dataclasses import replace

import numpy as np
import pytest
from polystore.streaming.identity import StreamProducerIdentity
from polystore.streaming_constants import StreamingDataType
from zmqruntime.viewer_protocol import ViewerWireField

from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_slice_projection import RuntimeProjectionSourceIdentityRequest
from openhcs.core.runtime_stores import RuntimeValueStore
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.function_patterns import InvocationArtifactInputEdgePlan
from openhcs.core.runtime_object_label_building import SourceImageObjectLabelBuildRequest
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis, RuntimePlaneAxisValueProjection
from openhcs.core.runtime_object_label_domains import ObjectLabelDomainScope
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.config import StepSourceBindingsConfig
from openhcs.core.source_bindings import NamedSourceBinding
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.source_metadata import SourceVoxelSpacing, SourceVoxelSpacingUnit
from openhcs.core.steps.function_outputs import StreamOutputBatch
from openhcs.core.steps.function_step import FunctionStep
from openhcs.core.steps.stream_component_semantics import StreamImagePayloadMetadataProjector
from openhcs.processing.backends.cellprofiler.intensity import (
    AutomaticHigh, AutomaticLow, RescaleIntensityModule, RescaleMethod, rescale_intensity,
)
from openhcs.processing.backends.cellprofiler.shape import measure_object_size_shape
from openhcs.interop.cellprofiler.runtime.adapter import CellProfilerRuntimeAdapter
from openhcs.interop.cellprofiler.runtime.module_execution import CellProfilerModuleExecutor
from openhcs.interop.cellprofiler.runtime.function_contract_execution import CellProfilerFunctionContractExecutor
from openhcs.runtime.napari_streaming_handlers import (
    NapariAggregateAxisBindingAuthority, NapariStreamLayerAddress, NapariStreamLayerItem,
)
from openhcs.runtime.viewer_component_system import (
    ViewerComponentAxisSemanticsAuthority, ViewerComponentValueDomainPayload,
)

# Reuse the original provider-free compiler and runtime fixtures, not a second ABI.
from test_cellprofiler_generic_special_input_binding import _compile_public_step
from tests.unit.cellprofiler_runtime_test_support import (
    cellprofiler_runtime_adapter_for_test,
)


@pytest.mark.parametrize("method", [RescaleMethod.DIVIDE_BY_VALUE, RescaleMethod.MANUAL_INPUT_RANGE])
@pytest.mark.parametrize("matching", [None, "Bright", "Other"])
def test_public_rescale_preserves_one_source_plane_through_stream_binding(method, matching):
    kwargs = {
        "select_the_input_image": "Bright", "name_the_output_image": "Detection",
        "rescale_method": method, "automatic_low": AutomaticLow.CUSTOM,
        "automatic_high": AutomaticHigh.CUSTOM, "source_low": 0.0,
        "source_high": 20.0, "divisor_value": 2.0,
    }
    if matching is not None:
        kwargs["select_image_to_match_in_maximum_intensity"] = matching
    step = FunctionStep(
        func=(rescale_intensity, kwargs), name="SyntheticRescale",
        source_bindings=StepSourceBindingsConfig(
            enabled=True, bindings=(NamedSourceBinding("Bright"),),
        ),
    )
    invocation = _compile_public_step(step)
    contract = replace(
        invocation.contract,
        metadata=replace(
            invocation.contract.metadata,
            runtime_adapter=CellProfilerRuntimeAdapter.runtime_adapter_spec(),
        ),
    )
    pixels = np.arange(20, dtype=np.float32).reshape(4, 5)
    metadata = ImagePayloadMetadata(
        source_path="/synthetic/A01_s1_w1_z1_t1.tif",
        source_component_metadata={"well": "A01", "site": "1", "channel": "1", "z_index": "1", "timepoint": "1"},
        source_image_names=("Bright",),
        source_voxel_spacing=SourceVoxelSpacing((1.0, 1.0, 1.0), SourceVoxelSpacingUnit.RELATIVE),
        source_spatial_domain=SourceSpatialDomain(origin_yx=(0, 0), source_shape_yx=(4, 5)),
    )
    source = metadata.payload_with(pixels, None)
    runtime = cellprofiler_runtime_adapter_for_test(
        runtime_value_store=RuntimeValueStore(), callable_contract=contract,
        axis_scope=RuntimeExecutionAxisScope.from_raw("synthetic", component=None, value=None),
        artifact_inputs={
            edge.key: InvocationArtifactInputEdgePlan.from_source_declarations(
                key=edge.key, spec=edge.spec,
                main_flow_artifacts=contract.artifact_inputs,
                invocation_sources=contract.artifact_inputs,
            )
            for edge in invocation.artifact_input_edges
        },
    )
    executor = CellProfilerModuleExecutor(rescale_intensity, contract)
    request = executor._image_request(
        source, runtime, module_type=RescaleIntensityModule,
        active_input_specs=contract.artifact_inputs.specs,
    )
    execution = executor._invocation_request(
        image_request=request, adapter=runtime, current_image=source,
        module_type=RescaleIntensityModule,
        kwargs={"rescale_method": method, "automatic_low": AutomaticLow.CUSTOM,
                "automatic_high": AutomaticHigh.CUSTOM, "source_low": 0.0,
                "source_high": 20.0, "divisor_value": 2.0},
    )
    result = CellProfilerFunctionContractExecutor().execute(
        contract, rescale_intensity, execution.payload, execution.kwargs,
        execution_mode=execution.execution_mode, plane_projection=execution.plane_projection,
    )
    (item,) = tuple(StreamOutputBatch.project_item(RuntimeProjectionSourceIdentityRequest(
        value=result, source_description="/synthetic/Detection.tif",
    )))
    fields = StreamImagePayloadMetadataProjector.item_fields(item.metadata, ("well", "site", "channel", "z_index", "timepoint"))
    native_item = NapariStreamLayerItem(
        data=item.data,
        producer=StreamProducerIdentity.pipeline_output(
            output_kind="main", output_key="main", projection_key="main",
            step_name="SyntheticRescale", pipeline_position=0, step_scope_id="synthetic",
        ),
        address=NapariStreamLayerAddress(
            components=dict(item.require_source_component_metadata()),
            path="/synthetic/Detection.tif", stream_layer_data_type=StreamingDataType.IMAGE,
        ),
        image_metadata=item.metadata,
        plane_component_domain=ViewerComponentValueDomainPayload.from_wire_mapping(
            fields.get(ViewerWireField.PLANE_COMPONENT_VALUES.value, {}), context="synthetic producer fields",
        ),
    )
    # The exact original strict receiver is reached, not replaced by a mock.
    NapariAggregateAxisBindingAuthority.bindings((native_item,), ViewerComponentAxisSemanticsAuthority.empty())
    assert contract.artifact_inputs.names() == ("Bright",)
    assert request.image_count == 1
    assert result.data.shape == (4, 5)
    assert result.metadata.source_spatial_domain == metadata.source_spatial_domain
    assert result.metadata.source_image_paths == metadata.source_image_paths
    assert result.metadata.source_voxel_spacing == metadata.source_voxel_spacing
    assert SourceVoxelSpacing.common_physical_pixel_size((result.metadata.source_voxel_spacing,)) is None
    assert item.require_source_component_metadata() == metadata.source_component_metadata
    expected = pixels / (2.0 if method is RescaleMethod.DIVIDE_BY_VALUE else 20.0)
    np.testing.assert_array_equal(item.data, expected)


@pytest.mark.parametrize("retained_site", [False, True])
def test_declared_source_plane_has_area_not_volume(retained_site):
    pixels = np.ones((4, 5), dtype=np.float32)
    labels = np.zeros((4, 5), dtype=np.int32)
    labels[1:3, 1:4] = 1
    metadata = ImagePayloadMetadata(
        source_path="/synthetic/site.tif",
        source_component_metadata={"site": "7"},
        source_spatial_domain=SourceSpatialDomain(origin_yx=(0, 0), source_shape_yx=(4, 5)),
    )
    if retained_site:
        pixels = pixels[None]
        labels = labels[None]
        metadata = ImagePayloadMetadata(
            source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
                paths=("/synthetic/site.tif",), component_metadata=({"site": "7"},),
            ),
            source_spatial_domain=metadata.source_spatial_domain,
            plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        )
    payload = metadata.payload_with(pixels, None)
    objects = SourceImageObjectLabelBuildRequest(
        image=payload,
        labels=labels,
        domain_scope=ObjectLabelDomainScope.PLANE if retained_site else None,
        plane_projection=(
            RuntimePlaneAxisValueProjection.from_source_declaration(
                metadata.plane_axis, metadata.source_provenance,
            )
            if retained_site else None
        ),
    ).payload()
    assert objects.plane_axis is (
        RuntimePlaneAxis.RUNTIME_SLICE if retained_site else None
    )
    assert objects.object_label_domain().scope is (
        ObjectLabelDomainScope.PLANE if retained_site else ObjectLabelDomainScope.PAYLOAD
    )
    _, rows = measure_object_size_shape.__wrapped__(
        payload, objects, calculate_advanced=False, calculate_zernikes=False,
    )
    fields = tuple(field.name for field in rows.fields)
    assert "Area" in fields
    assert "Volume" not in fields
    assert "SurfaceArea" not in fields
    assert tuple(row["Area"] for row in rows) == (6.0,)


def test_real_volume_is_not_squeezed_or_relabelled_as_area():
    pixels = np.ones((3, 4, 5), dtype=np.float32)
    labels = np.zeros_like(pixels, dtype=np.int32)
    labels[1:, 1:3, 1:4] = 1
    payload = ImagePayloadMetadata(source_path="/synthetic/volume.tif").payload_with(pixels, None)
    objects = SourceImageObjectLabelBuildRequest(image=payload, labels=labels).payload()
    _, rows = measure_object_size_shape.__wrapped__(
        payload, objects, calculate_advanced=False, calculate_zernikes=False,
    )
    fields = tuple(field.name for field in rows.fields)
    assert "Volume" in fields
    assert "Area" not in fields
    assert tuple(row["Volume"] for row in rows) == (12.0,)
