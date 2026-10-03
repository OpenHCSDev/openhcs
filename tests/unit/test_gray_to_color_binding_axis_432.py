"""Source-only #432: declared primary binding is not a runtime grouping axis."""

from dataclasses import replace

import numpy as np
import pytest

from openhcs.constants.constants import VariableComponents
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.aligned_image_payload import AlignedImageStack, ImagePayloadBundleContext, ImagePayloadExecutionMode
from openhcs.core.callable_contract import CallableContract
from openhcs.core.artifacts import ArtifactSpec, ImageArtifactType
from openhcs.core.config import StepSourceBindingsConfig
from openhcs.core.function_patterns import InvocationArtifactInputEdgePlan
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata, image_payload_data, image_payload_metadata,
)
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.runtime_plane_projection import RuntimePlaneAxisValueProjection
from openhcs.core.runtime_slice_projection import RuntimeSliceProjection
from openhcs.core.runtime_stores import RuntimeValueStore
from openhcs.core.source_bindings import NamedSourceBinding
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.steps.function_step import FunctionStep
from openhcs.interop.cellprofiler.runtime.adapter import CellProfilerRuntimeAdapter
from openhcs.interop.cellprofiler.runtime.function_contract_execution import (
    CellProfilerFunctionContractExecutor,
)
from openhcs.interop.cellprofiler.runtime.module_execution import CellProfilerModuleExecutor
from openhcs.interop.cellprofiler.runtime.artifact_binding import RuntimeArtifactTypeStrategy
from openhcs.processing.backends.cellprofiler.color import GrayToColorModule, gray_to_color
from test_cellprofiler_generic_special_input_binding import _compile_public_step
from tests.unit.cellprofiler_runtime_test_support import cellprofiler_runtime_adapter_for_test


@pytest.mark.parametrize("explicit_selector", [False, True])
def test_declared_fitc_runtime_plane_retains_values_and_physical_identity(explicit_selector):
    kwargs = {
        "color_scheme": GrayToColorModule.Scheme.STACK,
        "rescale_intensity": False,
        "name_the_output_image": "raw_body_reference",
    }
    if explicit_selector:
        kwargs["image_name"] = ("FITC",)
    step = FunctionStep(
        func=(gray_to_color, kwargs), name="RetainRawReference",
        source_bindings=StepSourceBindingsConfig(
            enabled=True, bindings=(NamedSourceBinding("FITC"),),
        ),
    )
    invocation = _compile_public_step(step)
    contract = replace(invocation.contract, metadata=replace(
        invocation.contract.metadata,
        runtime_adapter=CellProfilerRuntimeAdapter.runtime_adapter_spec(),
    ))
    pixels = np.arange(20, dtype=np.float32).reshape(4, 5) * 1000
    physical = {"well": "A01", "site": "1", "channel": "2", "z_index": "1", "timepoint": "1"}
    metadata = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/synthetic/A01_s1_w2_z1_t1.tif",), component_metadata=(physical,),
        ),
        source_image_names=("FITC",),
        source_voxel_spacing=SourceVoxelSpacing((1.0, 1.0)),
        source_spatial_domain=SourceSpatialDomain(origin_yx=(0, 0), source_shape_yx=(4, 5)),
    )
    source = metadata.payload_with(pixels[None], None)
    runtime = cellprofiler_runtime_adapter_for_test(
        runtime_value_store=RuntimeValueStore(), callable_contract=contract,
        variable_components=(VariableComponents.CHANNEL,),
        axis_scope=RuntimeExecutionAxisScope.from_raw("synthetic", component=None, value=None),
        artifact_inputs={edge.key: InvocationArtifactInputEdgePlan.from_source_declarations(
            key=edge.key, spec=edge.spec, main_flow_artifacts=contract.artifact_inputs,
            invocation_sources=contract.artifact_inputs,
        ) for edge in invocation.artifact_input_edges},
    )
    executor = CellProfilerModuleExecutor(gray_to_color, contract)
    request = executor._image_request(
        source, runtime, module_type=GrayToColorModule,
        active_input_specs=contract.artifact_inputs.specs,
    )
    assert contract.artifact_inputs.names() == ("FITC",)
    assert request.source_aliases == ("FITC",)
    assert request.image_count == 1
    # The source's acquisition axis remains distinct from the named input axis.
    assert isinstance(request.payload, AlignedImageStack)
    assert request.execution_mode is ImagePayloadExecutionMode.ALIGNED_MULTI_IMAGE_STACK
    assert request.plane_projection.axis is RuntimePlaneAxis.RUNTIME_SLICE
    assert request.plane_projection.axis_size == 1
    assert request.plane_projection.plane_index is None
    assert image_payload_metadata(request.payload.slices[0]).plane_axis is RuntimePlaneAxis.SOURCE_BINDING
    assert image_payload_metadata(request.payload.slices[0]).source_image_names == ("FITC",)
    execution = executor._invocation_request(
        image_request=request, adapter=runtime, current_image=source,
        module_type=GrayToColorModule,
        kwargs={"color_scheme": GrayToColorModule.Scheme.STACK, "rescale_intensity": False},
    )
    result = CellProfilerFunctionContractExecutor().execute(
        contract, contract.resolve_canonical_raw_callable(), execution.payload, execution.kwargs,
        execution_mode=execution.execution_mode, plane_projection=execution.plane_projection,
    )
    # Float32 is the original Stack runner's output contract, not unit normalization.
    assert image_payload_metadata(result).plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
    plane = RuntimeSliceProjection.value_for_slice(result, RuntimePlaneAxisValueProjection.from_selected_plane(
        axis=RuntimePlaneAxis.RUNTIME_SLICE, plane_index=0, axis_size=1,
    ))
    assert image_payload_data(plane).shape == (4, 5, 1)
    np.testing.assert_array_equal(image_payload_data(plane)[..., 0], pixels)
    np.testing.assert_array_equal(image_payload_data(source)[0], pixels)
    output = image_payload_metadata(result)
    assert output.source_image_paths == metadata.source_image_paths
    assert output.source_component_metadata["channel"] == "2"
    assert output.source_voxel_spacing == metadata.source_voxel_spacing
    assert output.source_spatial_domain == metadata.source_spatial_domain


def _source_plane(pixels, alias):
    return ImagePayloadMetadata(
        source_path="/synthetic/A01_s1_w2_z1_t1.tif",
        source_component_metadata={"well": "A01", "site": "1", "channel": "2", "z_index": "1", "timepoint": "1"},
        source_image_names=(alias,),
        source_voxel_spacing=SourceVoxelSpacing((1.0, 1.0)),
        source_spatial_domain=SourceSpatialDomain(origin_yx=(0, 0), source_shape_yx=pixels.shape[:2]),
    ).payload_with(pixels, None)


def _execute_bound_stack(bundle):
    contract = CallableContract.from_callable(gray_to_color)
    return CellProfilerFunctionContractExecutor().execute(
        contract, contract.resolve_canonical_raw_callable(), bundle,
        {"color_scheme": GrayToColorModule.Scheme.STACK, "rescale_intensity": False},
        execution_mode=ImagePayloadExecutionMode.FULL_STACK,
        plane_projection=RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.SOURCE_BINDING,
            axis_size=image_payload_data(bundle).shape[0],
            source_aliases=image_payload_metadata(bundle).source_image_names,
        ),
    )


@pytest.mark.parametrize("aliases", [("RawBody", "CappedOutgrowth"), ("IndependentRoleA", "IndependentRoleB")])
def test_two_processing_roles_share_physical_channel_without_fabrication(aliases):
    raw = np.arange(20, dtype=np.float32).reshape(4, 5) * 1000
    capped = np.clip(raw / 6000, 0, 1)
    inputs = tuple(_source_plane(pixels, alias) for pixels, alias in zip((raw, capped), aliases, strict=True))
    bundle = ImagePayloadBundleContext.from_payloads(inputs).compose()
    assert image_payload_metadata(bundle).plane_axis is RuntimePlaneAxis.SOURCE_BINDING
    result = _execute_bound_stack(bundle)
    np.testing.assert_array_equal(image_payload_data(result)[..., 0], raw)
    np.testing.assert_array_equal(image_payload_data(result)[..., 1], capped)
    np.testing.assert_array_equal(image_payload_data(inputs[0]), raw)
    metadata = image_payload_metadata(result)
    assert metadata.plane_axis is None
    assert metadata.source_channel_axis == -1
    assert metadata.source_component_metadata["channel"] == "2"
    assert set(metadata.source_image_paths) == {"/synthetic/A01_s1_w2_z1_t1.tif"}
    assert metadata.source_voxel_spacing == image_payload_metadata(inputs[0]).source_voxel_spacing
    assert metadata.source_spatial_domain == image_payload_metadata(inputs[0]).source_spatial_domain


def test_projected_runtime_plane_needs_a_separate_named_binding_axis():
    pixels = np.arange(20, dtype=np.float32).reshape(4, 5) * 1000
    scalar = _source_plane(pixels, "FITC")
    metadata = image_payload_metadata(scalar)
    retained = replace(metadata, plane_axis=RuntimePlaneAxis.RUNTIME_SLICE).payload_with(pixels[None], None)
    projected = RuntimeSliceProjection.value_for_slice(retained, RuntimePlaneAxisValueProjection.from_selected_plane(
        axis=RuntimePlaneAxis.RUNTIME_SLICE, plane_index=0, axis_size=1,
    ))
    assert image_payload_metadata(projected).plane_axis is None
    bundle = ImagePayloadBundleContext.from_payloads((projected,)).compose()
    assert image_payload_metadata(bundle).plane_axis is RuntimePlaneAxis.SOURCE_BINDING
    result = _execute_bound_stack(bundle)
    assert image_payload_data(result).shape == (4, 5, 1)
    np.testing.assert_array_equal(image_payload_data(result)[..., 0], pixels)
    assert image_payload_metadata(result).source_channel_axis == -1


def test_stack_color_output_is_not_a_second_scalar_gray_binding():
    pixels = np.arange(20, dtype=np.float32).reshape(4, 5)
    named = ImagePayloadBundleContext.from_payloads((_source_plane(pixels, "FITC"),)).compose()
    color = _execute_bound_stack(named)
    # The existing STACK contract emits YXC even for one role. A second grayscale
    # binding introduces C,Y,X,source-color rather than the required C,Y,X.
    assert image_payload_metadata(color).source_channel_axis == -1
    second_named = ImagePayloadBundleContext.from_payloads((color,)).compose()
    with pytest.raises(ValueError, match="axes don't match array"):
        _execute_bound_stack(second_named)


def test_integer_primary_binding_units_are_owned_before_stack_rescale_flag():
    pixels = np.arange(20, dtype=np.uint16).reshape(4, 5) * 1000
    source = _source_plane(pixels, "FITC")
    spec = ArtifactSpec.input("FITC", ImageArtifactType)
    binding_owner = RuntimeArtifactTypeStrategy.for_artifact_type(ImageArtifactType)
    bound = binding_owner.runtime_input_value(spec, source)
    # This conversion happens in the original input owner, before GrayToColor's
    # rescale_intensity argument. Do not claim a raw-unit-preserving four-step fix
    # from a passing floating-point Stack kernel test.
    np.testing.assert_array_equal(image_payload_data(bound), pixels.astype(np.float32) / 65535)
    np.testing.assert_array_equal(image_payload_data(source), pixels)
    assert image_payload_metadata(bound).source_image_paths == image_payload_metadata(source).source_image_paths
    assert image_payload_metadata(bound).source_component_metadata["channel"] == "2"
