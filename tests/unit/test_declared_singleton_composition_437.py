"""Declaration-owned admission to the unchanged source-bundle algorithm."""

from dataclasses import replace

import numpy as np
import pytest

from openhcs.core.aligned_image_payload import (
    AlignedImageSliceContext,
    AlignedImageStack,
    ImagePayloadExecutionMode,
)
from openhcs.core.callable_contract import CallableContract, ImagePayloadConsumption
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.function_patterns import (
    FunctionInvocationKey,
    InvocationArtifactInputEdgePlan,
    InvocationArtifactInputProjectionKey,
)
from openhcs.core.memory.decorators import numpy as numpy_contract
from openhcs.core.pipeline.function_contracts import (
    artifact_inputs,
    composed_image_payload,
)
from openhcs.core.artifacts import ArtifactSpec, ImageArtifactType
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_payload_data,
    image_payload_mask,
    image_payload_metadata,
)
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisValueProjection,
    RuntimePlaneProjection,
)
from openhcs.core.runtime_slice_projection import RuntimeSliceProjection
from openhcs.core.runtime_stores import RuntimeValueStore
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.interop.cellprofiler.runtime.adapter import CellProfilerRuntimeAdapter
from openhcs.interop.cellprofiler.runtime.function_contract_execution import (
    CellProfilerFunctionContractExecutor,
)
from openhcs.interop.cellprofiler.runtime.module_execution import (
    CellProfilerModuleExecutor,
)
from openhcs.processing.backends.cellprofiler.image_math import (
    image_math,
    MathOperation,
)
from openhcs.processing.backends.cellprofiler.color import (
    gray_to_color,
    GrayToColorModule,
)
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from tests.unit.cellprofiler_runtime_test_support import (
    cellprofiler_runtime_adapter_for_test,
)


@artifact_inputs(ArtifactSpec.input("FITC", ImageArtifactType))
@composed_image_payload
@numpy_contract(contract=ProcessingContract.PURE_3D)
def independently_declared_source_echo(image):
    """A new source consumer, not a GrayToColor alias or special-case branch."""
    assert image_payload_metadata(image).plane_axis is RuntimePlaneAxis.SOURCE_BINDING
    return RuntimeSliceProjection.value_for_slice(
        image,
        RuntimePlaneAxisValueProjection.from_selected_plane(
            axis=RuntimePlaneAxis.SOURCE_BINDING,
            plane_index=0,
            axis_size=1,
            source_aliases=("FITC",),
        ),
    )


class IndependentlyDeclaredSourceEchoModule(CellProfilerModule):
    module_name = "IndependentlyDeclaredSourceEcho437"
    function_name = "independently_declared_source_echo"


def _runtime_source(slice_count):
    pixels = (
        np.arange(slice_count * 20, dtype=np.float32).reshape(slice_count, 4, 5) / 100
    )
    masks = np.ones_like(pixels, dtype=bool)
    masks[:, 0, 0] = False
    metadata = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_image_names=("FITC",),
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=tuple(
                f"/synthetic/A01_s{index + 1}_w2.tif" for index in range(slice_count)
            ),
            component_metadata=tuple(
                {"well": "A01", "site": str(index + 1), "channel": "2"}
                for index in range(slice_count)
            ),
        ),
        source_voxel_spacing=SourceVoxelSpacing((1.25, 2.5)),
        source_spatial_domain=SourceSpatialDomain(
            origin_yx=(0, 0), source_shape_yx=(4, 5)
        ),
    )
    return metadata.payload_with(pixels, masks)


@pytest.mark.parametrize("slice_count", (1, 3))
@pytest.mark.parametrize("aligned", (False, True))
def test_new_declaration_reuses_composition_and_executor(slice_count, aligned):
    source = _runtime_source(slice_count)
    original_pixels = image_payload_data(source).copy()
    original_masks = image_payload_mask(source).copy()
    projection = RuntimePlaneAxisValueProjection.preserve(
        axis=RuntimePlaneAxis.RUNTIME_SLICE,
        axis_size=slice_count,
    )
    planes = tuple(
        RuntimeSliceProjection.value_for_slice(source, projection.selected_plane(index))
        for index in range(slice_count)
    )
    contexts = tuple(
        AlignedImageSliceContext.main_flow(f"site{index + 1}")
        for index in range(slice_count)
    )
    current = AlignedImageStack(planes, contexts) if aligned else source
    declared = CallableContract.from_callable(independently_declared_source_echo)
    contract = replace(
        declared,
        metadata=replace(
            declared.metadata,
            runtime_adapter=CellProfilerRuntimeAdapter.runtime_adapter_spec(),
        ),
    )
    spec = contract.artifact_inputs.specs[0]
    key = InvocationArtifactInputProjectionKey(
        invocation_key=FunctionInvocationKey("new-declaration437", "default", 0),
        input_index=0,
    )
    edge = InvocationArtifactInputEdgePlan.from_source_declarations(
        key=key,
        spec=spec,
        main_flow_artifacts=contract.artifact_inputs,
        invocation_sources=contract.artifact_inputs,
    )
    runtime = cellprofiler_runtime_adapter_for_test(
        runtime_value_store=RuntimeValueStore(),
        callable_contract=contract,
        axis_scope=RuntimeExecutionAxisScope.from_raw(
            "synthetic", component=None, value=None
        ),
        artifact_inputs={key: edge},
    )
    if aligned:
        # This case exercises the composition owner, not Root394's unresolved
        # pre-composition adapter ingress for already-aligned main-flow values.
        composition = contract.image_payload_consumption.compose_image_payload(
            "independent aligned declaration",
            (current,),
        )
        payload = composition.payload
        execution_mode = composition.execution_mode
        plane_projection = composition.preserved_plane_projection(
            RuntimePlaneProjection.stack(slice_count)
        )
    else:
        request = CellProfilerModuleExecutor(
            independently_declared_source_echo, contract
        )._image_request(
            current,
            runtime,
            module_type=IndependentlyDeclaredSourceEchoModule,
            active_input_specs=contract.artifact_inputs.specs,
        )
        invocation = CellProfilerModuleExecutor(
            independently_declared_source_echo, contract
        )._invocation_request(
            image_request=request,
            adapter=runtime,
            current_image=current,
            kwargs={},
            module_type=IndependentlyDeclaredSourceEchoModule,
        )
        payload = invocation.image
        execution_mode = invocation.execution_mode
        plane_projection = invocation.plane_projection
    assert execution_mode is ImagePayloadExecutionMode.ALIGNED_MULTI_IMAGE_STACK
    assert isinstance(payload, AlignedImageStack)
    assert plane_projection == projection
    assert payload.slice_contexts == (contexts if aligned else ())
    for index, plane in enumerate(payload.slices):
        metadata = image_payload_metadata(plane)
        assert metadata.plane_axis is RuntimePlaneAxis.SOURCE_BINDING
        assert metadata.source_image_names == ("FITC",)
        assert metadata.source_component_metadata["channel"] == "2"
        assert metadata.source_image_paths == (f"/synthetic/A01_s{index + 1}_w2.tif",)
        np.testing.assert_array_equal(
            image_payload_data(plane)[0], original_pixels[index]
        )
        np.testing.assert_array_equal(image_payload_mask(plane), original_masks[index])
    result = CellProfilerFunctionContractExecutor().execute(
        contract,
        contract.resolve_canonical_raw_callable(),
        payload,
        {},
        execution_mode=execution_mode,
        plane_projection=plane_projection,
    )
    assert RuntimeSliceProjection.slice_count_from_values((result,)) == slice_count
    for index in range(slice_count):
        result_plane = RuntimeSliceProjection.value_for_slice(
            result, projection.selected_plane(index)
        )
        np.testing.assert_array_equal(
            image_payload_data(result_plane), original_pixels[index]
        )
        np.testing.assert_array_equal(
            image_payload_mask(result_plane), original_masks[index]
        )
        metadata = image_payload_metadata(result_plane)
        assert metadata.plane_axis is None
        assert metadata.source_channel_axis is None
        assert (
            metadata.source_voxel_spacing
            == image_payload_metadata(source).source_voxel_spacing
        )
        assert (
            metadata.source_spatial_domain
            == image_payload_metadata(source).source_spatial_domain
        )
    np.testing.assert_array_equal(image_payload_data(source), original_pixels)
    np.testing.assert_array_equal(image_payload_mask(source), original_masks)


def test_declared_composed_scalar_introduces_one_source_axis():
    source = _runtime_source(1)
    scalar = RuntimeSliceProjection.value_for_slice(
        source,
        RuntimePlaneAxisValueProjection.from_selected_plane(
            axis=RuntimePlaneAxis.RUNTIME_SLICE,
            plane_index=0,
            axis_size=1,
        ),
    )
    composition = CallableContract.from_callable(
        independently_declared_source_echo
    ).image_payload_consumption.compose_image_payload(
        "independent scalar",
        (scalar,),
    )
    assert composition.execution_mode is ImagePayloadExecutionMode.FULL_STACK
    assert (
        image_payload_metadata(composition.payload).plane_axis
        is RuntimePlaneAxis.SOURCE_BINDING
    )
    contract = CallableContract.from_callable(independently_declared_source_echo)
    result = CellProfilerFunctionContractExecutor().execute(
        contract,
        contract.resolve_canonical_raw_callable(),
        composition.payload,
        {},
        execution_mode=composition.execution_mode,
    )
    np.testing.assert_array_equal(
        image_payload_data(result), image_payload_data(source)[0]
    )


@pytest.mark.parametrize("aligned", (False, True))
def test_natural_declaration_retains_exact_singleton(aligned):
    source = _runtime_source(3)
    current = AlignedImageStack((source,)) if aligned else source
    contract = CallableContract.from_callable(image_math)
    assert contract.image_payload_consumption is ImagePayloadConsumption.NATURAL
    composition = contract.image_payload_consumption.compose_image_payload(
        "natural identity", (current,)
    )
    assert composition.payload is current
    assert composition.execution_mode is (
        ImagePayloadExecutionMode.ALIGNED_MULTI_IMAGE_STACK
        if aligned
        else ImagePayloadExecutionMode.NATURAL
    )
    if not aligned:
        result = CellProfilerFunctionContractExecutor().execute(
            contract,
            contract.resolve_canonical_raw_callable(),
            composition.payload,
            {"operation": MathOperation.NONE},
            execution_mode=composition.execution_mode,
        )
        # NONE still applies the original mask policy: masked pixels become zero.
        np.testing.assert_array_equal(
            image_payload_data(result),
            image_payload_data(source) * image_payload_mask(source),
        )
        np.testing.assert_array_equal(
            image_payload_mask(result), image_payload_mask(source)
        )
        assert (
            image_payload_metadata(result).plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
        )


def test_kernel_still_rejects_unprojected_runtime_axis():
    source = _runtime_source(1)
    contract = CallableContract.from_callable(gray_to_color)
    with pytest.raises(ValueError, match="requires a source-binding plane axis"):
        contract.resolve_canonical_raw_callable()(
            source,
            color_scheme=GrayToColorModule.Scheme.STACK,
            rescale_intensity=False,
        )
