"""Selected image declarations must materialize with their exact source identity."""

from openhcs.core.artifacts import ImageArtifactType

from pathlib import Path
from dataclasses import dataclass, fields, replace
from multiprocessing.shared_memory import SharedMemory

import numpy as np
import pytest
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
from polystore.memory import MemoryStorageBackend
from polystore.napari_stream import NapariStreamingBackend
from polystore.streaming import (
    StreamingBatchMessageBuilder,
    StreamingBatchMessageRequest,
)

from openhcs.core.callable_contract import CallableContract
from openhcs.core.artifacts import ArtifactOutputPlan
from openhcs.core.measurement_row_materialization import (
    DataclassMeasurementColumnarRows,
)
from openhcs.core.projected_image_output import (
    SelectedPlaneImageOutput,
    SourcePlaneSelectionImageOutput,
)
from openhcs.core.runtime_artifact_values import RuntimeValue
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_payload_metadata,
)
from openhcs.core.runtime_object_label_building import (
    SourceImageObjectLabelBuildRequest,
)
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisValueProjection,
)
from openhcs.core.runtime_spatial_graph import SpatialGraph, SpatialGraphNode
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_metadata import SourceVoxelSpacing, SourceVoxelSpacingUnit

from openhcs.core.steps.function_artifact_materialization import (
    PersistentArtifactMaterializationTargetPlan,
    runtime_artifact_materializations,
)
from openhcs.processing.backends.analysis.neurite_outgrowth import (
    NeuriteAdmissionPlanes,
    NeuriteOwnershipPlanes,
    neurite_outgrowth_metaxpress,
    NeuriteOutgrowthSummary,
    NeuriteOutgrowthCellResult,
)
from openhcs.processing.backends.cellprofiler.primary_object_diagnostics import (
    SelectedDiagnosticPlaneImageOutput,
)
from openhcs.processing.materialization import materialize

from test_function_artifact_materialization import (
    _context,
    _plan,
    streaming_config_stub,
)
from test_materialization_core import _viewer_stream_backend_kwargs
from openhcs.domains.microscopy.axes import Microscopy


def _source_stack(axis, component=Microscopy.Channel.name):
    spacing = SourceVoxelSpacing((1.3556, 1.3556))
    coordinates = tuple(
        {
            "well": "A01",
            "site": "1",
            "channel": "7",
            "z_index": "1",
            "timepoint": "1",
            component: str(index),
        }
        for index in (1, 2)
    )
    metadata = ImagePayloadMetadata(
        plane_axis=axis,
        source_voxel_spacing=spacing,
        source_image_names=("DAPI", "FITC"),
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=tuple(f"/input/A01_s001_w{index}_z001_t001.tif" for index in (1, 2)),
            component_metadata=coordinates,
        ),
    )
    return metadata.payload_with(np.arange(112, dtype=np.uint16).reshape(2, 7, 8))


@pytest.mark.parametrize("axis", tuple(RuntimePlaneAxis))
@pytest.mark.parametrize(
    "output_type,artifact_name,dtype",
    (
        (SelectedPlaneImageOutput, "neurite_candidate_mask", np.uint16),
        (SelectedDiagnosticPlaneImageOutput, "neurite_enhanced_response", np.float32),
    ),
)
def test_public_selected_checkpoint_materializes_and_streams_without_storage_axes(
    axis,
    output_type, artifact_name, dtype,
    tmp_path,
    monkeypatch,
):
    source = _source_stack(axis)
    pixels = np.arange(56, dtype=dtype).reshape(1, 7, 8)
    selected = output_type(pixels, (1,))
    payload = ImageArtifactType.contextualize_output(
        source,
        selected,
        None,
        RuntimePlaneAxisValueProjection.preserve(axis=axis, axis_size=2),
    )
    spec = next(
        spec
        for spec in CallableContract.from_callable(
            neurite_outgrowth_metaxpress
        ).artifact_outputs
        if spec.name == artifact_name
    )
    viewer = NapariStreamingBackend()
    filemanager = FileManager(
        {
            "disk": DiskStorageBackend(),
            "memory": MemoryStorageBackend(),
            "napari_stream": viewer,
        }
    )
    saved_streams = []
    save_batch = filemanager.save_batch

    def capture_stream(data_list, paths, backend, **kwargs):
        if backend == "napari_stream":
            saved_streams.append(
                (tuple(data_list), tuple(paths), kwargs["stream_request"])
            )
            return
        return save_batch(data_list, paths, backend, **kwargs)

    monkeypatch.setattr(filemanager, "save_batch", capture_stream)
    try:
        result = materialize(
            spec.materialization,
            payload,
            str(tmp_path / "checkpoint.tif"),
            filemanager,
            ["disk", "napari_stream"],
            {"napari_stream": _viewer_stream_backend_kwargs()},
            context=_context(filemanager),
            variable_components=(),
        )
        assert Path(result).is_file()
        np.testing.assert_array_equal(
            np.asarray(filemanager.load(result, "disk")).reshape(-1), pixels.reshape(-1)
        )
        assert len(saved_streams) == 1
        (data,), (path,), request = saved_streams[0]
        assert path == result
        np.testing.assert_array_equal(np.asarray(data).reshape(-1), pixels.reshape(-1))
        assert data.shape == (7, 8)
        assert "plane_axis" not in request.source.item_fields
        assert "plane_component_values" not in request.source.item_fields
        assert (
            request.source.metadata.component_metadata_for_item(path, 0)["channel"] == 2
        )
        assert image_payload_metadata(payload).source_image_names == ("FITC",)
        assert (
            image_payload_metadata(payload).source_path
            == "/input/A01_s001_w2_z001_t001.tif"
        )
        assert image_payload_metadata(
            payload
        ).source_voxel_spacing == SourceVoxelSpacing((1.3556, 1.3556))
    finally:
        viewer.cleanup()


@pytest.mark.parametrize("component", ("channel", "site", "z_index", "timepoint"))
@pytest.mark.parametrize("indices", ((1,), (1, 0)))
def test_selection_contract_keeps_exact_source_order_without_channel_inference(
    component, indices
):
    source = _source_stack(RuntimePlaneAxis.SOURCE_BINDING, component)
    pixels = np.arange(len(indices) * 56).reshape(len(indices), 7, 8)
    payload = SelectedPlaneImageOutput(pixels, indices).resolve_source_context(
        source,
        RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.SOURCE_BINDING, axis_size=2
        ),
    )
    metadata = image_payload_metadata(payload)
    if len(indices) == 1:
        assert payload.shape == (7, 8)
        assert metadata.plane_axis is None
        assert dict(metadata.source_component_metadata)[component] == "2"
    else:
        assert payload.shape == (2, 7, 8)
        assert metadata.plane_axis is RuntimePlaneAxis.SOURCE_BINDING
        assert metadata.retained_plane_component_values() == {component: ("2", "1")}
    assert metadata.source_voxel_spacing == SourceVoxelSpacing((1.3556, 1.3556))
    np.testing.assert_array_equal(np.asarray(payload).reshape(-1), pixels.reshape(-1))


def test_independent_leaf_and_capabilities_execute_cooperative_selection_hooks():
    calls = []

    class ObservedSelection:
        def selected_source_plane_indices(self):
            calls.append("observe")
            return super().selected_source_plane_indices()

    class ReversedSelection:
        def selected_source_plane_indices(self):
            calls.append("reverse")
            return tuple(reversed(super().selected_source_plane_indices()))

    # The leaf supplies its declaration after the independent capabilities in MRO.
    class PlaneDeclaration(SourcePlaneSelectionImageOutput):
        def selected_source_plane_indices(self):
            calls.append("declaration")
            return (0, 1)

    @dataclass(frozen=True)
    class DeclaredCrop(ObservedSelection, ReversedSelection, PlaneDeclaration):
        data: np.ndarray

        def with_data(self, data):
            return replace(self, data=data)

    selected = DeclaredCrop(np.arange(112).reshape(2, 7, 8))
    calls.clear()
    payload = ImageArtifactType.contextualize_output(
        _source_stack(RuntimePlaneAxis.SOURCE_BINDING),
        selected,
        None,
        RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.SOURCE_BINDING, axis_size=2
        ),
    )
    assert calls == ["observe", "reverse", "declaration"]
    assert image_payload_metadata(payload).source_image_names == ("FITC", "DAPI")
    assert image_payload_metadata(payload).retained_plane_component_values() == {
        "channel": ("2", "1")
    }
    np.testing.assert_array_equal(np.asarray(payload), selected.data)


def test_new_diagnostic_leaf_composes_cooperative_hooks_without_consumer_edits():
    calls = []

    class ObservedProjection:
        def resolve_source_context(self, source, projection):
            calls.append("before")
            result = super().resolve_source_context(source, projection)
            calls.append("after")
            return result

        def selected_source_plane_indices(self):
            calls.append("selection")
            return super().selected_source_plane_indices()

    class DeclaredResponse(ObservedProjection, SelectedDiagnosticPlaneImageOutput):
        pass

    source = _source_stack(RuntimePlaneAxis.SOURCE_BINDING)
    pixels = np.full((1, 7, 8), .75, dtype=np.float32)
    response = DeclaredResponse(pixels, (1,))
    calls.clear()
    payload = ImageArtifactType.contextualize_output(
        source, response, None,
        RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.SOURCE_BINDING, axis_size=2
        ),
    )
    assert calls == ["before", "selection", "after"]
    np.testing.assert_array_equal(np.asarray(payload), pixels[0])
    assert image_payload_metadata(payload).source_image_names == ("FITC",)
    assert image_payload_metadata(payload).intensity_scale is None
    assert image_payload_metadata(payload).source_dtype == "float32"


def test_all_public_declared_outputs_persist_with_selected_qa_streams(
    tmp_path, monkeypatch, viewer_ack_return_route
):
    source = _source_stack(RuntimePlaneAxis.SOURCE_BINDING)
    projection = RuntimePlaneAxisValueProjection.preserve(
        axis=RuntimePlaneAxis.SOURCE_BINDING, axis_size=2
    )
    labels = np.zeros((2, 7, 8), dtype=np.int32)
    labels[1, 2:5, 3:6] = 1
    label_payload = SourceImageObjectLabelBuildRequest(
        image=source, labels=labels, plane_projection=projection
    ).payload()
    summary = NeuriteOutgrowthSummary(
        **{field.name: 0 for field in fields(NeuriteOutgrowthSummary) if field.name != "coordinate_unit"},
        coordinate_unit=SourceVoxelSpacingUnit.MICROMETERS,
    )
    cell = NeuriteOutgrowthCellResult(
        1, 1, SourceVoxelSpacingUnit.MICROMETERS, 0.0, 0, 0.0, 0.0, 0.0, 0, 0.0, 1.0, 0.0, False
    )
    selected = ImageArtifactType.contextualize_output(
        source,
        SelectedPlaneImageOutput((labels[1] > 0).astype(np.uint8)[None], (1,)),
        None,
        projection,
    )
    graph = SpatialGraph(
        name="neurite_morphology",
        nodes=(SpatialGraphNode(1, (3, 4), features=(("label", 1),)),),
        edges=(),
        coordinate_spacing=SourceVoxelSpacing((1.3556, 1.3556)),
        source_plane_index=1,
        source_provenance=image_payload_metadata(selected).source_provenance,
    )
    values = (
        DataclassMeasurementColumnarRows((summary,), row_type=NeuriteOutgrowthSummary),
        DataclassMeasurementColumnarRows((cell,), row_type=NeuriteOutgrowthCellResult),
        label_payload,
        label_payload,
        label_payload,
        label_payload,
        *(
            SelectedPlaneImageOutput((labels[1] > 0).astype(np.uint8)[None], (1,))
            for _ in range(5)
        ),
        *NeuriteAdmissionPlanes(
            np.asarray(source)[1].astype(np.float32),
            labels[1] > 0, labels[1] > 0,
            np.asarray(source)[1].astype(np.float32), labels[1] > 0,
            np.asarray(source)[1].astype(np.float32),
        ).selected_outputs(1),
        *NeuriteOwnershipPlanes(labels[1], labels[1], labels[1]).selected_outputs(1),
        graph,
    )
    specs = CallableContract.from_callable(
        neurite_outgrowth_metaxpress
    ).artifact_outputs
    plans = tuple(
        ArtifactOutputPlan(
            name=spec.name,
            path=str(tmp_path / "runtime" / f"{spec.name}.pkl"),
            artifact_type=spec.artifact_type,
            materialization=spec.materialization,
            viewer_streaming=spec.viewer_streaming,
            sidecar_role=spec.sidecar_role,
            relations=spec.relations,
        )
        for spec in specs
    )
    viewer = NapariStreamingBackend()
    filemanager = FileManager(
        {
            "disk": DiskStorageBackend(),
            "memory": MemoryStorageBackend(),
            "napari_stream": viewer,
        }
    )
    context = _context(filemanager)
    plan = replace(
        _plan(plans[0], streaming_configs={"napari_stream": streaming_config_stub()}),
        artifact_outputs={output.ref(): output for output in plans},
        analysis_results_dir=str(tmp_path / "analysis"),
        output_dir=tmp_path / "images",
    )
    for output, value in zip(plans, values, strict=True):
        value = (ImageArtifactType if output is None else output.artifact_type).contextualize_output(
            source,
            value,
            output,
            projection,
        )
        context.runtime_value_store.record(
            RuntimeValue.normalize(output, value, axis_id="A01"),
            path=output.path,
            backend="memory",
        )
    saved_streams = []
    save_batch = filemanager.save_batch

    def capture_stream(data_list, paths, backend, **kwargs):
        if backend == "napari_stream":
            saved_streams.append(
                (tuple(data_list), tuple(paths), kwargs["stream_request"])
            )
            return
        return save_batch(data_list, paths, backend, **kwargs)

    monkeypatch.setattr(filemanager, "save_batch", capture_stream)
    try:
        PersistentArtifactMaterializationTargetPlan("disk").materialize_outputs(filemanager, plan, context)
        materializations = runtime_artifact_materializations(plan, context)
        assert {item.output_plan.name for item in materializations} == set(
            specs.names()
        )
        assert len(materializations) == 12 + len(
            NeuriteAdmissionPlanes.artifact_specs() + NeuriteOwnershipPlanes.artifact_specs()
        )
        for item in materializations:
            outputs = item.outputs(plan, context)
            assert outputs
            assert all(Path(output.path).is_file() for output in outputs)
        checkpoints = [
            (data, paths, request)
            for data, paths, request in saved_streams
            if paths[0].endswith(".checkpoint.tif")
        ]
        assert len(checkpoints) == 5 + len(
            NeuriteAdmissionPlanes.artifact_specs() + NeuriteOwnershipPlanes.artifact_specs()
        )
        for (data,), (path,), request in checkpoints:
            assert (
                request.source.metadata.component_metadata_for_item(path, 0)["channel"]
                == 2
            )
            metadata = ImagePayloadMetadata.from_viewer_image_metadata(
                request.source.item_fields["image_metadata"]
            )
            assert metadata.source_voxel_spacing == SourceVoxelSpacing((1.3556, 1.3556))
            assert metadata.plane_axis is None
            assert data.shape == (7, 8)
            batch = StreamingBatchMessageBuilder.build(
                viewer,
                StreamingBatchMessageRequest(
                    return_route=viewer_ack_return_route,
                    data_list=[data],
                    file_paths=[path],
                    stream_request=request,
                    component_names_request=viewer.component_names_request(request),
                    display_payload_extra=viewer.display_payload_extra(request),
                ),
            )
            item = batch.batch_images[0]
            assert item["metadata"]["channel"] == 2
            memory = SharedMemory(name=item["shm_name"])
            try:
                transmitted = np.ndarray(
                    item["shape"], dtype=item["dtype"], buffer=memory.buf
                ).copy()
            finally:
                memory.close()
            np.testing.assert_array_equal(
                transmitted, np.asarray(filemanager.load(path, "disk"))
            )
    finally:
        viewer.cleanup()
