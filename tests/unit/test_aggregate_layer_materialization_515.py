"""Issue #515: automatic label TIFFs must honor scalar LAYER routing.

The renderer, disk TIFF writer and wire builder are real. Only the final viewer
transport is intercepted; no viewer or native process is started.
"""

from dataclasses import replace

import numpy as np
import pytest

from openhcs.core.artifacts import ArtifactOutputPlan, ObjectLabelsArtifactType
from openhcs.core.pipeline.artifact_planning import (
    AutomaticObjectLabelsArtifactOutputMaterializationStrategy,
)
from openhcs.core.runtime_artifact_values import RuntimeValue
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_object_label_domains import ObjectLabelDomain, ObjectLabelDomainScope
from openhcs.core.runtime_object_labels import ObjectLabelPayload, ObjectLabelVariantData
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis, RuntimePlaneAxisValueProjection
from openhcs.core.runtime_slice_projection import (
    RuntimeProjectionSourceIdentityRequest,
    RequiredSourceComponentMetadata,
    RuntimeSliceProjectionDeclarationError,
)
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.runtime.napari_streaming_handlers import (
    NapariAggregateAxisBindingAuthority,
    NapariStreamLayerAddress,
    NapariStreamLayerItem,
)
from openhcs.runtime.viewer_component_system import (
    ViewerComponentAxisSemanticsAuthority,
    ViewerComponentValueDomainPayload,
    ViewerMappingDisplayConfigInput,
)
from openhcs.core.steps.function_artifact_materialization import (
    PersistentArtifactMaterializationTargetPlan,
)
from polystore.napari_stream import NapariStreamingBackend
from polystore.base import ensure_storage_registry, storage_registry
from polystore.filemanager import FileManager
from polystore.streaming import StreamingBatchMessageBuilder, StreamingBatchMessageRequest
from polystore.streaming.receivers.napari.layer_key import build_route_key, normalize_component_layout
from polystore.streaming.viewer_transport import ViewerStreamKwarg
from polystore.streaming.viewer_transport import ViewerStreamBackendKwargs
from polystore.streaming_constants import StreamingDataType
from openhcs.processing.materialization.core import (
    BackendSaver,
    Output,
    ViewerStreamBackendCallKwargs,
)
from polystore.streaming.identity import StreamProducerIdentity

from tests.unit.test_function_artifact_materialization import (
    StreamingConfigStub,
    _context,
    _plan,
)
from openhcs.domains.microscopy.axes import Microscopy


class ComponentDisplayConfig(StreamingConfigStub):
    def __init__(self, component, mode):
        super().__init__(5555)
        self.component = component
        self.mode = mode

    def component_modes(self):
        return {**super().component_modes(), self.component.name: self.mode}


def _source_bound_labels(component):
    pixels = np.zeros((2, 4, 5), dtype=np.int32)
    pixels[0, 1:3, 1:4] = 1
    pixels[1, 1:3, 2:5] = 2
    source_fields = tuple(
        {"well": "A01", "site": 1, "channel": 1, "z_index": 1,
         "timepoint": 1, component.name: value}
        for value in (1, 2)
    )
    paths = tuple(
        f"/input/A01_s{fields['site']:03d}_w{fields['channel']}_z001_t001.tif"
        for fields in source_fields
    )
    labels = ObjectLabelPayload(
        variant_data=ObjectLabelVariantData(labels=pixels),
        plane_axis=RuntimePlaneAxis.SOURCE_BINDING,
        domain=ObjectLabelDomain(
            declared_object_id_domains=((1,), (2,)), scope=ObjectLabelDomainScope.PLANE,
        ),
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=paths, component_metadata=source_fields,
        ),
        source_component_metadata={
            key: value for key, value in source_fields[0].items()
            if all(fields[key] == value for fields in source_fields)
        },
        source_spatial_domain=SourceSpatialDomain(source_shape_yx=(4, 5)),
        parent_image_source_voxel_spacing=SourceVoxelSpacing((0.75, 0.75)),
    )
    return labels, pixels.copy()


def _automatic_label_tiff(component, mode, return_route, monkeypatch, tmp_path):
    labels, pixels = _source_bound_labels(component)
    output_plan = ArtifactOutputPlan(
        name="Nuclei", path="/memory/Nuclei.pkl", artifact_type=ObjectLabelsArtifactType,
        variable_components=(component,),
        materialization=AutomaticObjectLabelsArtifactOutputMaterializationStrategy().materialization(),
    )
    ensure_storage_registry()
    filemanager = FileManager(dict(storage_registry))
    stream_saves = []
    disk_outputs = []
    original_save_batch = filemanager.save_batch
    original_save_all = BackendSaver.save_all

    def save_all(saver, outputs):
        if "disk" in saver.backends:
            disk_outputs.extend(
                output for output in outputs if output.path.endswith(".labels.tif")
            )
        return original_save_all(saver, outputs)

    def save_batch(contents, paths, backend, **kwargs):
        if backend == "napari_stream":
            stream_saves.extend(
                (content, path, backend, kwargs)
                for content, path in zip(contents, paths, strict=True)
            )
            return
        return original_save_batch(contents, paths, backend, **kwargs)

    monkeypatch.setattr(filemanager, "save_batch", save_batch)
    monkeypatch.setattr(BackendSaver, "save_all", save_all)
    context = _context(filemanager)
    context.runtime_value_store.record(
        RuntimeValue.normalize(output_plan, labels, axis_id="A01"),
        path=output_plan.path, backend="memory",
    )
    plan = replace(_plan(
        output_plan,
        streaming_configs={"napari_stream": ComponentDisplayConfig(component, mode)},
        variable_components=(component,),
    ), analysis_results_dir=str(tmp_path / "analysis"), output_dir=tmp_path / "images")
    PersistentArtifactMaterializationTargetPlan("disk").materialize_outputs(filemanager, plan, context)
    assert len(disk_outputs) == 1
    import tifffile

    persisted_pixels = tifffile.imread(disk_outputs[0].path)
    np.testing.assert_array_equal(persisted_pixels, pixels)
    assert persisted_pixels.dtype == pixels.dtype
    metadata = disk_outputs[0].metadata
    assert metadata.plane_axis is RuntimePlaneAxis.SOURCE_BINDING
    assert metadata.source_provenance.source_plane_count == 2
    assert metadata.source_voxel_spacing.values_zyx == (0.75, 0.75)
    assert [metadata.source_provenance.for_source_plane(index).source_component_metadata[component.name]
            for index in range(2)] == [1, 2]
    np.testing.assert_array_equal(labels.labels, pixels)
    tiff_saves = [saved for saved in stream_saves if saved[1].endswith(".labels.tif")]
    assert tiff_saves, "Automatic object-label materialization did not reach the TIFF backend."
    backend = NapariStreamingBackend()
    wire_batches = []
    try:
        for content, path, backend_name, kwargs in tiff_saves:
            assert backend_name == "napari_stream"
            assert content.dtype == pixels.dtype
            request = kwargs[ViewerStreamKwarg.STREAM_REQUEST.value]
            wire_batches.append(StreamingBatchMessageBuilder.build(
                backend,
                StreamingBatchMessageRequest(
                    return_route=return_route, data_list=[content], file_paths=[path],
                    stream_request=request,
                    component_names_request=backend.component_names_request(request),
                    display_payload_extra=backend.display_payload_extra(request),
                ),
            ))
        return labels, pixels, tiff_saves, wire_batches
    finally:
        backend.cleanup()


def _route_keys(batches):
    return [
        build_route_key(
            item["producer_identity"], item["metadata"],
            normalize_component_layout(batch.message["display_config"]),
            StreamingDataType(item["data_type"]),
        )
        for batch in batches for item in batch.batch_images
    ]


def _received_item(batch, pixels):
    wire = batch.batch_images[0]
    item = NapariStreamLayerItem(
        data=pixels,
        producer=StreamProducerIdentity.from_payload(wire["producer_identity"]),
        address=NapariStreamLayerAddress(
            components=wire["metadata"], path=wire["path"],
            stream_layer_data_type=StreamingDataType(wire["data_type"]),
        ),
        image_metadata=ImagePayloadMetadata.from_viewer_image_metadata(wire["image_metadata"]),
        plane_component_domain=ViewerComponentValueDomainPayload.from_ordered_wire_mapping(
            wire["plane_component_values"], context="actual automatic TIFF wire domain",
        ),
    )
    semantics = ViewerComponentAxisSemanticsAuthority.from_display_config(
        ViewerMappingDisplayConfigInput(batch.message["display_config"]),
        ViewerComponentValueDomainPayload.from_wire_mapping(
            batch.message["component_value_domain"], context="actual automatic TIFF viewer domain",
        ),
    )
    return item, semantics


@pytest.mark.parametrize("component", (Microscopy.Channel, Microscopy.Site))
def test_automatic_aggregate_label_tiff_honors_separate_layers(component, viewer_ack_return_route, monkeypatch, tmp_path):
    labels, pixels, saves, batches = _automatic_label_tiff(component, "layer", viewer_ack_return_route, monkeypatch, tmp_path)
    # This is the original strict receiver, not a test-side default or projection.
    keys = _route_keys(batches)
    items = [item for batch in batches for item in batch.batch_images]
    assert [item["metadata"][component.name] for item in items] == [1, 2]
    assert len(set(keys)) == 2
    assert [tuple(item["shape"]) for item in items] == [(4, 5), (4, 5)]
    for index, (content, _path, _backend, _kwargs) in enumerate(saves):
        np.testing.assert_array_equal(content, pixels[index])
    np.testing.assert_array_equal(labels.labels, pixels)


@pytest.mark.parametrize("component", (Microscopy.Channel, Microscopy.Site))
def test_automatic_aggregate_label_tiff_preserves_stack(component, viewer_ack_return_route, monkeypatch, tmp_path):
    labels, pixels, saves, batches = _automatic_label_tiff(component, "stack", viewer_ack_return_route, monkeypatch, tmp_path)
    assert len(saves) == len(batches) == 1
    np.testing.assert_array_equal(saves[0][0], pixels)
    item = batches[0].batch_images[0]
    assert tuple(item["shape"]) == pixels.shape
    assert item["dtype"] == str(pixels.dtype)
    assert item["plane_axis"] == RuntimePlaneAxis.SOURCE_BINDING.value
    assert item["plane_component_values"] == {component.name: ["1", "2"]}
    decoded = ImagePayloadMetadata.from_viewer_image_metadata(item["image_metadata"])
    assert decoded.source_voxel_spacing.values_zyx == (0.75, 0.75)
    assert decoded.source_spatial_domain.source_shape_yx == (4, 5)
    assert component.name not in item["metadata"]
    assert len(_route_keys(batches)) == 1
    received, semantics = _received_item(batches[0], saves[0][0])
    bindings = NapariAggregateAxisBindingAuthority.bindings((received,), semantics)
    assert len(bindings.bindings) == 1
    assert bindings.bindings[0].component == component.name
    assert bindings.bindings[0].values == (1, 2)
    np.testing.assert_array_equal(labels.labels, pixels)


def test_strict_receiver_still_rejects_aggregate_without_scalar_layer(viewer_ack_return_route, monkeypatch, tmp_path):
    _labels, _pixels, _saves, batches = _automatic_label_tiff(
        Microscopy.Channel, "stack", viewer_ack_return_route, monkeypatch, tmp_path,
    )
    batch = batches[0]
    layout = normalize_component_layout(batch.message["display_config"])
    layout = replace(layout, component_modes={**layout.component_modes, "channel": "layer"})
    item = batch.batch_images[0]
    with pytest.raises(ValueError, match="missing layer component 'channel'"):
        build_route_key(item["producer_identity"], item["metadata"], layout, StreamingDataType.IMAGE)


@pytest.mark.parametrize("plane_count", (1, 2))
def test_single_output_kwargs_cannot_hide_projected_pixels(
    plane_count, viewer_ack_return_route, monkeypatch, tmp_path,
):
    labels, pixels, saves, _batches = _automatic_label_tiff(
        Microscopy.Channel, "stack", viewer_ack_return_route, monkeypatch, tmp_path,
    )
    metadata = labels.metadata.replace_fields(
        source_image_provenance_planes=SourceImageProvenancePlanes(
            labels.source_image_provenance_planes.planes[:plane_count]
        ),
    )
    request = replace(
        saves[0][3][ViewerStreamKwarg.STREAM_REQUEST.value],
        display_config=ComponentDisplayConfig(Microscopy.Channel, "layer"),
    )
    kwargs = ViewerStreamBackendCallKwargs(ViewerStreamBackendKwargs(request))
    output = Output(
        path=saves[0][1], content=pixels[:plane_count], metadata=metadata,
        variable_components=(Microscopy.Channel,),
    )
    with pytest.raises(ValueError, match="requires batch saving"):
        kwargs.to_filemanager_kwargs(output)
    batches = kwargs.filemanager_batches((output,))
    projected = [item for items, _kwargs in batches for item in items]
    assert len(projected) == plane_count
    assert len({item.path for item in projected}) == plane_count
    for index, item in enumerate(projected):
        np.testing.assert_array_equal(item.content, pixels[index])
        assert np.shares_memory(item.content, pixels)
        assert item.metadata.plane_axis is None
        assert item.source_component_metadata["channel"] == index + 1
    assert metadata.plane_axis is RuntimePlaneAxis.SOURCE_BINDING
    np.testing.assert_array_equal(output.content, pixels[:plane_count])


@pytest.mark.parametrize(
    ("domain", "error"),
    (({"channel": [1]}, "cardinality mismatch"),
     ({"channel": [1, 99]}, "outside the viewer domain"),
     ({"site": [1, 2], "channel": [1, 2]}, "more component axes")),
)
def test_strict_aggregate_receiver_rejects_malformed_tiff_domains(
    domain, error, viewer_ack_return_route, monkeypatch, tmp_path,
):
    _labels, _pixels, saves, batches = _automatic_label_tiff(
        Microscopy.Channel, "stack", viewer_ack_return_route, monkeypatch, tmp_path,
    )
    received, semantics = _received_item(batches[0], saves[0][0])
    received = replace(received, plane_component_domain=ViewerComponentValueDomainPayload.from_ordered_wire_mapping(
        domain, context="deliberately malformed incoming TIFF domain",
    ))
    with pytest.raises(ValueError, match=error):
        NapariAggregateAxisBindingAuthority.bindings((received,), semantics)


def test_strict_receiver_rejects_duplicate_plane_coordinates(viewer_ack_return_route, monkeypatch, tmp_path):
    _labels, _pixels, _saves, batches = _automatic_label_tiff(
        Microscopy.Channel, "stack", viewer_ack_return_route, monkeypatch, tmp_path,
    )
    wire = batches[0].batch_images[0]
    domain = {**wire["plane_component_values"], "channel": ["1", "1"]}
    with pytest.raises(ValueError, match="coordinates must be unique"):
        ViewerComponentValueDomainPayload.from_ordered_wire_mapping(
            domain, context="duplicate incoming pixel-plane coordinate",
        )


def test_strict_receiver_rejects_inconsistent_item_plane_domains(viewer_ack_return_route, monkeypatch, tmp_path):
    _labels, _pixels, saves, batches = _automatic_label_tiff(
        Microscopy.Channel, "stack", viewer_ack_return_route, monkeypatch, tmp_path,
    )
    received, semantics = _received_item(batches[0], saves[0][0])
    reversed_item = replace(
        received, plane_component_domain=ViewerComponentValueDomainPayload.from_ordered_wire_mapping(
            {"channel": [2, 1]}, context="contradictory second item pixel-plane order",
        ),
    )
    with pytest.raises(ValueError, match="inconsistent plane component domains"):
        NapariAggregateAxisBindingAuthority.bindings((received, reversed_item), semantics)


@pytest.mark.parametrize("component", (Microscopy.Channel, Microscopy.Site))
def test_existing_projection_owns_source_binding_label_planes(component):
    labels, pixels = _source_bound_labels(component)
    payload = labels.metadata.attach_to(labels.image_data())
    items = RequiredSourceComponentMetadata.project_payload_items(
        RuntimeProjectionSourceIdentityRequest(
            value=payload, source_description="automatic label TIFF",
            variable_components=(component,),
            plane_projection=RuntimePlaneAxisValueProjection.preserve(
                axis=RuntimePlaneAxis.SOURCE_BINDING, axis_size=2,
            ),
        )
    )
    assert len(items) == 2
    for index, item in enumerate(items):
        np.testing.assert_array_equal(item.data, pixels[index])
        assert item.metadata.plane_axis is None
        assert item.require_source_component_metadata()[component.name] == index + 1
        assert item.metadata.source_voxel_spacing.values_zyx == (0.75, 0.75)
        assert np.shares_memory(item.data, labels.image_data())


def test_existing_projection_does_not_infer_runtime_axis_from_label_array():
    labels, _pixels = _source_bound_labels(Microscopy.Channel)
    with pytest.raises(RuntimeSliceProjectionDeclarationError, match="requires a nominal payload"):
        RequiredSourceComponentMetadata.project_payload_items(
            RuntimeProjectionSourceIdentityRequest(
                value=labels.metadata.attach_to(labels.image_data()),
                source_description="automatic label TIFF",
                variable_components=(Microscopy.Channel,),
            )
        )


def test_existing_projection_rejects_label_source_cardinality_mismatch():
    labels, _pixels = _source_bound_labels(Microscopy.Channel)
    with pytest.raises(ValueError, match="metadata cardinality mismatch"):
        RequiredSourceComponentMetadata.project_payload_items(
            RuntimeProjectionSourceIdentityRequest(
                value=labels.metadata.attach_to(labels.image_data()),
                source_description="automatic label TIFF",
                variable_components=(Microscopy.Channel,),
                plane_projection=RuntimePlaneAxisValueProjection.preserve(
                    axis=RuntimePlaneAxis.SOURCE_BINDING, axis_size=3,
                ),
            )
        )
