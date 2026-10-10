"""Ordinary saved-image streaming must reach the strict receiver with owned axes."""

from dataclasses import replace
from hashlib import sha256
from multiprocessing.shared_memory import SharedMemory
from types import SimpleNamespace

import numpy as np
import pytest
from polystore.filemanager import FileManager
from polystore.napari_stream import NapariStreamingBackend
from polystore.streaming import (
    StreamingBatchMessageBuilder,
    StreamingBatchMessageRequest,
)

from openhcs.agent.dto.plate import PlateFileStreamRequest
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.plate_inspection_service import PlateInspectionService
from openhcs.agent.services.plate_streaming_service import PlateStreamingService
from openhcs.constants import Microscope
from openhcs.core.image_file_serialization import ImageFileFormat
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_projection import (
    SourceProjectionMetadataSerializer,
    SourceProjectionSet,
)
from openhcs.core.viewer_streaming_service import (
    ImageStreamingRequest,
    StreamingService,
)
from openhcs.core.virtual_workspace_metadata import AtomicMetadataWriter
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser
from openhcs.runtime.napari_streaming_handlers import (
    NapariAggregateAxisBindingAuthority,
    NapariImagePayloadAxisLabelPolicy,
    NapariStreamLayerItem,
)
from openhcs.runtime.napari_viewer_server import NapariBatchPayload, NapariImagePayload

from test_persisted_output_reopen import NoRuntimeBridge, declared_output


@pytest.fixture
def receiver_transport(monkeypatch, viewer_ack_return_route):
    """Replace only native lifecycle/transport; build and decode actual SHM wire."""
    viewer = NapariStreamingBackend()
    received = []
    allocated = []
    projected_metadata = []
    original_project = ImageStreamingRequest.project_image

    def observe_projection(request, image):
        projected = original_project(request, image)
        projected_metadata.append(projected.metadata)
        return projected

    def receive(_manager, data, paths, backend, **fields):
        assert backend == "napari_stream"
        request = fields["stream_request"]
        built = StreamingBatchMessageBuilder.build(
            viewer,
            StreamingBatchMessageRequest(
                return_route=viewer_ack_return_route,
                data_list=data,
                file_paths=paths,
                stream_request=request,
                component_names_request=viewer.component_names_request(request),
                display_payload_extra=viewer.display_payload_extra(request),
            ),
        )
        batch = NapariBatchPayload.from_json_payload(built.message)
        semantics = batch.axis_projection_semantics()
        for wire in batch.images:
            allocated.append(wire["shm_name"])
            memory = SharedMemory(name=wire["shm_name"])
            try:
                pixels = np.ndarray(
                    wire["shape"], dtype=wire["dtype"], buffer=memory.buf
                ).copy()
            finally:
                memory.close()
            payload = NapariImagePayload.from_payload(
                wire, semantics, batch.viewer_display_config
            )
            item = NapariStreamLayerItem(
                data=pixels,
                producer=payload.producer,
                address=payload.address,
                image_metadata=payload.image_metadata,
                plane_component_domain=payload.plane_component_domain,
            )
            bindings = NapariAggregateAxisBindingAuthority.bindings((item,), semantics)
            NapariImagePayloadAxisLabelPolicy.axis_labels(
                pixels, item.image_metadata, bindings.payload_axes
            )
            received.append((pixels, item, bindings))

    monkeypatch.setattr(
        "openhcs.agent.services.plate_streaming_service.StreamingViewerLifecycle.get_or_create_visualizer",
        lambda **_fields: SimpleNamespace(port=5992),
    )
    monkeypatch.setattr(StreamingService, "_wait_for_viewer_ready", lambda *_: None)
    monkeypatch.setattr(StreamingService, "_require_viewer_settled", lambda *_: None)
    monkeypatch.setattr(FileManager, "save_batch", receive)
    monkeypatch.setattr(ImageStreamingRequest, "project_image", observe_projection)
    try:
        yield received, projected_metadata
    finally:
        viewer.cleanup()
        for name in allocated:
            with pytest.raises(FileNotFoundError):
                SharedMemory(name=name)


@pytest.mark.parametrize("axis", (None, *RuntimePlaneAxis))
def test_public_declared_saved_image_reaches_strict_receiver(
    tmp_path, receiver_transport, axis
):
    inspection, declarations = declared_output(tmp_path / "native", ("FITC",))
    path, expected, projection, _declaration = declarations[0]
    root = path.parent.parent
    metadata = projection.image_metadata.replace_fields(
        source_voxel_spacing=SourceVoxelSpacing((1.3556, 1.3556)),
        plane_axis=axis,
        source_image_provenance_planes=(
            SourceImageProvenancePlanes()
            if axis is None
            else SourceImageProvenancePlanes.from_components(
                paths=(projection.image_metadata.source_path,),
                component_metadata=(
                    projection.image_metadata.source_component_metadata,
                ),
            )
        ),
    )
    image_format = ImageFileFormat.require_path(path)
    pixels = expected if axis is None else expected[None]
    image = metadata.payload_with(pixels)
    image_format.write(path, image)
    projection = replace(
        projection, image_metadata=image_format.persisted_metadata(path, image)
    )
    declaration = SourceProjectionMetadataSerializer(
        SourceSchemaFilenameParser()
    ).metadata_dict(
        SourceProjectionSet((projection,)),
        microscope_handler_name=Microscope.SOURCE_BINDINGS.value,
        source_filename_parser_name="SourceSchemaFilenameParser",
        grid_dimensions=[],
        pixel_size=1.3556,
        projection_paths=((projection, str(path.relative_to(root))),),
    )
    AtomicMetadataWriter().replace_subdirectory_metadata(
        root / "openhcs_metadata.json", path.parent.name, declaration
    )
    before = {
        p: sha256(p.read_bytes()).hexdigest()
        for p in (path, root / "openhcs_metadata.json")
    }
    result = PlateStreamingService(inspection, NoRuntimeBridge()).stream_files(
        PlateFileStreamRequest.from_fields(
            plate_path=str(root), kind="image", file_paths=[str(path)]
        )
    )
    assert result.errors == ()
    assert result.streamed_image_paths == (projection.ref.backend_address,)
    received, projected_metadata = receiver_transport
    assert len(received) == 1
    transmitted, item, bindings = received[0]
    np.testing.assert_array_equal(transmitted, expected)
    assert bindings.payload_axes == ()
    assert item.address.components["channel"] == 2
    # Full lineage remains with the original source owner; the declaration-owned
    # viewer codec deliberately does not serialize hidden provenance records.
    assert projected_metadata[0].source_image_names == ("FITC",)
    assert item.image_metadata.source_voxel_spacing == SourceVoxelSpacing(
        (1.3556, 1.3556)
    )
    assert item.image_metadata.plane_axis is None
    assert before == {p: sha256(p.read_bytes()).hexdigest() for p in before}


def test_plain_persisted_tiff_without_saved_image_metadata_streams(
    tmp_path, receiver_transport
):
    # Independent native ImageXpress branch, with no saved image_metadata or
    # imported broad inspection-test module. Explicit folders own nondefault Z/T.
    root = tmp_path / "plain"
    image_dir = root / "TimePoint_3" / "ZStep_5"
    image_dir.mkdir(parents=True)
    (root / "plain.HTD").write_text(
        '"XSites", 1\n"YSites", 1\n"PixelSizeUM", 0.5\n', encoding="utf-8"
    )
    paths = (image_dir / "plain_A01_s1_w2.tif",)
    expected = np.arange(30, dtype=np.uint16).reshape(5, 6)
    for path in paths:
        ImageFileFormat.require_path(path).write(path, expected)
    assert not (root / "openhcs_metadata.json").exists()
    inspection = PlateInspectionService(
        AgentPathPolicy.with_roots(readable_roots=(root,), writable_roots=())
    )
    result = PlateStreamingService(inspection, NoRuntimeBridge()).stream_files(
        PlateFileStreamRequest.from_fields(
            plate_path=str(root), kind="image", file_paths=[str(path) for path in paths]
        )
    )
    assert result.errors == ()
    received, _projected_metadata = receiver_transport
    assert len(received) == 1
    for transmitted, item, bindings in received:
        np.testing.assert_array_equal(transmitted, expected)
        assert item.image_metadata.plane_axis is None
        assert bindings.payload_axes == ()
        assert item.image_metadata.source_voxel_spacing == SourceVoxelSpacing(
            (0.5, 0.5)
        )
        assert item.address.components["z_index"] == 5
        assert item.address.components["timepoint"] == 3
    assert not (root / "openhcs_metadata.json").exists()
