from __future__ import annotations

from dataclasses import replace
from pathlib import Path
from types import MappingProxyType
from types import SimpleNamespace

import numpy as np
import pytest
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
from polystore.roi import ROI, PointShape
from polystore.roi_converters import NapariROIConverter
from polystore.streaming.identity import (
    FixedStreamProducerIdentityKind,
    StreamProducerIdentity,
)
from polystore.streaming.viewer_transport import ViewerStreamKwarg, ViewerStreamProducer
from polystore.virtual_workspace import SourcePixelRef
from polystore.zmq_config import POLYSTORE_ZMQ_CONFIG
from zmqruntime.viewer_protocol import ViewerBatchWireField, ViewerWireField
from zmqruntime.viewer_state import ViewerStateManager

from openhcs.constants.constants import AllComponents
from openhcs.core.artifacts import ObjectLabelsArtifactType
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.components.parser_metaprogramming import FilenameParseResult
from openhcs.core.config import (
    FijiDimensionMode,
    FijiStreamingConfig,
    GlobalPipelineConfig,
    NapariDimensionMode,
    NapariStreamingConfig,
    PipelineConfig,
    StreamingConfig,
    get_all_streaming_ports,
)
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_payload_data,
)
from openhcs.core.roi_source_metadata import ROIArchiveSourceMetadata
from openhcs.core.measurement_row_materialization import MeasurementSparseColumnarRows
from openhcs.core.runtime_measurements import (
    MeasurementScope,
    MeasurementSubject,
    MeasurementTable,
    ObjectCoreMeasurementFeature,
)
from openhcs.core.runtime_tabular_values import FieldSpec
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_metadata import SourceVoxelSpacing, SourceVoxelSpacingUnit
from openhcs.core.source_projection import SourceArtifactProjection
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.source_workspace_projection import VirtualWorkspaceSourceProjection
from openhcs.core.streaming_config_declarations import ViewerType
from openhcs.core.streaming_config_factory import ViewerProcessLaunchConfig
from openhcs.core.viewer_streaming_service import (
    ImageStreamingRequest,
    ManualImageStreamProjectionIdentity,
    RoiStreamingRequest,
    StreamingService,
    StreamingViewerLifecycle,
)
from openhcs.runtime.fiji_stream_visualizer import FijiStreamVisualizer
from openhcs.runtime.napari_stream_visualizer import NapariStreamVisualizer
from openhcs.runtime.viewer_protocol import (
    DetachedViewerLaunchFailure,
    DetachedViewerServerEntrypointSpec,
    ManagedViewerLifecycleMixin,
    ViewerControlMessageRequest,
    ViewerControlResponse,
    ViewerLaunchContext,
)
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG
from openhcs.runtime.viewer_component_system import (
    ViewerComponentAxisSemantics,
    ViewerComponentValueDomainPayload,
    ViewerLayerAxisProjectionRequestAuthority,
    ViewerLayerAxisProjector,
    ViewerObjectDisplayConfigInput,
    ViewerRouteComponentValueTracker,
)
from openhcs.processing.materialization import (
    MaterializationSpec,
    PointROIOptions,
    materialize,
)


class FakeFileManager:
    def __init__(self) -> None:
        self.saved_batches: list[tuple[list[object], list[str], str, dict]] = []

    def load(self, path: str, read_backend: str):
        return np.zeros((4, 5), dtype=np.uint16)

    def resolve_address(self, address: str, backend: str, *, base_path: Path):
        del backend
        return str(base_path / address)

    def exists(self, path, backend):
        return False

    def physical_source_path(self, path, backend, *, base_path=None):
        return None

    def save_batch(
        self,
        data_list: list[object],
        file_paths: list[str],
        backend: str,
        **metadata,
    ) -> None:
        self.saved_batches.append((data_list, file_paths, backend, metadata))


class FakeRuntimeEndpoint:
    def wait_ready(self, *, timeout: float, require_ready: bool) -> bool:
        del timeout, require_ready
        return True


class FakeViewer:
    port = 5565
    runtime_endpoint = FakeRuntimeEndpoint()

    def __init__(self, *, settlement_succeeds: bool = True) -> None:
        self.settlement_succeeds = settlement_succeeds
        self.settlement_calls = 0

    def settle_viewer_state(self) -> bool:
        self.settlement_calls += 1
        return self.settlement_succeeds


class FakeMetadataHandler:
    def source_workspace_metadata_document(self, plate_path):
        return None

    def find_metadata_file(self, root: Path) -> Path:
        return root

    def get_component_values(
        self,
        root: Path,
        component_name: str,
    ) -> dict[str, str]:
        return {}

    def source_voxel_spacing(self, plate_path) -> SourceVoxelSpacing:
        del plate_path
        return SourceVoxelSpacing((1.3556, 1.3556))


def filename_parse_result(*, channel: int = 1) -> FilenameParseResult:
    values = {
        AllComponents.WELL: "A01",
        AllComponents.SITE: 1,
        AllComponents.CHANNEL: channel,
        AllComponents.Z_INDEX: 1,
        AllComponents.TIMEPOINT: 1,
    }
    return FilenameParseResult(values.items(), extension=".tif")


def test_streaming_config_separates_registry_key_from_viewer_identity() -> None:
    assert set(StreamingConfig.__registry__) == {
        ViewerType.NAPARI,
        ViewerType.FIJI,
    }

    assert NapariStreamingConfig().streaming_config_key == "napari_streaming_config"
    assert NapariStreamingConfig().viewer_type is ViewerType.NAPARI
    assert FijiStreamingConfig().streaming_config_key == "fiji_streaming_config"
    assert FijiStreamingConfig().viewer_type is ViewerType.FIJI
    assert "source" not in NapariStreamingConfig().component_modes()
    assert "source" not in FijiStreamingConfig().component_modes()

    assert StreamingConfig.supported_config_keys() == (
        "fiji_streaming_config",
        "napari_streaming_config",
    )
    assert (
        StreamingConfig.display_name_for_config_key("fiji_streaming_config") == "Fiji"
    )
    assert NapariStreamingConfig().display_name == "Napari"


def test_napari_streaming_config_owns_process_launch_projection() -> None:
    assert NapariStreamingConfig(
        font_dpi=96
    ).viewer_runtime_config().process_launch == ViewerProcessLaunchConfig(
        qt_font_dpi=96
    )
    assert (
        FijiStreamingConfig().viewer_runtime_config().process_launch
        == ViewerProcessLaunchConfig()
    )


def test_napari_viewer_reuse_requires_matching_process_launch(monkeypatch) -> None:
    visualizer = NapariStreamVisualizer(
        filemanager=FakeFileManager(),
        runtime_config=NapariStreamingConfig(
            enabled=True,
            font_dpi=96,
        ).viewer_runtime_config(),
    )
    active_launch = ViewerProcessLaunchConfig(qt_font_dpi=96)

    monkeypatch.setattr(
        ViewerControlMessageRequest,
        "send",
        lambda _request: ViewerControlResponse(
            {
                "status": "success",
                "process_launch": active_launch.to_wire_mapping(),
            }
        ),
    )
    assert visualizer.matches_requested_process_launch(visualizer.process_launch)

    active_launch = ViewerProcessLaunchConfig(qt_font_dpi=120)
    assert not visualizer.matches_requested_process_launch(visualizer.process_launch)


@pytest.mark.parametrize("config", (GlobalPipelineConfig(), PipelineConfig()))
def test_all_streaming_ports_read_declared_registry_fields(config) -> None:
    ports = get_all_streaming_ports(config, num_ports_per_type=1)

    assert set(ports) == {5555, 5565}


def test_streaming_config_component_modes_apply_display_defaults() -> None:
    assert NapariStreamingConfig().component_modes() == {
        component: NapariDimensionMode.STACK.value
        for component in NapariStreamingConfig.COMPONENT_ORDER
    }
    assert FijiStreamingConfig().component_modes() == {
        "site": FijiDimensionMode.FRAME.value,
        "timepoint": FijiDimensionMode.FRAME.value,
        "channel": FijiDimensionMode.CHANNEL.value,
        "z_index": FijiDimensionMode.SLICE.value,
        "well": FijiDimensionMode.FRAME.value,
    }


def test_napari_dimension_modes_distinguish_layers_from_slices() -> None:
    assert tuple(NapariDimensionMode) == (
        NapariDimensionMode.LAYER,
        NapariDimensionMode.STACK,
    )
    assert NapariDimensionMode.LAYER.value == "layer"
    assert (
        NapariStreamingConfig(
            site_mode=NapariDimensionMode.LAYER,
        ).component_modes()["site"]
        == "layer"
    )
    with pytest.raises(ValueError):
        NapariDimensionMode("slice")


def test_stream_images_uses_resolved_config_backend_not_viewer_name(
    monkeypatch,
) -> None:
    monkeypatch.setattr(
        "openhcs.core.viewer_streaming_service.spawn_thread_with_context",
        lambda worker, name: worker(),
    )
    filemanager = FakeFileManager()
    config = FijiStreamingConfig(enabled=True)
    statuses: list[str] = []
    errors: list[str] = []
    transport_config = replace(
        OPENHCS_ZMQ_CONFIG,
        ipc_socket_prefix="test-openhcs-zmq",
    )

    service = StreamingService(
        filemanager=filemanager,
        microscope_handler=SimpleNamespace(
            parser=SimpleNamespace(
                parse_filename=lambda filename: (
                    filename_parse_result() if filename == "img.tif" else None
                )
            ),
            metadata_handler=FakeMetadataHandler(),
        ),
        plate_path=Path("/plate"),
        transport_config=transport_config,
    )
    viewer = FakeViewer()
    service.stream_images_async(
        ImageStreamingRequest(
            viewer=viewer,
            config=config,
            status_callback=statuses.append,
            error_callback=errors.append,
            filenames=("A01/img.tif",),
            read_backend="disk",
        )
    )

    assert errors == []
    assert viewer.settlement_calls == 1
    assert filemanager.saved_batches
    _data, _paths, backend, metadata = filemanager.saved_batches[0]
    assert backend == config.backend.value
    stream_request = metadata[ViewerStreamKwarg.STREAM_REQUEST.value]
    assert stream_request.display_config is config
    assert stream_request.host == config.host
    assert stream_request.transport_mode is config.transport_mode
    assert (
        stream_request.transport_config.resolve(POLYSTORE_ZMQ_CONFIG)
        is transport_config
    )
    assert stream_request.source.metadata.metadata_by_path == {
        "A01/img.tif": {
            "well": "A01",
            "site": 1,
            "channel": 1,
            "z_index": 1,
            "timepoint": 1,
        }
    }
    assert stream_request.message_extra[
        ViewerBatchWireField.COMPONENT_VALUE_DOMAIN.value
    ] == {
        "site": [1],
        "timepoint": [1],
        "channel": [1],
        "z_index": [1],
        "well": ["A01"],
    }
    assert stream_request.producer.identities[0].to_payload() == {
        "origin": "manual",
        "output_kind": "manual",
        "output_key": "selected_images",
        "projection_key": ManualImageStreamProjectionIdentity(
            plate_path="/plate",
            filenames=("A01/img.tif",),
        )
        .producer_identity()
        .projection_key,
        "step_name": None,
        "pipeline_position": None,
        "step_scope_id": None,
        "invocation_key": None,
        "artifact_kind": None,
    }


@pytest.mark.parametrize(
    "config", (FijiStreamingConfig(enabled=True), NapariStreamingConfig(enabled=True))
)
@pytest.mark.parametrize(
    "spacing",
    (
        SourceVoxelSpacing(),
        SourceVoxelSpacing((2.0, 0.4, 0.7)),
        SourceVoxelSpacing((1.0, 2.0), SourceVoxelSpacingUnit.RELATIVE),
    ),
)
def test_stream_images_uses_plate_calibration_without_overwriting_native_spacing(
    config,
    spacing,
) -> None:
    pixels = np.arange(20, dtype=np.uint16).reshape(4, 5)

    class CalibratedFileManager(FakeFileManager):
        def load(self, path, read_backend):
            return ImagePayloadMetadata(source_voxel_spacing=spacing).payload_with(
                pixels
            )

    class CalibratedMetadataHandler(FakeMetadataHandler):
        def source_voxel_spacing(self, plate_path):
            if spacing.has_values:
                raise AssertionError("Native calibration must not query plate defaults")
            return super().source_voxel_spacing(plate_path)

    filemanager = CalibratedFileManager()
    service = StreamingService(
        filemanager=filemanager,
        microscope_handler=SimpleNamespace(
            parser=SimpleNamespace(
                parse_filename=lambda _name: filename_parse_result()
            ),
            metadata_handler=CalibratedMetadataHandler(),
        ),
        plate_path=Path("/plate"),
    )
    result = service.stream_images(
        ImageStreamingRequest(
            viewer=FakeViewer(),
            config=config,
            status_callback=lambda _message: None,
            error_callback=lambda error: (_ for _ in ()).throw(AssertionError(error)),
            filenames=("A01/img.tif",),
            read_backend="disk",
        )
    )
    assert result.streamed_count == 1
    data, _paths, _backend, metadata = filemanager.saved_batches[0]
    expected = spacing if spacing.has_values else SourceVoxelSpacing((1.3556, 1.3556))
    np.testing.assert_array_equal(image_payload_data(data[0]), pixels)
    stream_request = metadata[ViewerStreamKwarg.STREAM_REQUEST.value]
    wire_metadata = ImagePayloadMetadata.from_viewer_image_metadata(
        stream_request.source.item_fields[ViewerWireField.IMAGE_METADATA.value]
    )
    assert wire_metadata.source_voxel_spacing == expected


def test_manual_image_projection_identity_separates_independent_selections() -> None:
    first = ManualImageStreamProjectionIdentity(
        plate_path="/plate",
        filenames=("A60/channel-1.tif", "A60/channel-2.tif"),
    ).producer_identity()
    reordered = ManualImageStreamProjectionIdentity(
        plate_path="/plate",
        filenames=("A60/channel-2.tif", "A60/channel-1.tif"),
    ).producer_identity()
    second = ManualImageStreamProjectionIdentity(
        plate_path="/plate",
        filenames=("A03/channel-1.tif",),
    ).producer_identity()

    assert first.output_key == second.output_key == "selected_images"
    assert first.projection_key == reordered.projection_key
    assert first.projection_key != second.projection_key
    assert first.route_parts() != second.route_parts()


def test_stream_images_reports_success_only_after_viewer_state_is_settled() -> None:
    events: list[str] = []

    class SettledStateViewer(FakeViewer):
        layer_state: dict[str, object] | None = None

        def settle_viewer_state(self) -> bool:
            events.append("settle")
            self.layer_state = {
                "mounted": True,
                "pending_update": False,
                "axis_labels": ("channel", "y", "x"),
                "payload_nonzero_counts": (4, 5),
                "component_values": (
                    {"channel": 1},
                    {"channel": 2},
                ),
            }
            return super().settle_viewer_state()

    viewer = SettledStateViewer()
    statuses: list[str] = []

    def record_status(message: str) -> None:
        statuses.append(message)
        if not message.startswith("Streamed "):
            return
        events.append("success")
        state = viewer.layer_state
        assert state is not None
        assert state["mounted"] is True
        assert state["pending_update"] is False
        assert state["axis_labels"] == ("channel", "y", "x")
        assert all(state["payload_nonzero_counts"])
        coordinates = tuple(
            tuple(sorted(values.items())) for values in state["component_values"]
        )
        assert len(coordinates) == len(set(coordinates))

    filemanager = FakeFileManager()
    service = StreamingService(
        filemanager=filemanager,
        microscope_handler=SimpleNamespace(
            parser=SimpleNamespace(
                parse_filename=lambda filename: filename_parse_result(
                    channel=int(filename[1])
                )
            ),
            metadata_handler=FakeMetadataHandler(),
        ),
        plate_path=Path("/plate"),
    )

    result = service.stream_images(
        ImageStreamingRequest(
            viewer=viewer,
            config=NapariStreamingConfig(enabled=True),
            status_callback=record_status,
            error_callback=lambda error: (_ for _ in ()).throw(AssertionError(error)),
            filenames=("w1.tif", "w2.tif"),
            read_backend="disk",
        )
    )

    assert result.streamed_count == 2
    assert events == ["settle", "success"]
    assert viewer.settlement_calls == 1


def test_stream_images_derives_rgb_channel_axis_before_viewer_dispatch(
    tmp_path: Path,
) -> None:
    import tifffile

    path = tmp_path / "A01_s001_wDNA_z001_t001.tif"
    tifffile.imwrite(path, np.zeros((8, 9, 3), dtype=np.uint8), photometric="rgb")

    class DiskFileManager(FakeFileManager):
        def load(self, path: str, read_backend: str) -> np.ndarray:
            assert read_backend == "disk"
            return tifffile.imread(path)

        def physical_source_path(
            self,
            address: str,
            backend: str,
            *,
            base_path: Path,
        ) -> Path | None:
            del backend, base_path
            return Path(address)

    filemanager = DiskFileManager()
    service = StreamingService(
        filemanager=filemanager,
        microscope_handler=SimpleNamespace(
            parser=SimpleNamespace(
                parse_filename=lambda _filename: filename_parse_result()
            ),
            metadata_handler=FakeMetadataHandler(),
        ),
        plate_path=tmp_path,
    )

    service.stream_images(
        ImageStreamingRequest(
            viewer=FakeViewer(),
            config=NapariStreamingConfig(enabled=True),
            status_callback=lambda _status: None,
            error_callback=lambda error: (_ for _ in ()).throw(AssertionError(error)),
            filenames=(path.name,),
            read_backend="disk",
        )
    )

    assert len(filemanager.saved_batches) == 1
    _data, _paths, _backend, kwargs = filemanager.saved_batches[0]
    stream_request = kwargs[ViewerStreamKwarg.STREAM_REQUEST.value]
    item_fields = dict(stream_request.source.item_fields)
    image_metadata = item_fields.pop("image_metadata")
    assert image_metadata["source_channel_axis"] == -1
    assert image_metadata["source_spatial_domain"]["origin_yx"] == [0, 0]
    assert item_fields == {
        "source_spatial_shape_yx": [8, 9],
        "spatial_origin_yx": [0, 0],
        "source_channel_axis": -1,
    }


def test_stream_images_projects_declared_channel_singleton_with_retained_plane_axis(
    tmp_path: Path,
) -> None:
    import tifffile

    path = tmp_path / "A01_s001_wDNA_z001_t001.tif"
    tifffile.imwrite(
        path,
        np.zeros((3, 8, 9), dtype=np.uint16),
        photometric="minisblack",
    )

    class DiskFileManager(FakeFileManager):
        def load(self, path: str, read_backend: str) -> np.ndarray:
            assert read_backend == "disk"
            return tifffile.imread(path)

        def physical_source_path(
            self,
            address: str,
            backend: str,
            *,
            base_path: Path,
        ) -> Path | None:
            del backend, base_path
            return Path(address)

    filemanager = DiskFileManager()
    viewer = FakeViewer()
    service = StreamingService(
        filemanager=filemanager,
        microscope_handler=SimpleNamespace(
            parser=SimpleNamespace(
                parse_filename=lambda _filename: filename_parse_result()
            ),
            metadata_handler=FakeMetadataHandler(),
        ),
        plate_path=tmp_path,
    )

    service.stream_images(
        ImageStreamingRequest(
            viewer=viewer,
            config=NapariStreamingConfig(enabled=True),
            status_callback=lambda _status: None,
            error_callback=lambda error: (_ for _ in ()).throw(AssertionError(error)),
            filenames=(path.name,),
            read_backend="disk",
        )
    )

    assert len(filemanager.saved_batches) == 1
    assert viewer.settlement_calls
    _data, _paths, _backend, kwargs = filemanager.saved_batches[0]
    stream_request = kwargs[ViewerStreamKwarg.STREAM_REQUEST.value]
    item_fields = dict(stream_request.source.item_fields)
    image_metadata = item_fields.pop("image_metadata")
    assert image_metadata["plane_axis"] is None
    assert image_metadata["source_channel_axis"] is None
    assert item_fields == {
        "source_spatial_shape_yx": [8, 9],
        "spatial_origin_yx": [0, 0],
    }


def test_stream_images_routes_aggregate_channel_through_payload_plane_axis(
    tmp_path: Path,
) -> None:
    path = tmp_path / "aggregate.labels.tif"
    expected = np.arange(2 * 8 * 9, dtype=np.int32).reshape(2, 8, 9)

    class AggregateFileManager(FakeFileManager):
        def load(self, path: str, read_backend: str) -> np.ndarray:
            assert path == str(tmp_path / "aggregate.labels.tif")
            assert read_backend == "disk"
            return expected

        def source_path(
            self,
            address: str,
            backend: str,
            *,
            base_path: str | Path,
        ) -> str:
            del backend, base_path
            return address

    source_metadata = MappingProxyType(
        {
            "well": "A49",
            "site": "1",
            "z_index": "1",
            "timepoint": "1",
            "source_alias": "neurite_outgrowth",
            "source_artifact_type": "object_labels",
        }
    )
    image_metadata = ImagePayloadMetadata(
        source_spatial_domain=SourceSpatialDomain((0, 0), (8, 9)),
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/source/channel-1.tif", "/source/channel-2.tif"),
            component_metadata=(
                {**source_metadata, "channel": "1"},
                {**source_metadata, "channel": "2"},
            ),
        ),
        source_dtype="int32",
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    )
    projection = SourceArtifactProjection(
        address=None,
        ref=SourcePixelRef(backend="disk", backend_address=str(path)),
        source_alias="neurite_outgrowth",
        artifact_kind=ObjectLabelsArtifactType,
        source_metadata=source_metadata,
        image_metadata=image_metadata,
        execution_scope=RuntimeExecutionAxisScope.from_raw(
            "A49",
            component=None,
            value=None,
            fixed_component_values=(("z_index", "1"), ("timepoint", "1")),
        ),
    )
    workspace_projection = VirtualWorkspaceSourceProjection(
        source_refs_by_virtual_path=MappingProxyType({path.name: projection.ref}),
        source_metadata_by_path=MappingProxyType({path.name: source_metadata}),
        workspace_root=str(tmp_path),
        source_projections_by_virtual_path=MappingProxyType({path.name: projection}),
    )
    filemanager = AggregateFileManager()
    service = StreamingService(
        filemanager=filemanager,
        microscope_handler=SimpleNamespace(
            parser=SimpleNamespace(parse_filename=lambda _filename: None),
            metadata_handler=FakeMetadataHandler(),
        ),
        plate_path=tmp_path,
    )

    service.stream_images(
        ImageStreamingRequest(
            viewer=FakeViewer(),
            config=NapariStreamingConfig(enabled=True),
            status_callback=lambda _status: None,
            error_callback=lambda error: (_ for _ in ()).throw(AssertionError(error)),
            filenames=(path.name,),
            read_backend="disk",
            source_projection=workspace_projection,
        )
    )

    assert len(filemanager.saved_batches) == 1
    _data, _paths, _backend, kwargs = filemanager.saved_batches[0]
    stream_request = kwargs[ViewerStreamKwarg.STREAM_REQUEST.value]
    assert stream_request.source.item_fields["plane_component_values"] == {
        "channel": ["1", "2"]
    }
    assert stream_request.source.metadata.metadata_by_path == {
        path.name: {
            "well": "A49",
            "site": 1,
            "z_index": 1,
            "timepoint": 1,
        }
    }
    assert stream_request.message_extra[
        ViewerBatchWireField.COMPONENT_VALUE_DOMAIN.value
    ]["channel"] == [1, 2]


def test_stream_images_does_not_report_success_when_viewer_settlement_fails() -> None:
    statuses: list[str] = []
    viewer = FakeViewer(settlement_succeeds=False)
    service = StreamingService(
        filemanager=FakeFileManager(),
        microscope_handler=SimpleNamespace(
            parser=SimpleNamespace(
                parse_filename=lambda _filename: filename_parse_result()
            ),
            metadata_handler=FakeMetadataHandler(),
        ),
        plate_path=Path("/plate"),
    )

    with pytest.raises(RuntimeError, match="Failed to settle streamed updates"):
        service.stream_images(
            ImageStreamingRequest(
                viewer=viewer,
                config=NapariStreamingConfig(enabled=True),
                status_callback=statuses.append,
                error_callback=lambda _error: None,
                filenames=("w1.tif",),
                read_backend="disk",
            )
        )

    assert viewer.settlement_calls == 1
    assert all(not status.startswith("Streamed ") for status in statuses)


def test_stream_rois_supplies_per_path_component_metadata_from_artifact_name(
    monkeypatch,
) -> None:
    monkeypatch.setattr(
        "openhcs.core.viewer_streaming_service.spawn_thread_with_context",
        lambda worker, name: worker(),
    )
    monkeypatch.setattr(
        "polystore.roi.load_rois_from_zip",
        lambda _path: [ROI(shapes=[PointShape(1, 2)])],
    )
    filemanager = FakeFileManager()
    config = FijiStreamingConfig(enabled=True)
    roi_filename = "A01_s001_w1_z001_t001_Nuclei_step3_rois.roi.zip"
    microscope_handler = SimpleNamespace(
        parser=SimpleNamespace(
            parse_filename=lambda filename: (
                filename_parse_result()
                if filename == "A01_s001_w1_z001_t001.tif"
                else None
            )
        ),
        metadata_handler=FakeMetadataHandler(),
    )

    service = StreamingService(
        filemanager=filemanager,
        microscope_handler=microscope_handler,
        plate_path=Path("/plate"),
    )
    service.stream_rois_async(
        RoiStreamingRequest(
            viewer=FakeViewer(),
            config=config,
            status_callback=lambda _status: None,
            error_callback=lambda error: (_ for _ in ()).throw(AssertionError(error)),
            roi_filenames=(roi_filename,),
        )
    )

    assert filemanager.saved_batches
    _data, _paths, _backend, metadata = filemanager.saved_batches[0]
    stream_request = metadata[ViewerStreamKwarg.STREAM_REQUEST.value]
    assert stream_request.source.metadata.metadata_by_path[roi_filename] == {
        "well": "A01",
        "site": 1,
        "channel": 1,
        "z_index": 1,
        "timepoint": 1,
    }
    assert stream_request.message_extra[
        ViewerBatchWireField.COMPONENT_VALUE_DOMAIN.value
    ] == {
        "site": [1],
        "timepoint": [1],
        "channel": [1],
        "z_index": [1],
        "well": ["A01"],
    }


def test_stream_rois_uses_explicit_component_metadata(monkeypatch) -> None:
    monkeypatch.setattr(
        "polystore.roi.load_rois_from_zip",
        lambda _path: [ROI(shapes=[PointShape(1, 2)])],
    )
    filemanager = FakeFileManager()
    config = FijiStreamingConfig(enabled=True)
    roi_path = "/output/images_results/A01_w2_rois.roi.zip"
    service = StreamingService(
        filemanager=filemanager,
        microscope_handler=SimpleNamespace(
            parser=SimpleNamespace(
                parse_filename=lambda _filename: (_ for _ in ()).throw(
                    AssertionError("parser fallback used")
                )
            ),
            metadata_handler=FakeMetadataHandler(),
        ),
        plate_path=Path("/plate"),
    )

    viewer = FakeViewer()
    service.stream_rois(
        RoiStreamingRequest(
            viewer=viewer,
            config=config,
            status_callback=lambda _status: None,
            error_callback=lambda error: (_ for _ in ()).throw(AssertionError(error)),
            roi_filenames=(roi_path,),
            component_metadata_by_path={
                roi_path: {
                    "well": "A01",
                    "site": 1,
                    "channel": 2,
                    "z_index": 1,
                    "timepoint": 1,
                }
            },
        )
    )

    assert viewer.settlement_calls == 1
    assert filemanager.saved_batches
    _data, _paths, _backend, metadata = filemanager.saved_batches[0]
    stream_request = metadata[ViewerStreamKwarg.STREAM_REQUEST.value]
    assert stream_request.source.metadata.metadata_by_path[roi_path] == {
        "well": "A01",
        "site": 1,
        "channel": 2,
        "z_index": 1,
        "timepoint": 1,
    }
    image_metadata = ImagePayloadMetadata.from_viewer_image_metadata(
        stream_request.source.item_fields[ViewerWireField.IMAGE_METADATA.value]
    )
    assert image_metadata.source_voxel_spacing == SourceVoxelSpacing((1.3556, 1.3556))


@pytest.mark.parametrize("config_type", [FijiStreamingConfig, NapariStreamingConfig])
def test_reopen_native_roi_archives_preserves_per_file_source_and_calibration(
    tmp_path, config_type, monkeypatch
):
    from polystore.disk import DiskStorageBackend

    paths = []
    metadata_items = []
    for channel, spacing in [(3, (0.65, 0.65)), (4, (2.0, 0.8, 0.8))]:
        metadata = ImagePayloadMetadata(
            source_path=f"/actual/source/channel-{channel}.tif",
            source_component_metadata={
                "well": "B02",
                "site": 1,
                "channel": channel,
                "z_index": 7,
                "timepoint": 1,
            },
            source_spatial_domain=SourceSpatialDomain(
                origin_yx=(10, 20), source_shape_yx=(100, 200)
            ),
            source_voxel_spacing=SourceVoxelSpacing(spacing),
        )
        path = tmp_path / f"misleading_A01_w{channel}.roi.zip"
        DiskStorageBackend().save(
            ROIArchiveSourceMetadata.bind(
                [ROI([PointShape(32.25, 40.5)], {"label": channel})], metadata
            ),
            path,
        )
        paths.append(str(path))
        metadata_items.append(metadata)
    filemanager = FakeFileManager()
    metadata_handler = FakeMetadataHandler()
    monkeypatch.setattr(
        metadata_handler,
        "source_voxel_spacing",
        lambda _path: pytest.fail("Native explicit spacing must not be replaced"),
    )
    handler = SimpleNamespace(
        parser=SimpleNamespace(
            parse_filename=lambda _filename: pytest.fail(
                "Native metadata must not use a filename guess"
            )
        ),
        metadata_handler=metadata_handler,
    )
    result = StreamingService(filemanager, handler, Path("/actual/source")).stream_rois(
        RoiStreamingRequest(
            viewer=FakeViewer(),
            config=config_type(enabled=True),
            status_callback=lambda _status: None,
            error_callback=lambda error: pytest.fail(error),
            roi_filenames=tuple(paths),
            require_source_metadata=True,
        )
    )
    assert result.streamed_paths == tuple(paths)
    assert len(filemanager.saved_batches) == 2
    for (data, batch_paths, _backend, kwargs), expected in zip(
        filemanager.saved_batches, metadata_items, strict=True
    ):
        stream = kwargs[ViewerStreamKwarg.STREAM_REQUEST.value]
        metadata = ImagePayloadMetadata.from_viewer_image_metadata(
            stream.source.item_fields[ViewerWireField.IMAGE_METADATA.value]
        )
        assert metadata.source_voxel_spacing == expected.source_voxel_spacing
        assert metadata.source_spatial_domain == expected.source_spatial_domain
        assert (
            stream.source.metadata.metadata_by_path[batch_paths[0]]
            == expected.source_component_metadata
        )
        assert ROIArchiveSourceMetadata.feature_metadata(data[0][0].metadata) == {
            "label": expected.source_component_metadata["channel"]
        }
        assert ROIArchiveSourceMetadata.decode(data[0]) == expected
        assert data[0][0].shapes == [PointShape(32.25, 40.5)]


def test_3d_point_archive_reopens_with_native_z_domain_and_features(tmp_path):
    import tifffile

    source_directory = tmp_path / "source"
    source_directory.mkdir()
    source_paths = tuple(
        str(source_directory / f"A01_s001_w1_z{z + 1:03d}_t001.tif") for z in range(4)
    )
    for z, path in enumerate(source_paths):
        source_pixels = np.zeros((8, 8), dtype=np.uint16)
        if z == 2:
            source_pixels[1:3, 3:5] = 2048
        tifffile.imwrite(path, source_pixels)
    source_path = source_paths[0]
    components = tuple(
        {"well": "A01", "site": 1, "channel": 1, "z_index": z, "timepoint": 1}
        for z in range(4)
    )
    table = MeasurementTable(
        name="centres",
        rows=MeasurementSparseColumnarRows.from_rows(
            (
                {
                    "object_label": 7,
                    "center_z": 2.375,
                    "center_y": 1.25,
                    "center_x": 3.5,
                    "response": 4.75,
                },
            ),
            fields=(
                FieldSpec("object_label", int),
                FieldSpec("center_z", float),
                FieldSpec("center_y", float),
                FieldSpec("center_x", float),
                FieldSpec("response", float),
            ),
        ),
        source_path=source_path,
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=source_paths,
            component_metadata=components,
        ),
        subject=MeasurementSubject(MeasurementScope.OBJECT, "nuclei", "object_label"),
    )
    features = ObjectCoreMeasurementFeature
    archive = materialize(
        MaterializationSpec(
            PointROIOptions(
                z_feature=features.CENTER_Z,
                y_feature=features.CENTER_Y,
                x_feature=features.CENTER_X,
            )
        ),
        data=table,
        path=str(tmp_path / "centres"),
        filemanager=FileManager({"disk": DiskStorageBackend()}),
        backends=["disk"],
        backend_kwargs={},
    )
    filemanager = FakeFileManager()
    handler = SimpleNamespace(
        metadata_handler=FakeMetadataHandler(),
        parser=SimpleNamespace(
            parse_filename=lambda _filename: pytest.fail(
                "Native point archive must not infer provenance from filenames"
            )
        ),
    )
    config = NapariStreamingConfig(enabled=True)
    result = StreamingService(filemanager, handler, tmp_path).stream_rois(
        RoiStreamingRequest(
            viewer=FakeViewer(),
            config=config,
            status_callback=lambda _status: None,
            error_callback=lambda error: pytest.fail(error),
            roi_filenames=(archive,),
            require_source_metadata=True,
        )
    )
    assert result.streamed_paths == (archive,)
    assert len(filemanager.saved_batches) == 1
    data, paths, _backend, kwargs = filemanager.saved_batches[0]
    stream = kwargs[ViewerStreamKwarg.STREAM_REQUEST.value]
    assert paths == [archive]
    assert data[0][0].metadata["response"] == 4.75
    assert data[0][0].metadata["openhcs_fractional_z"] == 2.375
    reopened_source = ROIArchiveSourceMetadata.decode(data[0])
    assert reopened_source is not None
    assert reopened_source.source_provenance == table.source_provenance
    assert stream.source.metadata.metadata_by_path[archive]["z_index"] == 0
    assert stream.message_extra[ViewerBatchWireField.COMPONENT_VALUE_DOMAIN.value][
        "z_index"
    ] == [0, 1, 2, 3]
    domain = ViewerComponentValueDomainPayload.from_wire_mapping(
        stream.message_extra[ViewerBatchWireField.COMPONENT_VALUE_DOMAIN.value],
        context="native point archive",
    )
    semantics = ViewerComponentAxisSemantics(
        entries=domain.entries,
        layout=ViewerObjectDisplayConfigInput(config).layout(),
    )
    item = SimpleNamespace(
        address=SimpleNamespace(
            components=stream.source.metadata.metadata_by_path[archive]
        ),
        data=NapariROIConverter.rois_to_shapes(data[0]),
    )
    request = ViewerLayerAxisProjectionRequestAuthority.from_component_axis_semantics(
        route_key="centres",
        component_axis_semantics=semantics,
        layer_items=[item],
        route_value_tracker=ViewerRouteComponentValueTracker(),
        aggregate_component_values={},
        geometric_component_values={},
    )
    projection = ViewerLayerAxisProjector().project(request)
    assert "z_index" in projection.projected_axis_components
    from openhcs.runtime.napari_viewer_server import _build_nd_points

    points, properties = _build_nd_points([item], projection)
    assert points[0, projection.projected_axis_components.index("z_index")] == 2.375
    assert properties["response"] == [4.75]


def test_explicit_native_reopening_rejects_an_external_roi_without_source(tmp_path):
    from polystore.disk import DiskStorageBackend

    path = tmp_path / "A01_s001_w1_z001_t001.roi.zip"
    DiskStorageBackend().save([ROI([PointShape(1, 2)], {"label": 1})], path)
    filemanager = FakeFileManager()
    with pytest.raises(ValueError, match="Native ROI source metadata is required"):
        StreamingService(filemanager, SimpleNamespace(), tmp_path).stream_rois(
            RoiStreamingRequest(
                viewer=FakeViewer(),
                config=NapariStreamingConfig(enabled=True),
                status_callback=lambda _status: None,
                error_callback=lambda error: pytest.fail(error),
                roi_filenames=(str(path),),
                require_source_metadata=True,
            )
        )
    assert filemanager.saved_batches == []


def test_stream_rois_preserves_per_artifact_producer_identities(monkeypatch) -> None:
    monkeypatch.setattr(
        "polystore.roi.load_rois_from_zip",
        lambda _path: [ROI(shapes=[PointShape(1, 2)])],
    )
    filemanager = FakeFileManager()
    config = FijiStreamingConfig(enabled=True)
    roi_paths = (
        "/output/results/A01_bodies.roi.zip",
        "/output/results/A01_neurites.roi.zip",
    )
    service = StreamingService(
        filemanager=filemanager,
        microscope_handler=SimpleNamespace(metadata_handler=FakeMetadataHandler()),
        plate_path=Path("/plate"),
    )
    producer_identities = tuple(
        StreamProducerIdentity.fixed_output(
            FixedStreamProducerIdentityKind.MANUAL,
            artifact_key,
        )
        for artifact_key in ("A01_bodies", "A01_neurites")
    )

    service.stream_rois(
        RoiStreamingRequest(
            viewer=FakeViewer(),
            config=config,
            status_callback=lambda _status: None,
            error_callback=lambda error: (_ for _ in ()).throw(AssertionError(error)),
            roi_filenames=roi_paths,
            component_metadata_by_path={
                path: {
                    "well": "A01",
                    "site": 1,
                    "channel": 2,
                    "z_index": 1,
                    "timepoint": 1,
                }
                for path in roi_paths
            },
            producer=ViewerStreamProducer.from_identities(producer_identities),
        )
    )

    _data, _paths, _backend, metadata = filemanager.saved_batches[0]
    stream_request = metadata[ViewerStreamKwarg.STREAM_REQUEST.value]
    assert stream_request.producer.identities == producer_identities


def test_stream_rois_keeps_producer_identity_aligned_when_archive_is_empty(
    monkeypatch,
) -> None:
    roi_paths = (
        "/output/results/A01_empty.roi.zip",
        "/output/results/A01_bodies.roi.zip",
    )
    monkeypatch.setattr(
        "polystore.roi.load_rois_from_zip",
        lambda path: (
            []
            if str(path).endswith("A01_empty.roi.zip")
            else [ROI(shapes=[PointShape(1, 2)])]
        ),
    )
    filemanager = FakeFileManager()
    producer_identities = tuple(
        StreamProducerIdentity.fixed_output(
            FixedStreamProducerIdentityKind.MANUAL,
            artifact_key,
        )
        for artifact_key in ("A01_empty", "A01_bodies")
    )
    service = StreamingService(
        filemanager=filemanager,
        microscope_handler=SimpleNamespace(metadata_handler=FakeMetadataHandler()),
        plate_path=Path("/plate"),
    )

    service.stream_rois(
        RoiStreamingRequest(
            viewer=FakeViewer(),
            config=FijiStreamingConfig(enabled=True),
            status_callback=lambda _status: None,
            error_callback=lambda error: (_ for _ in ()).throw(AssertionError(error)),
            roi_filenames=roi_paths,
            component_metadata_by_path={
                path: {
                    "well": "A01",
                    "site": 1,
                    "channel": 2,
                    "z_index": 1,
                    "timepoint": 1,
                }
                for path in roi_paths
            },
            producer=ViewerStreamProducer.from_identities(producer_identities),
        )
    )

    _data, paths, _backend, metadata = filemanager.saved_batches[0]
    stream_request = metadata[ViewerStreamKwarg.STREAM_REQUEST.value]
    assert paths == [roi_paths[1]]
    assert stream_request.producer.identities == (producer_identities[1],)


def test_stream_rois_rejects_unresolved_source_plane_metadata() -> None:
    service = StreamingService(
        filemanager=FakeFileManager(),
        microscope_handler=SimpleNamespace(
            parser=SimpleNamespace(parse_filename=lambda _filename: None)
        ),
        plate_path=Path("/plate"),
    )

    with pytest.raises(ValueError, match="Could not resolve source-plane metadata"):
        service.source.roi_component_metadata_by_path(
            ["nuclei1_out_c00_dr90_image_Watershed_step3_rois.roi.zip"],
        )


@pytest.fixture
def lifecycle_manager(monkeypatch):
    # Exercise the real manager/acquisition path without starting or stopping
    # any real viewer, endpoint, Qt application or foreign process.
    monkeypatch.setattr(ViewerStateManager, "_instance", None)
    monkeypatch.setattr(
        ManagedViewerLifecycleMixin, "is_running", property(lambda self: True)
    )
    monkeypatch.setattr(
        ManagedViewerLifecycleMixin, "wait_for_ready", lambda self, timeout: True
    )
    monkeypatch.setattr(
        ManagedViewerLifecycleMixin, "force_stop",
        lambda self: self.lifecycle_state.mark_stopped(),
    )
    monkeypatch.setattr(
        ManagedViewerLifecycleMixin, "start",
        lambda self: (_ for _ in ()).throw(AssertionError("must not restart")),
    )
    manager = ViewerStateManager.get_instance()
    yield manager
    manager.stop_all_viewers()


def test_streaming_viewer_lifecycle_attaches_existing_viewer_without_restart(
    monkeypatch, lifecycle_manager,
) -> None:
    monkeypatch.setattr(
        NapariStreamVisualizer,
        "existing_viewer_is_ready",
        lambda self: True,
    )

    viewer = StreamingViewerLifecycle.get_or_create_visualizer(
        filemanager=FakeFileManager(),
        config=NapariStreamingConfig(enabled=True, port=5563, persistent=True),
        fresh=False,
        launch_context=ViewerLaunchContext.headless(),
    )

    assert isinstance(viewer, NapariStreamVisualizer)
    assert viewer.lifecycle_state.is_connected_external


@pytest.mark.parametrize(
    ("config", "visualizer_type"),
    (
        (
            NapariStreamingConfig(enabled=True, port=5563, persistent=True),
            NapariStreamVisualizer,
        ),
        (
            FijiStreamingConfig(enabled=True, port=5564, persistent=True),
            FijiStreamVisualizer,
        ),
    ),
)
def test_streaming_viewer_lifecycle_projects_launch_context_for_every_viewer(
    monkeypatch,
    lifecycle_manager,
    config,
    visualizer_type,
) -> None:
    monkeypatch.setattr(
        visualizer_type,
        "existing_viewer_is_ready",
        lambda self: True,
    )
    launch_context = ViewerLaunchContext.projected_graphical_session(
        {
            "DISPLAY": ":31",
            "XAUTHORITY": "/run/user/1000/xauth",
            "XDG_RUNTIME_DIR": "/run/user/1000",
        }
    )

    viewer = StreamingViewerLifecycle.get_or_create_visualizer(
        filemanager=FakeFileManager(),
        config=config,
        fresh=False,
        launch_context=launch_context,
    )

    assert isinstance(viewer, visualizer_type)
    assert viewer.detached_launch_request().launch_context is launch_context


def test_streaming_viewer_lifecycle_reports_bounded_launch_log(
    monkeypatch,
    tmp_path: Path,
) -> None:
    class FakeManager:
        def release_viewer(
            self, viewer_type: str, port: int, *, stop: bool, force: bool
        ):
            del viewer_type, port, stop, force

    def fail_after_factory(*, factory, **_kwargs):
        viewer = factory()
        log_file = viewer.detached_launch_request().log_file
        log_file.parent.mkdir(parents=True, exist_ok=True)
        log_file.write_text(
            "\n".join(f"startup-{index:03d}" for index in range(100)),
            encoding="utf-8",
        )
        raise RuntimeError("napari process terminated unexpectedly during startup")

    monkeypatch.setattr(
        "zmqruntime.ViewerStateManager.get_instance",
        lambda: FakeManager(),
    )
    monkeypatch.setattr("zmqruntime.get_or_create_viewer", fail_after_factory)
    monkeypatch.setattr(
        DetachedViewerServerEntrypointSpec,
        "log_file_for",
        lambda self, port: tmp_path / f"{self.viewer_type.wire_value}_{port}.log",
    )

    with pytest.raises(DetachedViewerLaunchFailure) as error:
        StreamingViewerLifecycle.get_or_create_visualizer(
            filemanager=FakeFileManager(),
            config=NapariStreamingConfig(enabled=True, port=5563, persistent=True),
        )

    assert error.value.log_file == tmp_path / "napari_5563.log"
    assert error.value.log_tail.endswith("startup-099")
    assert "startup-000" not in error.value.log_tail
    assert str(error.value.log_file) in str(error.value)


@pytest.mark.parametrize("config_type", (NapariStreamingConfig, FijiStreamingConfig))
@pytest.mark.parametrize(
    ("owns_process", "requested_host", "reusable"),
    ((True, "127.0.0.1", False), (True, "*", True), (False, "127.0.0.1", True)),
)
def test_streaming_viewer_lifecycle_admits_new_launch_inside_managed_acquisition(
    monkeypatch, lifecycle_manager, config_type, owns_process, requested_host, reusable
) -> None:
    active_config = config_type(enabled=True, port=5563, persistent=True, listen_host="*")
    existing_viewer = active_config.create_visualizer(FakeFileManager())
    existing_viewer.lifecycle_state.mark_connected_external()
    monkeypatch.setattr(
        ManagedViewerLifecycleMixin, "owned_viewer_process_is_alive",
        lambda self: owns_process,
    )
    monkeypatch.setattr(
        ViewerControlMessageRequest, "send",
        lambda self: ViewerControlResponse({
            "status": "success",
            "process_launch": active_config.viewer_process_launch_config().to_wire_mapping(),
        }),
    )
    lifecycle_manager.get_or_create_viewer(
        active_config.viewer_type.wire_value, 5563, lambda: existing_viewer
    )
    monkeypatch.setattr(
        config_type,
        "create_visualizer",
        lambda *args, **kwargs: (_ for _ in ()).throw(
            AssertionError("managed reuse must not construct another viewer")
        ),
    )

    requested = config_type(
        enabled=True, port=5563, persistent=True, listen_host=requested_host
    )
    if reusable:
        assert StreamingViewerLifecycle.get_or_create_visualizer(
            filemanager=FakeFileManager(), config=requested, fresh=False,
        ) is existing_viewer
    else:
        with pytest.raises(RuntimeError, match="does not match the requested process launch"):
            StreamingViewerLifecycle.get_or_create_visualizer(
                filemanager=FakeFileManager(), config=requested, fresh=False,
            )
    assert lifecycle_manager.get_viewer(
        active_config.viewer_type.wire_value, 5563
    ) is existing_viewer
