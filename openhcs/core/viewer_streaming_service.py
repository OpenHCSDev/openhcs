"""Public viewer streaming service for plate images and ROI artifacts.

Eliminates duplication between Napari and Fiji streaming code by parametrizing
on viewer_type. Callers provide UI or agent callbacks; all heavy operations run
in background threads.
"""

from __future__ import annotations

import logging
import re
import time
from collections.abc import Callable, Mapping
from dataclasses import dataclass, field, replace
from hashlib import sha256
from json import dumps
from pathlib import Path
from typing import TYPE_CHECKING, ClassVar

from objectstate import spawn_thread_with_context
from polystore.streaming.identity import (
    FixedStreamProducerIdentityKind,
    StreamProducerIdentity,
)
from polystore.streaming.viewer_transport import (
    ViewerStreamProducer,
    ViewerStreamSourceIdentity,
)
from zmqruntime.config import ZMQConfig
from zmqruntime.viewer_protocol import ViewerWireMapping

from openhcs.core.runtime_image_loading import ImagePayloadSourceMetadataContext
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_payload_data,
    image_payload_mask,
    image_payload_metadata,
)
from openhcs.core.source_image_provenance import SourceImageIdentity
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_workspace_projection import (
    VirtualWorkspacePathLookup,
    VirtualWorkspaceSourceProjection,
    VirtualWorkspaceSourceProjectionAuthority,
)
from openhcs.core.steps.stream_component_semantics import (
    StreamComponentMessageExtraAuthority,
    StreamImagePayloadMetadataProjector,
    StreamSourceComponentMetadataItems,
)
from openhcs.core.streaming_config_declarations import ViewerType
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG

if TYPE_CHECKING:
    from polystore.filemanager import FileManager

    from openhcs.core.config import StreamingConfig
    from openhcs.microscopes.microscope_base import MicroscopeHandler
    from openhcs.runtime.viewer_protocol import (
        ManagedViewerLifecycleMixin,
        ViewerLaunchContext,
    )

logger = logging.getLogger(__name__)

# Chunk size to prevent file descriptor exhaustion
# Each image creates a shared memory segment (file descriptor on Linux)
CHUNK_SIZE = 50
ROI_ARCHIVE_SUFFIX = ".roi.zip"
SOURCE_FILENAME_EXTENSIONS = (".tif", ".tiff", ".png", ".jpg", ".jpeg")


@dataclass(frozen=True, slots=True)
class ViewerStreamingContext:
    """Shared viewer/request context for asynchronous streaming operations."""

    viewer: ManagedViewerLifecycleMixin
    config: StreamingConfig
    status_callback: Callable[[str], None]
    error_callback: Callable[[str], None]


@dataclass(frozen=True, slots=True)
class ImageStreamingRequest(ViewerStreamingContext):
    """Request to stream image files to one viewer."""

    filenames: tuple[str, ...]
    read_backend: str
    source_projection: VirtualWorkspaceSourceProjection | None = None
    producer: ViewerStreamProducer | None = None


@dataclass(frozen=True, slots=True)
class ManualImageStreamProjectionIdentity:
    """Exact route identity for one manually selected source-image set."""

    plate_path: str
    filenames: tuple[str, ...]

    OUTPUT_KEY: ClassVar[str] = "selected_images"

    def producer_identity(self) -> StreamProducerIdentity:
        """Return the producer identity for this exact selection."""

        canonical_selection = dumps(
            {
                "plate_path": self.plate_path,
                "filenames": sorted(self.filenames),
            },
            sort_keys=True,
            separators=(",", ":"),
        )
        projection_digest = sha256(canonical_selection.encode("utf-8")).hexdigest()
        return replace(
            StreamProducerIdentity.fixed_output(
                FixedStreamProducerIdentityKind.MANUAL,
                self.OUTPUT_KEY,
            ),
            projection_key=f"{self.OUTPUT_KEY}_{projection_digest}",
        )


@dataclass(frozen=True, slots=True)
class RoiStreamingRequest(ViewerStreamingContext):
    """Request to stream ROI files to one viewer."""

    roi_filenames: tuple[str, ...]
    component_metadata_by_path: Mapping[str, ViewerWireMapping] = field(
        default_factory=dict
    )
    producer: ViewerStreamProducer | None = None


@dataclass(frozen=True, slots=True)
class ViewerStreamingResult:
    """Synchronous result for one manual viewer streaming request."""

    viewer_type: ViewerType
    port: int
    display_name: str
    payload_kind: str
    requested_count: int
    streamed_count: int
    streamed_paths: tuple[str, ...]
    messages: tuple[str, ...] = ()


class StreamingViewerLifecycle:
    """Shared lifecycle entrypoint for manual and orchestrated viewer streaming."""

    @staticmethod
    def get_or_create_visualizer(
        *,
        filemanager: FileManager,
        config: StreamingConfig,
        visualizer_config=None,
        transport_config: ZMQConfig = OPENHCS_ZMQ_CONFIG,
        fresh: bool = True,
        ready_timeout: float = 30.0,
        launch_context: ViewerLaunchContext | None = None,
    ) -> ManagedViewerLifecycleMixin:
        from zmqruntime import ViewerStateManager, get_or_create_viewer
        from zmqruntime.queue_tracker import GlobalQueueTrackerRegistry

        from openhcs.runtime.viewer_protocol import (
            ViewerGraphicalSessionUnavailableError,
            ViewerLaunchContext,
        )

        resolved_launch_context = (
            launch_context or ViewerLaunchContext.inherited_graphical_session()
        )
        registry = GlobalQueueTrackerRegistry()
        registry.get_or_create_tracker(config.port, config.viewer_type.wire_value)
        manager = ViewerStateManager.get_instance()

        if fresh:
            manager.release_viewer(
                config.viewer_type.wire_value,
                config.port,
                stop=True,
                force=True,
            )
        else:
            managed_viewer = manager.get_viewer(
                config.viewer_type.wire_value,
                config.port,
            )
            if managed_viewer is not None:
                return managed_viewer

            external_viewer = StreamingViewerLifecycle._create_managed_visualizer(
                filemanager=filemanager,
                config=config,
                visualizer_config=visualizer_config,
                transport_config=transport_config,
                launch_context=resolved_launch_context,
            )
            if external_viewer.existing_viewer_is_ready():
                external_viewer.lifecycle_state.mark_connected_external()
                return external_viewer

        created_viewer: ManagedViewerLifecycleMixin | None = None

        def create_viewer() -> ManagedViewerLifecycleMixin:
            nonlocal created_viewer
            created_viewer = StreamingViewerLifecycle._create_managed_visualizer(
                filemanager=filemanager,
                config=config,
                visualizer_config=visualizer_config,
                transport_config=transport_config,
                launch_context=resolved_launch_context,
            )
            return created_viewer

        try:
            viewer, _created = get_or_create_viewer(
                viewer_type=config.viewer_type.wire_value,
                port=config.port,
                factory=create_viewer,
                wait_for_ready=True,
                ready_timeout=ready_timeout,
            )
        except ViewerGraphicalSessionUnavailableError:
            raise
        except Exception as exc:
            if created_viewer is not None:
                raise created_viewer.detached_launch_request().failure(exc) from exc
            raise
        return viewer

    @staticmethod
    def _create_managed_visualizer(
        *,
        filemanager: FileManager,
        config: StreamingConfig,
        visualizer_config,
        transport_config: ZMQConfig,
        launch_context: ViewerLaunchContext,
    ) -> ManagedViewerLifecycleMixin:
        from openhcs.runtime.viewer_protocol import ManagedViewerLifecycleMixin

        viewer = config.create_visualizer(
            filemanager,
            visualizer_config,
            transport_config,
        )
        if not isinstance(viewer, ManagedViewerLifecycleMixin):
            raise TypeError(
                "Streaming viewer config produced an unsupported viewer "
                f"lifecycle type: {type(viewer).__name__}"
            )
        viewer.configure_launch_context(launch_context)
        return viewer


class StreamingSourceFilenameAuthority:
    """Resolve source-image filename candidates for streamed viewer artifacts."""

    @staticmethod
    def roi_artifact_stem(filename: str) -> str:
        name = Path(filename).name
        if name.lower().endswith(ROI_ARCHIVE_SUFFIX):
            return name[: -len(ROI_ARCHIVE_SUFFIX)]
        return Path(name).stem

    @classmethod
    def source_filename_candidates_for_roi(cls, filename: str) -> tuple[str, ...]:
        """Return plausible source-image names for an analysis ROI artifact."""
        candidates: list[str] = []

        def add(value: str) -> None:
            if value and value not in candidates:
                candidates.append(value)

        name = Path(filename).name
        stem = cls.roi_artifact_stem(name)
        add(name)
        add(stem)

        bases = [stem]
        for pattern in (
            r"^(?P<base>.+)_step\d+_rois$",
            r"^(?P<base>.+)_step\d+$",
            r"^(?P<base>.+)_rois$",
        ):
            match = re.match(pattern, stem)
            if match:
                bases.append(match.group("base"))

        parts = stem.split("_")
        for end in range(len(parts) - 1, 0, -1):
            bases.append("_".join(parts[:end]))

        for base in bases:
            add(base)
            if not Path(base).suffix:
                for extension in SOURCE_FILENAME_EXTENSIONS:
                    add(f"{base}{extension}")

        return tuple(candidates)

    @staticmethod
    def source_filename_candidates_for_image(filename: str) -> tuple[str, ...]:
        name = Path(filename).name
        if filename == name:
            return (name,)
        return (filename, name)


@dataclass(frozen=True, slots=True, kw_only=True)
class ViewerStreamingSource(ViewerStreamSourceIdentity):
    """Source authority for viewer streaming from one initialized plate."""

    filemanager: FileManager
    microscope_handler: MicroscopeHandler

    def source_workspace_projection(self) -> VirtualWorkspaceSourceProjection:
        return VirtualWorkspaceSourceProjectionAuthority.from_plate_metadata(
            plate_path=Path(self.plate_path),
            metadata_handler=self.microscope_handler.metadata_handler,
            filemanager=self.filemanager,
        ).projection_or_empty()

    def roi_image_metadata(self) -> ImagePayloadMetadata:
        """Return plate-owned physical calibration for ROI pixel coordinates."""
        pixel_size = float(
            self.microscope_handler.metadata_handler.get_pixel_size(self.plate_path)
        )
        return ImagePayloadMetadata(
            source_voxel_spacing=SourceVoxelSpacing((pixel_size, pixel_size))
        )

    def load_image(
        self,
        filename: str,
        read_backend: str,
        *,
        source_projection: VirtualWorkspaceSourceProjection,
        component_metadata: ViewerWireMapping,
    ):
        lookup = VirtualWorkspacePathLookup.from_paths(
            filename, str(Path(self.plate_path) / filename)
        )
        source_ref = source_projection.source_ref_for(lookup)
        backend = read_backend if source_ref is None else source_ref.backend
        source_path = source_projection.resolved_source_path_for(
            lookup, self.filemanager
        )
        image = self.filemanager.load(source_path, backend)
        image = source_projection.project_unbound_payload(lookup, image)
        metadata = ImagePayloadSourceMetadataContext(
            source_identity=SourceImageIdentity(
                lookup.full_virtual_path,
                source_projection.source_metadata_for(lookup) or component_metadata,
            ),
            read_backend=backend,
            filemanager=self.filemanager,
            source_address=source_path,
        ).metadata(image)
        return metadata.payload_with(
            image_payload_data(image), image_payload_mask(image)
        )

    def component_metadata_by_path(
        self,
        paths: list[str],
        candidate_names_for_path: Callable[[str], tuple[str, ...]],
        artifact_label: str,
    ) -> dict[str, ViewerWireMapping]:
        parser = self.microscope_handler.parser
        metadata_by_path: dict[str, ViewerWireMapping] = {}

        for path in paths:
            parsed = None
            for candidate in candidate_names_for_path(path):
                parsed = parser.parse_filename(candidate)
                if parsed is not None:
                    break

            if parsed is None:
                raise ValueError(
                    "Could not resolve source-plane metadata for "
                    f"{artifact_label} {path!r}; streaming requires explicit "
                    "component metadata."
                )
            metadata_by_path[path] = dict(parsed.component_wire_mapping())

        return metadata_by_path

    def image_component_metadata_by_path(
        self,
        paths: list[str],
        source_projection: VirtualWorkspaceSourceProjection | None = None,
    ) -> dict[str, ViewerWireMapping]:
        if source_projection is None:
            return self.component_metadata_by_path(
                paths,
                StreamingSourceFilenameAuthority.source_filename_candidates_for_image,
                "image",
            )
        metadata_by_path = {
            path: metadata
            for path in paths
            if (
                metadata := source_projection.source_metadata_for(
                    VirtualWorkspacePathLookup.from_paths(
                        path, str(Path(self.plate_path) / path)
                    )
                )
            )
            is not None
        }
        metadata_by_path.update(
            self.component_metadata_by_path(
                [path for path in paths if path not in metadata_by_path],
                StreamingSourceFilenameAuthority.source_filename_candidates_for_image,
                "image",
            )
        )
        return metadata_by_path

    def require_projected_image_window(
        self, filename: str, image, source_projection: VirtualWorkspaceSourceProjection
    ) -> None:
        """Validate a request-authored full-window binding against loaded pixels."""
        projection = source_projection.source_projection_for(
            VirtualWorkspacePathLookup.from_paths(
                filename, str(Path(self.plate_path) / filename)
            )
        )
        if projection is None or projection.image_metadata is None:
            raise ValueError(
                "Explicit image projection requires a metadata-bearing source."
            )
        metadata = projection.image_metadata
        shape = tuple(image_payload_data(image).shape)
        if (
            len(shape) != 3
            or metadata.plane_axis is None
            or shape[0] != metadata.source_plane_metadata_count
            or metadata.source_spatial_domain.origin_yx != (0, 0)
            or tuple(shape[-2:]) != metadata.source_spatial_domain.source_shape_yx
        ):
            raise ValueError(
                "Loaded image window conflicts with its explicit source binding."
            )

    def image_source_metadata_items(
        self,
        paths: tuple[str, ...],
        metadata_by_path: Mapping[str, ViewerWireMapping],
        source_projection: VirtualWorkspaceSourceProjection,
    ) -> StreamSourceComponentMetadataItems:
        """Include declared pixel-plane coordinates, never mere contributors."""
        values = []
        for path in paths:
            projection = source_projection.source_projection_for(
                VirtualWorkspacePathLookup.from_paths(
                    path, str(Path(self.plate_path) / path)
                )
            )
            metadata = None if projection is None else projection.image_metadata
            if metadata is not None and metadata.plane_axis is not None:
                values.extend(
                    metadata.source_image_provenance_planes.runtime_component_metadata
                )
            else:
                values.append(metadata_by_path[path])
        return StreamSourceComponentMetadataItems.from_values(values)

    def roi_component_metadata_by_path(
        self,
        paths: list[str],
    ) -> dict[str, ViewerWireMapping]:
        return self.component_metadata_by_path(
            paths,
            StreamingSourceFilenameAuthority.source_filename_candidates_for_roi,
            "ROI artifact",
        )


class StreamingService:
    """Unified service for streaming images/ROIs to viewers.

    Handles all viewer communication in background threads.
    Uses callbacks for caller-owned status updates and error handling.
    """

    def __init__(
        self,
        filemanager: FileManager,
        microscope_handler: MicroscopeHandler,
        plate_path: Path,
        transport_config: ZMQConfig = OPENHCS_ZMQ_CONFIG,
    ):
        self.source = ViewerStreamingSource(
            filemanager=filemanager,
            microscope_handler=microscope_handler,
            plate_path=plate_path,
        )
        self.transport_config = transport_config

    def _wait_for_viewer_ready(
        self,
        viewer: ManagedViewerLifecycleMixin,
        config: StreamingConfig,
        num_items: int,
    ) -> None:
        """Wait for viewer to be ready, registering as launching if needed."""
        # Use centralized ViewerStateManager for launching/queued state
        from zmqruntime.viewer_state import ViewerStateManager

        manager = ViewerStateManager.get_instance()

        is_already_running = viewer.runtime_endpoint.wait_ready(
            timeout=0.1,
            require_ready=True,
        )

        # Update queued images for UI display via manager. The QueueTracker
        # will later update counts precisely as images are sent/acked.
        manager.update_queued_images(
            config.viewer_type.wire_value,
            viewer.port,
            num_items,
        )

        if not is_already_running:
            logger.info(
                f"Waiting for {config.display_name} viewer on port {viewer.port} to become ready"
            )

            if not viewer.runtime_endpoint.wait_ready(
                timeout=15.0,
                require_ready=True,
            ):
                # Clear queued count for UI if startup failed
                manager.update_queued_images(
                    config.viewer_type.wire_value,
                    viewer.port,
                    0,
                )
                raise RuntimeError(
                    f"{config.display_name} viewer on port {viewer.port} failed to become ready"
                )

            logger.info(f"{config.display_name} viewer on port {viewer.port} is ready")

    @staticmethod
    def _require_viewer_settled(request: ViewerStreamingContext) -> None:
        """Require receiver-accepted payloads to finish viewer-native mounting."""

        if request.viewer.settle_viewer_state():
            return
        raise RuntimeError(
            "Failed to settle streamed updates for "
            f"{request.config.display_name} viewer on port {request.viewer.port}."
        )

    def stream_images_async(
        self,
        request: ImageStreamingRequest,
    ) -> None:
        """Load and stream images to viewer in background thread.

        Uses chunked streaming to prevent file descriptor exhaustion.
        """
        display_name = request.config.display_name

        def _worker():
            try:
                self.stream_images(request)
            except Exception as e:
                logger.error(f"Failed to stream images to {display_name}: {e}")
                request.status_callback(f"Error: {e}")
                request.error_callback(str(e))

        spawn_thread_with_context(
            _worker,
            name=f"stream_images_{request.config.viewer_type.wire_value}",
        )
        logger.info(
            f"Started streaming {len(request.filenames)} images to {display_name}"
        )

    def stream_images(
        self,
        request: ImageStreamingRequest,
    ) -> ViewerStreamingResult:
        """Load and stream images to a viewer before returning."""
        backend_enum = request.config.backend
        display_name = request.config.display_name
        messages: list[str] = []

        self._wait_for_viewer_ready(
            request.viewer,
            request.config,
            len(request.filenames),
        )

        total_images = len(request.filenames)
        num_chunks = (total_images + CHUNK_SIZE - 1) // CHUNK_SIZE
        logger.info(f"Streaming {total_images} images in {num_chunks} chunks")
        source_projection = (
            self.source.source_workspace_projection()
            if request.source_projection is None
            else request.source_projection
        )
        all_metadata_by_path = self.source.image_component_metadata_by_path(
            list(request.filenames), source_projection
        )
        viewer_surface = request.config.viewer_surface(
            self.source,
            self.transport_config,
        )
        source_metadata_items = self.source.image_source_metadata_items(
            request.filenames, all_metadata_by_path, source_projection
        )
        message_authority = StreamComponentMessageExtraAuthority.from_viewer_surface(
            viewer_surface,
            source_metadata_items=source_metadata_items,
        )
        producer = request.producer or ViewerStreamProducer.from_identity(
            ManualImageStreamProjectionIdentity(
                plate_path=str(self.source.plate_path),
                filenames=request.filenames,
            ).producer_identity()
        )

        for chunk_idx in range(num_chunks):
            start_idx = chunk_idx * CHUNK_SIZE
            end_idx = min(start_idx + CHUNK_SIZE, total_images)
            chunk_filenames = request.filenames[start_idx:end_idx]

            message = (
                f"Loading chunk {chunk_idx + 1}/{num_chunks} "
                f"({len(chunk_filenames)} images)..."
            )
            messages.append(message)
            request.status_callback(message)

            image_data_list = []
            file_paths = []
            for filename in chunk_filenames:
                image_data = self.source.load_image(
                    filename,
                    request.read_backend,
                    source_projection=source_projection,
                    component_metadata=all_metadata_by_path[filename],
                )
                if request.source_projection is not None:
                    self.source.require_projected_image_window(
                        filename, image_data, source_projection
                    )
                image_data_list.append(image_data)
                file_paths.append(filename)

            logger.info(
                f"Loaded chunk {chunk_idx + 1}/{num_chunks}: {len(image_data_list)} images"
            )

            component_order = message_authority.layout.component_order
            for indices in StreamImagePayloadMetadataProjector.partition_indices(
                (image_payload_metadata(image) for image in image_data_list),
                component_order,
            ):
                metadata = image_payload_metadata(image_data_list[indices[0]])
                item_fields = StreamImagePayloadMetadataProjector.item_fields(
                    metadata,
                    component_order,
                )
                partition_metadata_by_path = {
                    file_paths[index]: all_metadata_by_path[file_paths[index]]
                    for index in indices
                }
                producer_subset = producer.for_indices(
                    tuple(start_idx + index for index in indices), total_images
                )
                self.source.filemanager.save_batch(
                    [image_payload_data(image_data_list[index]) for index in indices],
                    [file_paths[index] for index in indices],
                    backend_enum.value,
                    **message_authority.viewer_backend_kwargs(
                        producer=producer_subset,
                        source_metadata=message_authority.path_mapped_source_metadata(
                            partition_metadata_by_path,
                            item_fields=item_fields,
                        ),
                    )
                    .with_item_fields(item_fields)
                    .to_kwargs(),
                )
            logger.info(
                f"Streamed chunk {chunk_idx + 1}/{num_chunks} to {display_name}"
            )

            if chunk_idx < num_chunks - 1:
                time.sleep(0.1)

        self._require_viewer_settled(request)
        message = f"Streamed {total_images} images to {display_name}"
        logger.info("Successfully %s", message.lower())
        messages.append(message)
        request.status_callback(message)
        return ViewerStreamingResult(
            viewer_type=request.config.viewer_type,
            port=request.viewer.port,
            display_name=display_name,
            payload_kind="image",
            requested_count=total_images,
            streamed_count=total_images,
            streamed_paths=tuple(request.filenames),
            messages=tuple(messages),
        )

    def stream_rois_async(
        self,
        request: RoiStreamingRequest,
    ) -> None:
        """Load and stream ROI files to viewer in background thread."""
        display_name = request.config.display_name

        def _worker():
            try:
                self.stream_rois(request)
            except Exception as e:
                logger.error(f"Failed to stream ROIs to {display_name}: {e}")
                request.status_callback(f"Error: {e}")
                request.error_callback(str(e))

        spawn_thread_with_context(
            _worker,
            name=f"stream_rois_{request.config.viewer_type.wire_value}",
        )

    def stream_rois(
        self,
        request: RoiStreamingRequest,
    ) -> ViewerStreamingResult:
        """Load and stream ROI files to a viewer before returning."""
        from polystore.roi import load_rois_from_zip

        backend_enum = request.config.backend
        display_name = request.config.display_name
        messages: list[str] = []

        total = len(request.roi_filenames)
        if total == 0:
            return ViewerStreamingResult(
                viewer_type=request.config.viewer_type,
                port=request.viewer.port,
                display_name=display_name,
                payload_kind="rois",
                requested_count=0,
                streamed_count=0,
                streamed_paths=(),
            )

        message = f"Loading {total} ROI file(s) from disk..."
        messages.append(message)
        request.status_callback(message)

        data_list: list = []
        paths: list[str] = []
        loaded_indices: list[int] = []

        for i, filename in enumerate(request.roi_filenames, 1):
            file_path = Path(self.source.plate_path) / filename
            rois = load_rois_from_zip(file_path)
            if not rois:
                logger.warning(f"No ROIs found in {file_path.name}")
                continue

            data_list.append(rois)
            paths.append(filename)
            loaded_indices.append(i - 1)

            if i % 5 == 0 or i == total:
                message = f"Loading ROIs: {i}/{total} file(s)..."
                messages.append(message)
                request.status_callback(message)

        if not data_list:
            message = "No ROIs loaded from any selected files."
            logger.warning(message)
            messages.append(message)
            request.status_callback(message)
            return ViewerStreamingResult(
                viewer_type=request.config.viewer_type,
                port=request.viewer.port,
                display_name=display_name,
                payload_kind="rois",
                requested_count=total,
                streamed_count=0,
                streamed_paths=(),
                messages=tuple(messages),
            )

        self._wait_for_viewer_ready(
            request.viewer,
            request.config,
            len(paths),
        )

        viewer_surface = request.config.viewer_surface(
            self.source,
            self.transport_config,
        )
        if request.component_metadata_by_path:
            missing_metadata = tuple(
                path for path in paths if path not in request.component_metadata_by_path
            )
            if missing_metadata:
                raise ValueError(
                    "ROI streaming received explicit component metadata, but "
                    f"metadata was missing for {missing_metadata!r}."
                )
            metadata_by_path = {
                path: dict(request.component_metadata_by_path[path]) for path in paths
            }
        else:
            metadata_by_path = self.source.roi_component_metadata_by_path(paths)
        source_metadata_items = StreamSourceComponentMetadataItems.from_values(
            metadata_by_path[path] for path in paths
        )
        message_authority = StreamComponentMessageExtraAuthority.from_viewer_surface(
            viewer_surface,
            source_metadata_items=source_metadata_items,
        )
        producer = request.producer or ViewerStreamProducer.from_identity(
            StreamProducerIdentity.fixed_output(
                FixedStreamProducerIdentityKind.MANUAL,
                "selected_rois",
            )
        )
        stream_backend_kwargs = message_authority.viewer_backend_kwargs(
            producer=producer.for_indices(
                loaded_indices,
                total,
            ),
            source_metadata=message_authority.path_mapped_source_metadata(
                metadata_by_path
            ),
        ).with_item_fields(
            StreamImagePayloadMetadataProjector.item_fields(
                self.source.roi_image_metadata(),
                message_authority.layout.component_order,
            )
        )

        message = f"Streaming {len(paths)} ROI file(s) to {display_name}..."
        messages.append(message)
        request.status_callback(message)

        self.source.filemanager.save_batch(
            data_list,
            paths,
            backend_enum.value,
            **stream_backend_kwargs.to_kwargs(),
        )

        self._require_viewer_settled(request)
        message = (
            f"Streamed {len(paths)} ROI file(s) to {display_name} "
            f"on port {request.viewer.port}"
        )
        logger.info(message)
        messages.append(message)
        request.status_callback(message)
        return ViewerStreamingResult(
            viewer_type=request.config.viewer_type,
            port=request.viewer.port,
            display_name=display_name,
            payload_kind="rois",
            requested_count=total,
            streamed_count=len(paths),
            streamed_paths=tuple(paths),
            messages=tuple(messages),
        )
