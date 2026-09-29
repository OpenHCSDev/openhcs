"""Persisted source declaration -> inventory -> ordinary viewer loading, no GUI."""

from pathlib import Path

import numpy as np
import pytest

from openhcs.agent.dto.plate import PlatePathInspectionRequest
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.plate_inspection_service import PlateInspectionService
from openhcs.agent.services.plate_streaming_service import PlateStreamingService
from openhcs.core.plate_image_inventory import PlateFileKind
from openhcs.core.runtime_image_values import image_payload_data, image_payload_metadata
from openhcs.core.source_workspace_projection import VirtualWorkspacePathLookup
from openhcs.core.viewer_streaming_service import (
    FullWindowImageStreamingRequest,
    ImageStreamingRequest,
    ViewerStreamingSource,
)
from tests.diagnostics.check_viewer_feature_measurement_live import make_fixture


def test_inventory_stream_preserves_original_nominal_crop_and_spacing(tmp_path: Path):
    paths = make_fixture(tmp_path / "plate")
    inspection = PlateInspectionService(
        AgentPathPolicy.with_roots(
            readable_roots=(tmp_path,), writable_roots=(tmp_path,)
        )
    )
    context, errors, _warnings = inspection.open_context(
        PlatePathInspectionRequest(plate_path=str(paths[0].parent))
    )
    assert errors == () and context is not None
    inventory, _warnings = inspection.file_inventory(context, kind=PlateFileKind.IMAGE)
    records = inventory.file_records(kinds=(PlateFileKind.IMAGE,))
    assert len(records) == 2
    projection = PlateStreamingService._inventory_source_projection(records, context)
    source = ViewerStreamingSource(
        filemanager=context.filemanager,
        microscope_handler=context.handler,
        plate_path=str(paths[0].parent),
    )
    for image_record, record in zip(inventory.image_records, records, strict=True):
        lookup = VirtualWorkspacePathLookup.from_paths(
            record.virtual_path, record.full_virtual_path
        )
        assert record.source_projection is image_record.source_projection
        assert projection.source_projection_for(lookup) is record.source_projection
        payload = source.load_image(
            record.streamable_image_path,
            record.source_ref.backend,
            source_projection=projection,
            component_metadata=record.metadata,
        )
        metadata = image_payload_metadata(payload)
        assert metadata.source_spatial_domain.origin_yx == (7, 11)
        assert metadata.source_spatial_domain.source_shape_yx == (80, 100)
        assert metadata.source_voxel_spacing.values_zyx == (2, 3)
        request_fields = dict(
            viewer=None,
            config=None,
            status_callback=lambda _: None,
            error_callback=lambda _: None,
            filenames=(record.streamable_image_path,),
            read_backend=record.source_ref.backend,
            source_projection=projection,
        )
        ImageStreamingRequest(**request_fields).require_image_window(
            source, record.streamable_image_path, payload, projection
        )
        with pytest.raises(ValueError, match="window conflicts"):
            FullWindowImageStreamingRequest(**request_fields).require_image_window(
                source, record.streamable_image_path, payload, projection
            )
        if record.metadata["channel"] == 1:
            np.testing.assert_array_equal(
                image_payload_data(payload),
                (10 * np.arange(64)[:, None] + np.arange(64)[None, :]).astype(
                    np.uint16
                ),
            )
