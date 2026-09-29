from dataclasses import replace
from pathlib import Path

import numpy as np
import pytest
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
from polystore.roi import ROI, PointShape, load_rois_from_zip

from openhcs.core.roi_source_metadata import ROIArchiveSourceMetadata
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_object_labels import (
    ObjectLabelPayload,
    ObjectLabelVariantData,
)
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.processing.materialization import (
    MaterializationSpec,
    ROIOptions,
    materialize,
)


@pytest.mark.parametrize("spacing", [(0.65, 0.65), (2.0, 0.65, 0.65)])
def test_native_roi_disk_roundtrip_preserves_the_source_owner(tmp_path, spacing):
    metadata = ImagePayloadMetadata(
        source_path="/source/actual-image.tif",
        source_component_metadata={"well": "B02", "channel": 3, "z_index": 7},
        source_spatial_domain=SourceSpatialDomain(
            origin_yx=(10, 20), source_shape_yx=(100, 200)
        ),
        source_voxel_spacing=SourceVoxelSpacing(spacing),
    )
    rois = [ROI([PointShape(32.25, 40.5)], {"label": 12, "plane_indices": (2,)})]
    bound = ROIArchiveSourceMetadata.bind(rois, metadata)
    path = tmp_path / "misleading_A01_w2.roi.zip"
    DiskStorageBackend().save(bound, path)
    restored = load_rois_from_zip(path)
    decoded = ROIArchiveSourceMetadata.decode(restored)
    assert decoded.source_provenance == metadata.source_provenance
    assert decoded.source_voxel_spacing == metadata.source_voxel_spacing
    assert decoded.source_spatial_domain == metadata.source_spatial_domain
    assert ROIArchiveSourceMetadata.geometry(restored) == rois
    assert rois[0].metadata == {"label": 12, "plane_indices": (2,)}


def test_source_metadata_is_optional_only_for_external_shapes():
    roi = ROI([PointShape(1, 2)], {"label": 1})
    assert ROIArchiveSourceMetadata.decode([roi]) is None
    bound = ROIArchiveSourceMetadata.bind(
        [roi], ImagePayloadMetadata(source_path="one")
    )
    with pytest.raises(ValueError, match="missing or conflicting"):
        ROIArchiveSourceMetadata.decode([*bound, roi])
    conflict = ROIArchiveSourceMetadata.bind(
        [roi], ImagePayloadMetadata(source_path="two")
    )
    with pytest.raises(ValueError, match="missing or conflicting"):
        ROIArchiveSourceMetadata.decode([*bound, *conflict])
    malformed = replace(roi, metadata={ROIArchiveSourceMetadata.FIELD: {"unknown": 1}})
    with pytest.raises((TypeError, ValueError)):
        ROIArchiveSourceMetadata.decode([malformed])


def test_real_roi_materialization_persists_output_source_metadata(tmp_path):
    labels = np.zeros((8, 8), dtype=np.int32)
    labels[2:6, 3:7] = 12
    payload = ObjectLabelPayload(
        variant_data=ObjectLabelVariantData(labels=labels),
        source_path="/source/actual-image.tif",
        source_component_metadata={
            "well": "B02",
            "site": 1,
            "channel": 3,
            "z_index": 7,
            "timepoint": 1,
        },
        source_spatial_domain=SourceSpatialDomain(
            origin_yx=(10, 20), source_shape_yx=(100, 200)
        ),
        parent_image_source_voxel_spacing=SourceVoxelSpacing((0.65, 0.65)),
    )
    path = materialize(
        MaterializationSpec(ROIOptions(min_area=0)),
        data=payload,
        path=str(tmp_path / "labels.roi.zip"),
        filemanager=FileManager({"disk": DiskStorageBackend()}),
        backends=["disk"],
        backend_kwargs={},
    )
    rois = load_rois_from_zip(Path(path))
    metadata = ROIArchiveSourceMetadata.decode(rois)
    assert metadata.source_path == payload.source_path
    assert metadata.source_component_metadata == payload.source_component_metadata
    assert metadata.source_voxel_spacing == payload.parent_image_source_voxel_spacing
    assert metadata.source_spatial_domain.origin_yx == (10, 20)
    assert metadata.source_spatial_domain.source_shape_yx == (100, 200)
    assert rois[0].metadata["label"] == 12
    assert rois[0].metadata["centroid"] == (13.5, 24.5)
