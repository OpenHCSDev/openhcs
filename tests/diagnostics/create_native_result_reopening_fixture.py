"""Create native transport fixtures, never detections, beside a synthetic plate."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
from polystore.roi import ROI, PointShape, load_rois_from_zip

from openhcs.core.roi_source_metadata import ROIArchiveSourceMetadata
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_object_label_building import (
    SourceImageObjectLabelBuildRequest,
)
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.processing.materialization import (
    MaterializationSpec,
    ROIOptions,
    materialize,
)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("plate_path", type=Path)
    args = parser.parse_args()
    source = args.plate_path / "TimePoint_1/A01_s001_w1_z001_t001.tif"
    if not source.is_file():
        parser.error(f"Synthetic raw image missing: {source}")
    target = args.plate_path / "retained_native_20260929"
    if target.exists():
        parser.error(f"Refusing to overwrite an existing fixture: {target}")
    metadata = ImagePayloadMetadata(
        source_path=str(source),
        source_component_metadata={
            "well": "A01",
            "site": 1,
            "channel": 1,
            "z_index": 1,
            "timepoint": 1,
        },
        source_spatial_domain=SourceSpatialDomain(
            origin_yx=(0, 0), source_shape_yx=(128, 128)
        ),
        source_voxel_spacing=SourceVoxelSpacing((0.65, 0.65)),
    )
    coordinates = ((32.25, 40.5), (64.5, 80.25), (96.75, 64.0))
    points = [
        ROI(
            [PointShape(y, x)],
            {
                "label": label,
                "fixture_purpose": "synthetic transport only; not cell detections",
            },
        )
        for label, (y, x) in enumerate(coordinates, 1)
    ]
    disk = DiskStorageBackend()
    archive = target / "misleading_B99_w7_points.roi.zip"
    disk.save(ROIArchiveSourceMetadata.bind(points, metadata), archive)
    assert (
        ROIArchiveSourceMetadata.decode(load_rois_from_zip(archive)).source_provenance
        == metadata.source_provenance
    )
    labels = np.zeros((128, 128), dtype=np.int32)
    for label, (y, x) in enumerate(coordinates, 1):
        labels[int(y) - 2 : int(y) + 3, int(x) - 2 : int(x) + 3] = label
    payload = SourceImageObjectLabelBuildRequest(
        image=metadata.payload_with(np.zeros_like(labels)), labels=labels
    ).payload()
    materialized = materialize(
        MaterializationSpec(ROIOptions(min_area=0)),
        data=payload,
        path=str(target / "misleading_B99_w7_labels.roi.zip"),
        filemanager=FileManager({"disk": disk}),
        backends=["disk"],
        backend_kwargs={},
    )
    restored = ROIArchiveSourceMetadata.decode(load_rois_from_zip(Path(materialized)))
    assert restored.source_provenance == metadata.source_provenance
    assert restored.source_voxel_spacing == metadata.source_voxel_spacing
    print(
        json.dumps(
            {
                "result_directory": str(target),
                "points_archive": str(archive),
                "materialized_archive": materialized,
                "coordinates_yx": coordinates,
                "purpose": "native transport only; no scientific detector or acceptance",
            }
        )
    )


if __name__ == "__main__":
    main()
