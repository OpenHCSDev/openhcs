"""Create explicit synthetic POINT ROIs for the installed managed-viewer check.

Run with the isolated installed Python, not a source-override environment.
The input must already be a 128x128 synthetic plate; this does not segment cells.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from polystore.disk import DiskStorageBackend
from polystore.roi import PointShape, ROI


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("plate_path", type=Path)
    args = parser.parse_args()
    source = args.plate_path / "TimePoint_1/A01_s001_w1_z001_t001.tif"
    if not source.is_file():
        parser.error(f"Synthetic source image is absent: {source}")
    target = args.plate_path / "images_results/A01_s001_w1_z001_t001.roi.zip"
    if target.exists():
        parser.error(f"Refusing to overwrite an existing archive: {target}")
    coordinates = ((32.25, 40.5), (64.5, 80.25), (96.75, 64.0))
    rois = [
        ROI(
            [PointShape(y, x)],
            metadata={
                "label": label,
                "object_name": "synthetic_transport_points",
                "source_image_name": source.name,
                "source_spatial_shape_yx": (128, 128),
                "fixture_purpose": "POINT transport only; not cell detections",
            },
        )
        for label, (y, x) in enumerate(coordinates, start=1)
    ]
    DiskStorageBackend().save(rois, target)
    restored = DiskStorageBackend().load(target)
    assert [roi.shapes for roi in restored] == [roi.shapes for roi in rois]
    assert [roi.metadata for roi in restored] == [roi.metadata for roi in rois]
    print(json.dumps({"archive": str(target), "coordinates_yx": coordinates}))


if __name__ == "__main__":
    main()
