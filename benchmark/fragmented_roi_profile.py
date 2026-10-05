"""Bounded provider-free profile of the declared ROI extraction/ZIP owners."""

from __future__ import annotations

import argparse
import cProfile
import json
import pstats
from collections import Counter
from pathlib import Path
from time import perf_counter
from zipfile import ZipFile

import numpy as np
from polystore.disk import DiskStorageBackend
from polystore.roi import extract_rois_from_labeled_mask
from polystore.roi_converters import FijiROIConverter, NapariShapeMetadata


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "output_dir", type=Path, help="Owned disposable scratch directory."
    )
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    labels = np.zeros((128, 128), dtype=np.int32)
    labels[4:124:4, 4:124:4] = 188
    labels[1:3, 1:3] = 7
    labels[125:127, 125:127] = 42
    start = perf_counter()
    extract_rois_from_labeled_mask(labels, min_area=1)
    cold_extraction_seconds = perf_counter() - start
    profiler = cProfile.Profile()
    start = perf_counter()
    rois = profiler.runcall(extract_rois_from_labeled_mask, labels, min_area=1)
    warm_extraction_seconds = perf_counter() - start
    stats = pstats.Stats(profiler)
    bbox_scan_calls = sum(
        value[1] for key, value in stats.stats.items() if key[2] == "find_objects"
    )
    start = perf_counter()
    members = FijiROIConverter.rois_to_imagej_members(rois)
    encoding_seconds = perf_counter() - start
    archive = args.output_dir / "fragmented.roi.zip"
    start = perf_counter()
    DiskStorageBackend().save(rois, archive)
    archive_seconds = perf_counter() - start
    with ZipFile(archive) as zipped:
        member_count = sum(name.endswith(".roi") for name in zipped.namelist())
    print(
        json.dumps(
            {
                "shape": list(labels.shape),
                "parent_labels": [
                    NapariShapeMetadata.from_metadata(roi.metadata).label
                    for roi in rois
                ],
                "fragments_by_parent": dict(
                    Counter(
                        NapariShapeMetadata.from_metadata(member.metadata).label
                        for member in members
                    )
                ),
                "zip_roi_members": member_count,
                "cold_extraction_seconds": cold_extraction_seconds,
                "warm_extraction_seconds": warm_extraction_seconds,
                "bbox_scan_calls": bbox_scan_calls,
                "member_encoding_seconds": encoding_seconds,
                "archive_encoding_and_write_seconds": archive_seconds,
            },
            sort_keys=True,
        )
    )
    # The archive writer includes its own required conversion; this does not
    # imply production converts twice. The standalone conversion isolates cost.
    stats.strip_dirs().sort_stats("cumulative").print_stats(15)


if __name__ == "__main__":
    main()
