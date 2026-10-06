"""Losslessly wrap the pinned cells3d nucleus volume as a ZYX OME-TIFF."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path

import numpy as np
import tifffile


SOURCE_SHA256 = "e4ba6eba21412a9441d2576943594234f681bd11fa1d6d1865d36a2242118305"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    with args.source.open("rb") as source_file:
        actual_sha256 = hashlib.file_digest(source_file, "sha256").hexdigest()
    if actual_sha256 != SOURCE_SHA256:
        raise ValueError(f"source SHA-256 mismatch: {actual_sha256}")
    if args.destination.exists():
        raise FileExistsError(args.destination)

    volume = tifffile.imread(args.source)
    if volume.shape != (60, 256, 256) or volume.dtype != np.uint16:
        raise ValueError(f"unexpected source volume: {volume.shape}, {volume.dtype}")
    tifffile.imwrite(args.destination, volume, ome=True, metadata={"axes": "ZYX"})
    with tifffile.TiffFile(args.destination) as wrapped:
        if wrapped.ome_metadata is None or wrapped.series[0].axes != "ZYX":
            raise ValueError("OME-TIFF does not declare ZYX axes")
        reread = wrapped.asarray()
    if not np.array_equal(volume, reread):
        raise ValueError("OME-TIFF voxel values differ from source")
    print(f"Verified lossless ZYX OME-TIFF: {args.destination}")


if __name__ == "__main__":
    main()
