"""Tiny explicit engineering fixture; not a segmentation or blind biology run."""

import argparse
import json
import shutil
from pathlib import Path

import numpy as np
import tifffile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    if args.destination.exists():
        parser.error("Refusing to overwrite an existing fixture.")
    raw = args.destination / "TimePoint_1"
    raw.mkdir(parents=True)
    shutil.copyfile(
        Path(__file__).with_name("orthogonal_plate.HTD"), args.destination / "plate.HTD"
    )
    z, y, x = np.mgrid[:9, :64, :80]
    first = ((z - 4) / 2.5) ** 2 + ((y - 24) / 10) ** 2 + ((x - 28) / 12) ** 2
    second = ((z - 3) / 1.8) ** 2 + ((y - 44) / 7) ** 2 + ((x - 56) / 9) ** 2
    volume = (1000 + 35000 * np.exp(-first) + 24000 * np.exp(-second)).astype(np.uint16)
    paths = []
    for channel in (1, 2):
        for plane in range(9):
            path = raw / f"A01_s001_w{channel}_z{plane+1:03d}_t001.tif"
            tifffile.imwrite(path, volume[plane] // channel, photometric="minisblack")
            paths.append(str(path.relative_to(args.destination)))
    print(
        json.dumps(
            {
                "purpose": "Synthetic native orthogonal transport/rendering only",
                "plate": str(args.destination),
                "shape_zyx": list(volume.shape),
                "file_paths": paths,
                "declared_synthetic_xy_spacing_um": 0.8,
                "physical_z_spacing_known": False,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
