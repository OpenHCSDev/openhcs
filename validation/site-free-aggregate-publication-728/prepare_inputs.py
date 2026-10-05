"""Create fresh tiny synthetic acquisition files through the original fixture.

No pipeline/runtime imports, processing, source receipts or reference images.
Source headers use the existing test_source_tile_geometry._xml declaration;
the packet must accompany the same pinned source as the whole installed owner.
"""
import hashlib
import json
from pathlib import Path
import sys

import numpy as np
import tifffile


def main():
    checkout = Path(sys.argv[1]).resolve()
    packet = Path(sys.argv[2]).resolve()
    sys.path.insert(0, str(checkout / "tests/unit"))
    from test_source_tile_geometry import _xml

    # Exclusive creation preserves the first original intent and input bytes.
    acquisition = packet / "acquisition"
    acquisition.mkdir(parents=True, exist_ok=False)
    records = []
    for channel in (2, 1):
        for site in (3, 1):
            x_pixels = 6 if site == 3 else 0
            path = acquisition / f"A01_s{site:03d}_w{channel}_z001_t001.tif"
            pixels = np.full((4, 6), 10 * channel + site, dtype=np.uint16)
            tifffile.imwrite(
                path, pixels,
                description=_xml(
                    x=x_pixels * 0.5, y=0,
                    row=1, column=2 if site == 3 else 1,
                    sx=0.5, sy=0.25,
                ),
                metadata=None,
            )
            records.append({
                "path": str(path),
                "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                "channel": channel, "site": site,
                "shape": list(pixels.shape), "value": int(pixels[0, 0]),
                "positions_xy": [x_pixels, 0],
            })
    with (packet / "INPUTS.json").open("x") as stream:
        json.dump(records, stream, indent=2)
    print(json.dumps(records, indent=2))


if __name__ == "__main__":
    main()
