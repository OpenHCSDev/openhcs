"""Generate two tiny deterministic TIFF planes, never read scientific images."""

import hashlib
import json
from pathlib import Path

import numpy as np
import tifffile


def main() -> None:
    root = Path("/run/media/ts/hdd/openhcs-engineering/execution-axis1005-20261006/input")
    root.mkdir(parents=True, exist_ok=False)
    receipts = []
    for well, value in (("A01", 0.2), ("A02", 0.8)):
        image = np.full((32, 32), value, dtype=np.float32)
        path = root / f"probe_{well}_s1_w1.tif"
        tifffile.imwrite(path, image, photometric="minisblack")
        receipts.append({
            "path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "shape": list(image.shape), "dtype": str(image.dtype), "value": float(image[0, 0]),
        })
    print(json.dumps(receipts, indent=2))


if __name__ == "__main__":
    main()
