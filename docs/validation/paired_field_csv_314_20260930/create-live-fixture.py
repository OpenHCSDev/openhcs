"""Author tiny known-value inputs; never reads or alters biological images."""

import sys
from pathlib import Path

import numpy as np
import tifffile


root = Path(sys.argv[1])
root.mkdir(parents=True, exist_ok=False)
(root / "plate.HTD").write_text(
    '"XSites", 1\n"YSites", 1\n"PixelSizeUM", 0.65\n'
)
images = root / "TimePoint_1"
images.mkdir()
for well in ("A01", "B01"):
    dna = np.zeros((32, 32), dtype=np.uint16)
    dna[5:9, 5:9] = 12000
    dna[22:26, 22:26] = 18000
    for channel, image in ((1, dna), (2, np.full((32, 32), 24000, dtype=np.uint16))):
        tifffile.imwrite(images / f"{well}_s001_w{channel}_z001_t001.tif", image)
print(root)
