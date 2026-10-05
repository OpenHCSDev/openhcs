"""Stage the existing branched-neuron engineering fixture, never run analysis.

Geometry/values are the unchanged branched case of
tests/unit/test_neurite_outgrowth.py::_draw_fluorescent_neuron.
Invoke only in the receiving owner's newly admitted acquisition directory.
"""
import argparse
from pathlib import Path

import numpy as np
from skimage.draw import disk, line
import tifffile


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("acquisition", type=Path)
    args = parser.parse_args()
    path = args.acquisition / "A01_s1_w2_z1_t1.tif"
    if path.exists():
        raise FileExistsError(path)
    image = np.zeros((128, 128), dtype=np.uint16)
    rows, columns = disk((64, 20), 9, shape=image.shape)
    image[rows, columns] = 1000
    for start, end in (
        ((64, 28), (64, 115)),
        ((64, 75), (35, 105)),
        ((64, 75), (93, 105)),
    ):
        rows, columns = line(*start, *end)
        image[rows, columns] = 700
    args.acquisition.mkdir(parents=True, exist_ok=True)
    # Scalar YX TIFF: channel is acquisition metadata, not a stored stack axis.
    with path.open("xb") as stream:
        tifffile.imwrite(stream, image, photometric="minisblack")


if __name__ == "__main__":
    main()
