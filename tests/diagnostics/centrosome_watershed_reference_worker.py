"""Run the installed CellProfiler 4.2 watershed primitive on a synthetic fixture.

This worker runs under the existing Python 3.9 oracle environment. It imports
neither OpenHCS nor CellProfiler's GUI/JVM startup. Input is NPZ, output is NPY;
both use NumPy's non-pickle array format, not a second production wire protocol.
"""

from dataclasses import dataclass, fields
from io import BytesIO
import sys

import numpy as np
from skimage.segmentation import watershed


@dataclass(frozen=True)
class WatershedReferenceFixture:
    image: np.ndarray
    markers: np.ndarray
    mask: np.ndarray
    connectivity: np.ndarray

    @classmethod
    def read(cls, source):
        with np.load(BytesIO(source.read()), allow_pickle=False) as arrays:
            return cls(**{field.name: arrays[field.name] for field in fields(cls)})

    def execute(self):
        # NPZ scalar arrays decode to the scalar connectivity accepted by the
        # external skimage API; footprints remain arrays.
        connectivity = (
            self.connectivity.item() if self.connectivity.ndim == 0 else self.connectivity
        )
        return watershed(
            image=self.image, markers=self.markers, mask=self.mask,
            connectivity=connectivity,
        )


if __name__ == "__main__":
    fixture = WatershedReferenceFixture.read(sys.stdin.buffer)
    result = BytesIO()
    np.save(result, fixture.execute(), allow_pickle=False)
    sys.stdout.buffer.write(result.getvalue())
