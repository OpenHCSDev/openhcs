"""On the labels the two failing workflows produced: does a last-bit change in arccos move the enclosing circle, and how far do shape Zernikes move?"""
import glob
import math
import sys

import numpy as np

from openhcs.processing.backends.cellprofiler import label_geometry as lg
from openhcs.processing.backends.cellprofiler import zernike as zk

glibc = lambda v: np.array([math.acos(x) for x in np.asarray(v, float)])
cr = lambda v: np.arccos(np.asarray(v, np.longdouble)).astype(np.float64)


def perturbed(seed):
    rng = np.random.default_rng(seed)

    def f(v):
        base = glibc(v)
        step = rng.integers(-1, 2, size=base.size)
        out = base.copy()
        out[step > 0] = np.nextafter(base[step > 0], np.inf)
        out[step < 0] = np.nextafter(base[step < 0], -np.inf)
        return np.clip(out, 0.0, np.pi)

    return f


def circle(lab, ids, fn):
    lg._numpy_124_arccos = fn
    return lg.minimum_enclosing_circle_from_labels(lab, ids)


idx = zk._zernike_indexes_array(9)
seen = set()
for path in sorted(glob.glob(sys.argv[1] + "/circle_*.npz")):
    d = np.load(path)
    lab, ids = d["labels"], d["ids"]
    key = (lab.shape, int(lab.sum()), ids.size)
    if key in seen or ids.size == 0:
        continue
    seen.add(key)
    c0, r0 = circle(lab, ids, glibc)
    z0 = zk._shape_zernike_moments_with_geometry(idx, lab, ids, c0, r0)
    # how many arccos inputs differ between glibc and correctly rounded
    print(f"{path.split('/')[-1][:28]} shape={lab.shape} objects={ids.size}")
    for name, fn in (("correctly-rounded", cr), ("+-1ulp a", perturbed(1)), ("+-1ulp b", perturbed(2))):
        c1, r1 = circle(lab, ids, fn)
        bits = (r1 != r0) | (c1 != c0).any(axis=1)
        z1 = zk._shape_zernike_moments_with_geometry(idx, lab, ids, c1, r1)
        dz = np.abs(z1 - z0)
        moved = (dz > 1e-6).any(axis=1)
        with np.errstate(invalid="ignore", divide="ignore"):
            rel_r = np.nanmax(np.abs(r1 - r0) / r0) if ids.size else 0
        print(
            f"   {name:18s} circles changed in any bit: {int(bits.sum()):4d}  max rel radius change {rel_r:.2e}"
            f"  objects with a Zernike moved >1e-6: {int(moved.sum()):4d}  max |dZ| {np.nanmax(dz):.3e}"
        )
