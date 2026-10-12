"""Compare recorded arccos results of a platform dump with round-to-nearest arccos."""
import glob, sys
import numpy as np
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from cracos import acos_rn
tot = d_used = d_libm = d_np = 0
for path in sorted(glob.glob(sys.argv[1] + "/circle_*.npz")):
    z = np.load(path)
    x = z["arccos_in"]
    if not x.size:
        continue
    ux, idx = np.unique(x, return_index=True)
    rn = np.array([acos_rn(float(v)) for v in ux])
    tot += ux.size
    d_used += int((z["arccos_out"][idx] != rn).sum())
    d_libm += int((z["arccos_libm"][idx] != rn).sum())
    d_np += int((z["arccos_numpy"][idx] != rn).sum())
print(f"distinct arccos inputs {tot}: used-by-kernel != RN {d_used}; math.acos != RN {d_libm}; np.arccos != RN {d_np}")
