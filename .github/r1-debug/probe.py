"""TEMPORARY (surface R1z): print the numeric environment of the runner."""

import math
import os
import platform
import sys

import numba
import numpy as np
import scipy

print("platform", platform.platform(), platform.machine(), sys.version)
print("numpy", np.__version__, "scipy", scipy.__version__, "numba", numba.__version__)
for key in ("NPY_DISABLE_CPU_FEATURES", "NUMBA_DISABLE_INTEL_SVML", "OPENHCS_CPU_ONLY"):
    print(key, os.environ.get(key))
probes = [0.1, 0.5, 0.7071067811865476, 0.9999, -0.3, 1 / 3, 0.123456789]
print("acos", [(v, math.acos(v).hex(), float(np.arccos(v)).hex()) for v in probes])
pairs = ((1e-9, -1.0), (0.3, 0.7), (-0.2, 0.1), (3.1, 4.7))
print("atan2", [(math.atan2(a, b).hex(), float(np.arctan2(a, b)).hex()) for a, b in pairs])
print("hypot", [(math.hypot(a, b).hex(), float(np.hypot(a, b)).hex()) for a, b in pairs])
angles = (0.3, 1.1, 2.9, -2.2)
print("sin", [(math.sin(v).hex(), float(np.sin(v)).hex()) for v in angles])
print("cos", [(math.cos(v).hex(), float(np.cos(v)).hex()) for v in angles])
print("exp", math.exp(0.3).hex(), float(np.exp(0.3)).hex())
print("pow", (0.3**7).hex(), float(np.power(0.3, 7)).hex())
