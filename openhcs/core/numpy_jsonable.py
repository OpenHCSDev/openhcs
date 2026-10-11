"""numpy values in ``to_jsonable``, the one value-to-JSON encoder.

Importing this module registers numpy scalars (as their Python value) and
arrays (as nested lists); modules that encode values which may be numpy import
it before calling ``to_jsonable``.
"""

from __future__ import annotations

import numpy as np
from python_introspect import JsonValue, to_jsonable


@to_jsonable.register(np.generic)
def _jsonable_numpy_scalar(value: np.generic) -> JsonValue:
    return to_jsonable(value.item())


@to_jsonable.register(np.ndarray)
def _jsonable_numpy_array(value: np.ndarray) -> JsonValue:
    return to_jsonable(value.tolist())
