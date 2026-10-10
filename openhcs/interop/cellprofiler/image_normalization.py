"""CellProfiler image intensity normalization semantics."""

from __future__ import annotations

from typing import Any

import numpy as np



def normalize_cellprofiler_image_payload(
    payload: Any,
    *,
    dtype: Any = np.float32,
    channel_index: int = 0,
) -> Any:
    """Return payload in native CellProfiler's float image intensity domain."""
    return payload.normalize_intensity_payload(dtype=np.dtype(dtype),
        channel_index=channel_index,)
