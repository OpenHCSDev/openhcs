"""Shared helpers for materialization handlers.

Keep this module free of backend/registry concerns.
"""

from __future__ import annotations

from dataclasses import fields, is_dataclass
from typing import Any, Dict, List, Optional, Tuple


def extract_fields(item: Any, field_names: Optional[List[str]] = None) -> Dict[str, Any]:
    """Extract fields from dataclass, dict, or pandas objects.

    Supports:
    - dataclass instances (uses dataclass reflection)
    - dicts (uses dict keys)
    - pandas DataFrames (uses column names)
    - pandas Series (uses index)
    """

    # pandas (optional)
    try:
        import pandas as pd

        if isinstance(item, pd.DataFrame):
            if field_names:
                return {f: item[f].tolist() for f in field_names if f in item.columns}
            return {col: item[col].tolist() for col in item.columns}

        if isinstance(item, pd.Series):
            if field_names:
                return {f: item[f] for f in field_names if f in item.index}
            return item.to_dict()
    except ImportError:
        pass

    if is_dataclass(item):
        if field_names:
            return {f: getattr(item, f, None) for f in field_names if hasattr(item, f)}
        return {f.name: getattr(item, f.name) for f in fields(item)}

    if isinstance(item, dict):
        if field_names:
            return {f: item.get(f) for f in field_names if f in item}
        return item

    return {"value": item}


def coerce_jsonable(value: Any) -> Any:
    """Convert numpy scalars/arrays to JSON-serializable Python types."""
    try:
        import numpy as np

        if isinstance(value, np.generic):
            return value.item()
        if isinstance(value, np.ndarray):
            return value.tolist()
    except Exception:
        pass
    return value


def normalize_slices(obj: Any, *, name: str):
    """Normalize input to list of 2D numpy arrays."""
    import numpy as np

    if obj is None:
        return []
    if isinstance(obj, list):
        return [np.asarray(x) for x in obj]
    arr = np.asarray(obj)
    if arr.ndim == 2:
        return [arr]
    if arr.ndim == 3:
        return [arr[i] for i in range(arr.shape[0])]
    raise ValueError(f"{name} must be a 2D/3D array or list of 2D arrays, got shape {arr.shape}")


def discover_array_fields(item: Any) -> List[str]:
    """Discover array/tuple fields in a dataclass instance."""
    if not hasattr(item, "__dataclass_fields__"):
        return []

    from typing import get_origin

    array_fields: List[str] = []
    for f in fields(item):
        value = getattr(item, f.name, None)
        origin = hasattr(f.type, "__origin__") and get_origin(f.type)
        if origin in (list, List, tuple, Tuple):
            array_fields.append(f.name)
        elif isinstance(value, list) and value and isinstance(value[0], (tuple, list)):
            array_fields.append(f.name)
    return array_fields


def expand_array_field(
    array_data: List[Any],
    base_row: Dict[str, Any],
    row_columns: Dict[str, str],
) -> List[Dict[str, Any]]:
    """Expand an array field into multiple rows."""
    if not array_data:
        return [base_row]

    rows: List[Dict[str, Any]] = []
    for elem in array_data:
        if isinstance(elem, (list, tuple)):
            cols = {
                col: elem[int(idx)]
                for idx, col in row_columns.items()
                if str(idx).isdigit() and int(idx) < len(elem)
            }
        else:
            cols = {}
        rows.append({**base_row, **cols})
    return rows
