"""Put native CellProfiler AreaShape values back on the objects they measured.

CellProfiler's ``MeasureObjectSizeShape.analyze_objects`` records the
``regionprops_table`` vectors (and the radius vectors built from them), which
hold one value per *non-empty* label in label order, and the CSV writer then
assigns value *i* to ``ObjectNumber`` *i + 1*. When a declared object is empty
(an unoccupied grid cell, a cytoplasm swallowed by its nucleus), every later
object in that image receives its predecessor's area, centre, radius and so on.
Feret diameters and Zernike moments are indexed by label and are not affected;
in 3-D every AreaShape vector is positional.

OpenHCS writes each value on the object it measured, so a native reference is
compared after undoing that positional write. The undo is a permutation of the
native values inside each image: the non-empty objects (finite
``Location_Center_X``, which CellProfiler records by label) take the leading
positions in order, and the empty objects take the trailing positions. No
value is invented or dropped.
"""

from __future__ import annotations

import math
from dataclasses import replace

from benchmark.equivalence.table_snapshots import RuntimeTableSnapshot

_IMAGE_NUMBER = "ImageNumber"
_OBJECT_NUMBER = "ObjectNumber"
_LOCATION_X = "Location_Center_X"
_SHAPE_PREFIX = "AreaShape_"
_VOLUME = "AreaShape_Volume"
_LABEL_INDEXED_2D = ("AreaShape_MinFeretDiameter", "AreaShape_MaxFeretDiameter")
_LABEL_INDEXED_2D_PREFIX = "AreaShape_Zernike_"


def positional_shape_columns(header: tuple[str, ...]) -> tuple[int, ...]:
    """Columns CellProfiler writes by position rather than by label."""
    volumetric = _VOLUME in header
    return tuple(
        index
        for index, column in enumerate(header)
        if column.startswith(_SHAPE_PREFIX)
        and (
            volumetric
            or (
                column not in _LABEL_INDEXED_2D
                and not column.startswith(_LABEL_INDEXED_2D_PREFIX)
            )
        )
    )


def _is_finite(text: str) -> bool:
    try:
        return math.isfinite(float(text))
    except ValueError:
        return False


def shape_rows_on_their_labels(table: RuntimeTableSnapshot) -> RuntimeTableSnapshot:
    """Return a native object table with positional AreaShape values undone."""
    header = table.header
    if not {_IMAGE_NUMBER, _OBJECT_NUMBER, _LOCATION_X} <= set(header):
        return table
    columns = positional_shape_columns(header)
    if not columns:
        return table
    image_index = header.index(_IMAGE_NUMBER)
    object_index = header.index(_OBJECT_NUMBER)
    location_index = header.index(_LOCATION_X)
    row_indexes_by_image: dict[str, list[int]] = {}
    for row_index, row in enumerate(table.rows):
        row_indexes_by_image.setdefault(row[image_index], []).append(row_index)
    rows = [list(row) for row in table.rows]
    for row_indexes in row_indexes_by_image.values():
        ordered = sorted(row_indexes, key=lambda index: float(rows[index][object_index]))
        measured = [index for index in ordered if _is_finite(rows[index][location_index])]
        if len(measured) == len(ordered):
            continue
        empty = [index for index in ordered if index not in set(measured)]
        positional = {
            column: [rows[index][column] for index in ordered] for column in columns
        }
        for position, row_index in enumerate((*measured, *empty)):
            for column in columns:
                rows[row_index][column] = positional[column][position]
    return replace(table, rows=tuple(tuple(row) for row in rows))
