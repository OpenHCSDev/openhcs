"""Declaring an empty object label never moves another label's measurements.

Every object measurement that takes a label payload is run twice on the same
labels: once declaring only the labels present, once also declaring an empty
label below them. The rows of the present labels must be identical, so a value
can never land on a neighbouring label.
"""

from __future__ import annotations

import math

import numpy as np
import pytest

from openhcs.core.runtime_measurements import MeasurementRowAxisField
from openhcs.core.runtime_object_label_domains import ObjectLabelDomain
from openhcs.core.runtime_object_labels import (
    ObjectLabelPayload,
    ObjectLabelRepresentation,
    ObjectLabelVariantData,
)
from openhcs.core.runtime_sparse_labels import SparseIJVLabelRows
from openhcs.processing.backends.cellprofiler import (
    granularity,
    intensity,
    neighbors,
    shape,
    texture,
)

PRESENT_IDS = (2, 7)
OBJECT_ID_FIELDS = MeasurementRowAxisField.object_id_field_names()
QUALIFIER_FIELDS = ("slice_index", "scale", "direction", "gray_levels")
EMPTY_ID = 1


def _plane() -> np.ndarray:
    plane = np.zeros((40, 48), dtype=np.int32)
    plane[3:12, 4:15] = 2
    plane[20:34, 22:40] = 7
    return plane


def _image(shape_: tuple[int, ...]) -> np.ndarray:
    return np.random.default_rng(0).random(shape_).astype(np.float32)


def _dense(labels: np.ndarray, ids: tuple[int, ...]) -> ObjectLabelPayload:
    return ObjectLabelPayload(
        variant_data=ObjectLabelVariantData(labels=labels),
        domain=ObjectLabelDomain(declared_object_ids=ids),
    )


def _sparse(labels: np.ndarray, ids: tuple[int, ...]) -> ObjectLabelPayload:
    y, x = np.nonzero(labels)
    ijv = np.column_stack((y, x, labels[y, x])).astype(np.int32)
    return ObjectLabelPayload(
        variant_data=ObjectLabelVariantData(labels=SparseIJVLabelRows(ijv)),
        representation=ObjectLabelRepresentation.SPARSE_IJV,
        domain=ObjectLabelDomain(declared_object_ids=ids),
    )


# (measurement, label kinds it accepts)
MEASUREMENTS = {
    "AreaShape": (
        lambda image, labels: shape.measure_object_size_shape.__wrapped__(
            image, labels, calculate_advanced=True, calculate_zernikes=True
        ),
        ("dense_2d", "dense_3d", "sparse_2d"),
    ),
    "Intensity": (
        lambda image, labels: intensity.measure_object_intensity.__wrapped__(
            image, labels
        ),
        ("dense_2d", "dense_3d"),
    ),
    "Texture": (
        lambda image, labels: texture.measure_texture_objects.__wrapped__(
            image, labels
        ),
        ("dense_2d",),
    ),
    "Granularity": (
        lambda image, labels: granularity.measure_granularity_objects.__wrapped__(
            image, labels
        ),
        ("dense_2d",),
    ),
    "Neighbors": (
        lambda image, labels: neighbors.measure_object_neighbors.__wrapped__(
            image,
            labels,
            distance_method=neighbors.DistanceMethod.EXPAND,
            neighbor_distance=5,
        ),
        ("dense_2d",),
    ),
}

LABEL_KINDS = {
    "dense_2d": (lambda: _plane(), _dense),
    "dense_3d": (lambda: np.stack((_plane(),) * 3), _dense),
    "sparse_2d": (lambda: _plane(), _sparse),
}


def _rows_by_label(result) -> dict[tuple[object, ...], dict[str, object]]:
    rows = result[-1]
    by_label: dict[tuple[object, ...], dict[str, object]] = {}
    for row in rows.row_mappings():
        row = dict(row)
        (object_id,) = (
            row[field] for field in OBJECT_ID_FIELDS if field in row
        )
        key = (object_id, *(row.get(field) for field in QUALIFIER_FIELDS))
        by_label[key] = row
    return by_label


def _same(left: object, right: object) -> bool:
    if isinstance(left, float) and isinstance(right, float):
        return (math.isnan(left) and math.isnan(right)) or left == right
    return bool(np.all(np.asarray(left) == np.asarray(right)))


@pytest.mark.parametrize(
    ("measurement", "label_kind"),
    tuple(
        (name, kind)
        for name, (_call, kinds) in MEASUREMENTS.items()
        for kind in kinds
    ),
)
def test_empty_declared_label_leaves_other_labels_unchanged(measurement, label_kind):
    call, _kinds = MEASUREMENTS[measurement]
    make_labels, make_payload = LABEL_KINDS[label_kind]
    labels = make_labels()
    image = _image(labels.shape)

    without_empty = _rows_by_label(call(image, make_payload(labels, PRESENT_IDS)))
    with_empty = _rows_by_label(
        call(image, make_payload(labels, (EMPTY_ID, *PRESENT_IDS)))
    )

    assert without_empty, f"{measurement} produced no rows"
    assert set(PRESENT_IDS) <= {key[0] for key in without_empty}
    for key, row in without_empty.items():
        assert key in with_empty, f"{measurement} lost the row of label {key}"
        moved = {
            field: (value, with_empty[key].get(field))
            for field, value in row.items()
            if not _same(value, with_empty[key].get(field))
        }
        assert not moved, f"{measurement} label {key[0]} changed: {moved}"


def test_native_cellprofiler_positional_shape_values_return_to_their_labels(tmp_path):
    from benchmark.equivalence.native_shape_rows import shape_rows_on_their_labels
    from benchmark.equivalence.table_snapshots import RuntimeTableSnapshot

    # Object 2 is empty: CellProfiler wrote object 3's area on row 2 and padded
    # the vector's tail; Location and Feret are recorded by label.
    native = tmp_path / "Cells.csv"
    native.write_text(
        "ImageNumber,ObjectNumber,Location_Center_X,AreaShape_Area,"
        "AreaShape_MaxFeretDiameter\n"
        "1,1,4.0,10,3.0\n"
        "1,2,nan,30,0.0\n"
        "1,3,9.0,nan,5.0\n"
        "2,1,2.0,7,1.0\n"
    )
    table = shape_rows_on_their_labels(RuntimeTableSnapshot.from_csv(native))
    assert [row[3] for row in table.rows] == ["10", "nan", "30", "7"]
    assert [row[4] for row in table.rows] == ["3.0", "0.0", "5.0", "1.0"]
