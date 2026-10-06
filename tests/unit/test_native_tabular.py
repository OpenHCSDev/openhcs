"""Native tabular boundaries preserve standard CSV and shared measurement semantics."""

import csv
import io
from collections import UserDict
from decimal import Decimal
from fractions import Fraction

import numpy as np
import pytest

from openhcs.core import _tabular_native as native
from openhcs.core.measurement_row_materialization import (
    MEASUREMENT_SPARSE_CELL,
    MeasurementSparseCell,
    _measurement_sparse_cell_values_equal,
)
from openhcs.processing.backends.cellprofiler.spreadsheet_export import (
    SpreadsheetDelimiter,
    SpreadsheetNanRepresentation,
    SpreadsheetFileSelection,
)


@pytest.mark.parametrize("delimiter", tuple(SpreadsheetDelimiter))
@pytest.mark.parametrize("mode", tuple(SpreadsheetNanRepresentation))
def test_csv_matches_standard_writer_with_explicit_nonfinite_values(delimiter, mode):
    values = (
        None,
        "",
        True,
        False,
        0,
        -(2**100),
        2**100,
        1.23456789012345,
        -0.0,
        float("nan"),
        float("inf"),
        float("-inf"),
        np.float32(1.25),
        np.float64(1e-200),
        np.int64(42),
        np.uint64(2**64 - 1),
        np.bool_(True),
        Decimal("NaN"),
        Decimal("1.234"),
        Fraction(3, 7),
        "a,b",
        "a\tb",
        "x\ny",
        "x\ry",
        '"quoted"',
        "caf\u00e9",
        "\U0001f600",
        "\ud800",
        "\udfff",
        "\u2028",
        "a\0b",
        b"bytes",
        (1, 2),
    )
    normalized = list(values)
    normalized[9:12] = (
        ("", "", "")
        if mode is SpreadsheetNanRepresentation.NULL
        else ("NaN", "Inf", "-Inf")
    )
    stream = io.StringIO(newline="")
    writer = csv.writer(stream, delimiter=delimiter.value, lineterminator="\n")
    writer.writerow(("index", "value"))
    writer.writerows(enumerate(normalized))
    expected = stream.getvalue()
    rows = tuple({"index": index, "value": value} for index, value in enumerate(values))
    assert (
        SpreadsheetFileSelection(("Image",), "Image.csv").render_csv(
            rows,
            active_subjects=("Image",),
            delimiter=delimiter,
            nan_representation=mode,
        )
        == expected
    )
    assert (
        SpreadsheetFileSelection(("Image",), "Image.csv").render_csv(
            tuple(UserDict(row) for row in rows),
            active_subjects=("Image",),
            delimiter=delimiter,
            nan_representation=mode,
        )
        == expected
    )


@pytest.mark.parametrize(
    "rows,expected",
    (
        ((), ""),
        (({},), ""),
        (({"value": None},), 'value\n""\n'),
        (({"value": ""},), 'value\n""\n'),
        (({"first": 1}, {"second": 2}), "first,second\n1,\n,2\n"),
    ),
)
def test_empty_cells_and_missing_columns(rows, expected):
    assert (
        SpreadsheetFileSelection(("Image",), "Image.csv").render_csv(
            rows,
            active_subjects=("Image",),
            delimiter=SpreadsheetDelimiter.COMMA,
            nan_representation=SpreadsheetNanRepresentation.NAN,
        )
        == expected
    )


def test_unicode_subclasses_are_not_stringified_again():
    class Text(str):
        def __str__(self):
            raise AssertionError("csv.writer uses Unicode subclasses directly")

    assert (
        SpreadsheetFileSelection(("Image",), "Image.csv").render_csv(
            ({Text("field"): Text("a,b")},),
            active_subjects=("Image",),
            delimiter=SpreadsheetDelimiter.COMMA,
            nan_representation=SpreadsheetNanRepresentation.NAN,
        )
        == 'field\n"a,b"\n'
    )


def test_csv_normalizes_whole_row_before_stringification_and_retains_values():
    events = []
    row = {}

    class First:
        def __str__(self):
            events.append("stringify:first")
            return "first"

    class Second(float):
        def __float__(self):
            events.append("normalize:second")
            del row["first"]
            return 1.0

        def __str__(self):
            events.append("stringify:second")
            return "second"

    row.update(first=First(), second=Second(1))
    result = SpreadsheetFileSelection(("Image",), "Image.csv").render_csv(
        (row,),
        active_subjects=("Image",),
        delimiter=SpreadsheetDelimiter.COMMA,
        nan_representation=SpreadsheetNanRepresentation.NAN,
    )
    assert result == "first,second\nfirst,second\n"
    assert events == ["normalize:second", "stringify:first", "stringify:second"]


def test_nonfinite_float_subclass_skips_its_stringification():
    class BecomesNan(float):
        def __float__(self):
            return float("nan")

        def __str__(self):
            raise AssertionError("normalized nonfinite values are already text")

    assert (
        SpreadsheetFileSelection(("Image",), "Image.csv").render_csv(
            ({"value": BecomesNan(1)},),
            active_subjects=("Image",),
            delimiter=SpreadsheetDelimiter.COMMA,
            nan_representation=SpreadsheetNanRepresentation.NAN,
        )
        == "value\nNaN\n"
    )


def test_numeric_conversion_failure_does_not_poison_next_render():
    with pytest.raises(OverflowError):
        SpreadsheetFileSelection(("Image",), "Image.csv").render_csv(
            ({"value": 10**500},),
            active_subjects=("Image",),
            delimiter=SpreadsheetDelimiter.COMMA,
            nan_representation=SpreadsheetNanRepresentation.NAN,
        )
    assert (
        SpreadsheetFileSelection(("Image",), "Image.csv").render_csv(
            ({"value": 1.0},),
            active_subjects=("Image",),
            delimiter=SpreadsheetDelimiter.COMMA,
            nan_representation=SpreadsheetNanRepresentation.NAN,
        )
        == "value\n1.0\n"
    )


def test_scalar_assignment_uses_shared_nan_and_array_equality():
    target = {"nan": float("nan"), "array": np.array([1.0, np.nan])}
    missing = object()
    native.assign_cell(
        target,
        (0, 7),
        "nan",
        float("nan"),
        missing,
        _measurement_sparse_cell_values_equal,
    )
    native.assign_cell(
        target,
        (0, 7),
        "array",
        np.array([1.0, np.nan]),
        missing,
        _measurement_sparse_cell_values_equal,
    )
    with pytest.raises(
        ValueError, match="Conflicting sparse measurement values for row identity"
    ):
        native.assign_cell(
            target,
            (0, 7),
            "array",
            np.array([2.0, np.nan]),
            missing,
            _measurement_sparse_cell_values_equal,
        )
    assert np.array_equal(target["array"], [1, np.nan], equal_nan=True)


def test_feature_assignment_preserves_sparse_skip_and_callback_read_order():
    events = []
    target = {}
    later_values = [2]
    columns = (
        ("missing", [MEASUREMENT_SPARSE_CELL]),
        ("first", [1]),
        ("later", later_values),
    )

    def project(name, qualifiers):
        events.append(name)
        if name == "first":
            later_values[0] = 3
        return name

    native.assign_columns(
        target,
        (0, 7),
        columns,
        0,
        project,
        (),
        MeasurementSparseCell,
        MEASUREMENT_SPARSE_CELL,
        _measurement_sparse_cell_values_equal,
    )
    assert events == ["first", "later"]
    assert target == {"first": 1, "later": 3}


def test_conflict_stops_column_projection_with_original_partial_assignment():
    events = []
    target = {"duplicate": 9}

    def project(name, qualifiers):
        events.append(name)
        return name

    columns = (("first", [1]), ("duplicate", [2]), ("later", [3]))
    with pytest.raises(ValueError) as error:
        native.assign_columns(
            target,
            (0, 7),
            columns,
            0,
            project,
            (),
            MeasurementSparseCell,
            MEASUREMENT_SPARSE_CELL,
            _measurement_sparse_cell_values_equal,
        )
    assert (
        str(error.value)
        == "Conflicting sparse measurement values for row identity (0, 7), field 'duplicate': 9 vs 2."
    )
    assert events == ["first", "duplicate"]
    assert target == {"duplicate": 9, "first": 1}


def test_custom_mutable_mapping_assignment_respects_its_public_methods():
    target = UserDict()
    native.assign_cell(
        target,
        (0, 7),
        "value",
        1,
        MEASUREMENT_SPARSE_CELL,
        _measurement_sparse_cell_values_equal,
    )
    assert target == {"value": 1}
