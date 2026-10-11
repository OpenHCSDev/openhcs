"""The measurement dialect family: one ABC names rows; domains and formats subclass it."""

from __future__ import annotations

from collections.abc import Iterator

import pytest

from openhcs.core.axes import (
    Axis,
    AxisFamily,
    ColourAxis,
    DefaultGroupBy,
    DefaultVariable,
    LabelValued,
    OrdinalValued,
    PartitionAxis,
    TileAxis,
)
from openhcs.core.measurement_dialect import (
    MeasurementDialect,
    PlainMeasurementDialect,
)
from openhcs.core.runtime_measurements import MeasurementScope, MeasurementSubject
from openhcs.domains.microscopy.axes import Microscopy
from openhcs.interop.cellprofiler.measurement_dialect import (
    CELLPROFILER_MEASUREMENT_DIALECT,
)
from openhcs.processing.materialization.core import _render_csv_rows


class Survey(AxisFamily):
    payload_spatial_rank = 2

    class Plot(Axis, TileAxis, DefaultVariable, OrdinalValued):
        name = "plot"

    class Band(Axis, ColourAxis, DefaultGroupBy, OrdinalValued):
        name = "band"

    class Site(Axis, PartitionAxis, LabelValued):
        name = "site"


class SurveyDialect(MeasurementDialect):
    dialect_name = "survey"
    axis_family = Survey

    def scope_name(self, scope: MeasurementScope) -> str:
        return {MeasurementScope.SAMPLE: "scan"}.get(scope, scope.value)

    def row_field_name(self, field_name: str) -> str:
        return {"slice_index": "scan_index"}.get(field_name, field_name)


@pytest.fixture
def survey() -> Iterator[type[Survey]]:
    Survey.activate()
    try:
        yield Survey
    finally:
        Microscopy.activate()


def test_a_family_without_its_own_dialect_writes_kernel_names() -> None:
    assert type(MeasurementDialect.for_family(Microscopy)) is PlainMeasurementDialect
    assert _render_csv_rows(({"slice_index": 0, "count": 3},), ("slice_index", "count")) == (
        "slice_index,count\r\n0,3\r\n"
    )


def test_the_active_family_names_written_rows_through_its_dialect(survey) -> None:
    assert type(MeasurementDialect.for_active_family()) is SurveyDialect
    assert _render_csv_rows(({"slice_index": 0, "count": 3},), ("slice_index", "count")) == (
        "scan_index,count\r\n0,3\r\n"
    )


def test_each_dialect_spells_the_unqualified_sample() -> None:
    names = MeasurementDialect.unqualified_sample_names()
    assert {"", "sample", "image", "scan"} <= names
    for name in ("sample", "Image", "scan"):
        assert MeasurementSubject(MeasurementScope.SAMPLE, name).source_image_name is None
    assert (
        MeasurementSubject(MeasurementScope.SAMPLE, "DNA").source_image_name == "DNA"
    )


def test_cellprofiler_spells_scopes_and_sample_numbers_in_its_own_dialect() -> None:
    dialect = CELLPROFILER_MEASUREMENT_DIALECT
    plain = PlainMeasurementDialect.shared()

    assert dialect.scope_name(MeasurementScope.SAMPLE) == "Image"
    assert dialect.scope_name(MeasurementScope.RUN) == "Experiment"
    assert dialect.scope_name(MeasurementScope.OBJECT) == "Object"
    assert plain.scope_name(MeasurementScope.SAMPLE) == "sample"

    contract = dialect.row_identity_contract
    assert contract.is_sample_number_reference("Parent_ImageNumber_Nuclei")
    assert contract.is_aggregate_sample_number_reference("Mean_Nuclei_ImageNumber")
    assert not contract.is_sample_number_reference("ImageNumber")
    assert not plain.row_identity_contract.is_sample_number_reference(
        "Parent_ImageNumber_Nuclei"
    )
    assert dialect.spatial_grid_measurement_feature_name("Grid", "x_spacing") == (
        "DefinedGrid_Grid_XSpacing"
    )
    assert plain.spatial_grid_measurement_feature_name("Grid", "x_spacing") == (
        "spatial_grid_grid_x_spacing"
    )
