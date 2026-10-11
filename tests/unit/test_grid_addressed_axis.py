"""The grid role: placement lives on the grid axis, and only a family with one has a grid."""

from __future__ import annotations

import pytest

from openhcs.core.axes import (
    Axis,
    AxisFamily,
    GridAddressed,
    LabelValued,
    OrdinalValued,
    PartitionAxis,
    TileAxis,
)
from openhcs.core.component_filters import ComponentFilters
from openhcs.domains.microscopy.axes import Microscopy
from openhcs.pyqt_gui.widgets.shared.plate_view_widget import active_grid_axis


class _Survey(AxisFamily):
    payload_spatial_rank = 2

    class Plot(Axis, TileAxis, OrdinalValued):
        name = "plot"

    class Region(Axis, PartitionAxis, LabelValued):
        name = "region"


def test_microscopy_grid_axis_is_the_well_and_places_its_values() -> None:
    assert Microscopy.with_role(GridAddressed) == (Microscopy.Well,)
    assert Microscopy.Well.default_grid == (8, 12)
    assert Microscopy.Well.grid_index("B03") == (2, 3)
    assert Microscopy.Well.grid_index("AA10") == (27, 10)
    assert Microscopy.Well.grid_index("R01C03") is None
    assert Microscopy.Well.grid_position("C", "04") == (3, 4)
    assert [Microscopy.Well.row_label(row) for row in (1, 26, 27, 52)] == [
        "A",
        "Z",
        "AA",
        "AZ",
    ]


def test_a_family_without_a_grid_axis_has_no_plate_grid() -> None:
    _Survey.activate()
    try:
        assert active_grid_axis() is None
    finally:
        Microscopy.activate()
    assert active_grid_axis() is Microscopy.Well


def test_a_grid_axis_must_declare_its_placement() -> None:
    with pytest.raises(TypeError, match="must declare default_grid"):

        class _Undeclared(AxisFamily):
            payload_spatial_rank = 2

            class Cell(Axis, PartitionAxis, GridAddressed, LabelValued):
                name = "cell"


def test_component_filters_validate_against_the_family_and_match_generically() -> None:
    filters = ComponentFilters.from_mapping({"well": ["A01", "B02"], "channel": "1"})
    assert filters.matches({"well": "B02", "channel": 1, "site": 3})
    assert not filters.matches({"well": "C03", "channel": 1})
    assert not filters.matches({"channel": 1})
    assert ComponentFilters.from_assignments(["well=A01", "well=B02", "channel=1"]) == filters
    assert ComponentFilters().matches({})
    with pytest.raises(ValueError, match="unknown axes"):
        ComponentFilters.from_mapping({"plot": "1"})
