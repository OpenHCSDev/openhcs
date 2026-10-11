from pyqt_reactive.widgets.grid_selector import GridModel

from openhcs.domains.microscopy.axes import Microscopy
from openhcs.pyqt_gui.widgets.image_browser import GridAxisAddressing

WELLS = GridAxisAddressing(Microscopy.Well)


def test_well_axis_places_standard_well_ids_on_the_plate_grid() -> None:
    model = GridModel.of(WELLS, {"B02", "C04", "AA10"})

    assert model.cell_at_position[(2, 2)] == "B02"
    assert model.cell_at_position[(3, 4)] == "C04"
    assert model.cell_at_position[(27, 10)] == "AA10"
    assert model.position_of_cell["AA10"] == (27, 10)
    assert model.dimensions == (26, 9)
    assert GridModel.of(WELLS, set()).dimensions == Microscopy.Well.default_grid
    assert Microscopy.Well.row_label(27) == "AA"
