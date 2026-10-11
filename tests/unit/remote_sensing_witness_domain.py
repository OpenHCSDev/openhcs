"""The remote-sensing witness domain: declarations only.

A second domain plugs into the kernel by declaring its axis family and its
measurement dialect. Nothing here is executable logic; kernel processes the
witness spawns (execution server, workers) import this module by the family's
declared name.
"""

from __future__ import annotations

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
    TimeAxis,
)
from openhcs.core.measurement_dialect import MeasurementDialect


class RemoteSensing(AxisFamily):
    """Scenes in parallel; tiles, spectral bands and acquisition dates within each."""

    payload_spatial_rank = 2

    class Tile(Axis, TileAxis, DefaultVariable, OrdinalValued):
        name = "tile"
        filename_prefix = "f"
        filename_padding = 3

    class Band(Axis, ColourAxis, DefaultGroupBy, OrdinalValued):
        name = "band"
        filename_prefix = "b"

    class Date(Axis, TimeAxis, OrdinalValued):
        name = "date"
        filename_prefix = "d"
        filename_padding = 3

    class Scene(Axis, PartitionAxis, LabelValued):
        name = "scene"


class RemoteSensingMeasurementDialect(MeasurementDialect):
    """How this domain names its measurement rows: a plane is a reading."""

    dialect_name = "remote_sensing"
    axis_family = RemoteSensing

    def row_field_name(self, field_name: str) -> str:
        return {"slice_index": "reading"}.get(field_name, field_name)
