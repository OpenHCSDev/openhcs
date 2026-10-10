"""The microscopy axis family: the axes of a high-content screening plate."""

from openhcs.core.axes import (
    Axis,
    AxisFamily,
    ColourAxis,
    DefaultGroupBy,
    DefaultVariable,
    LabelValued,
    OrdinalValued,
    PartitionAxis,
    StackAxis,
    TileAxis,
    TimeAxis,
)


class Microscopy(AxisFamily):
    """Plate axes in canonical filename order; wells run in parallel."""

    payload_spatial_rank = 2

    class Site(Axis, TileAxis, DefaultVariable, OrdinalValued):
        name = "site"
        filename_prefix = "s"
        filename_padding = 3

    class Channel(Axis, ColourAxis, DefaultGroupBy, OrdinalValued):
        name = "channel"
        filename_prefix = "w"

    class ZIndex(Axis, StackAxis, OrdinalValued):
        name = "z_index"
        filename_prefix = "z"
        filename_padding = 3

    class Timepoint(Axis, TimeAxis, OrdinalValued):
        name = "timepoint"
        filename_prefix = "t"
        filename_padding = 3

    class Well(Axis, PartitionAxis, LabelValued):
        name = "well"
