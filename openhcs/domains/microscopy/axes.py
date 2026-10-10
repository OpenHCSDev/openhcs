"""The microscopy axis family: the axes of a high-content screening plate."""

import re

from openhcs.core.axes import (
    Axis,
    AxisFamily,
    ColourAxis,
    ConstantValue,
    DefaultGroupBy,
    DefaultVariable,
    ImageSetOrdinal,
    ImageSetOrdinalUnlessIndexedBy,
    LabelValued,
    MetadataLookup,
    OrdinalValued,
    PartitionAxis,
    StackAxis,
    TileAxis,
    TimeAxis,
)


class Microscopy(AxisFamily):
    """Plate axes in filename order; wells run in parallel."""

    config_modules = ("openhcs.domains.microscopy.config",)
    extension_modules = (
        "openhcs.microscopes",
        "openhcs.domains.microscopy.analysis_consolidation",
    )

    payload_spatial_rank = 2

    class Site(Axis, TileAxis, DefaultVariable, OrdinalValued):
        name = "site"
        filename_prefix = "s"
        filename_padding = 3
        metadata_aliases = ("site", "imagenumber")
        metadata_fallback = ImageSetOrdinalUnlessIndexedBy((StackAxis, TimeAxis))

    class Channel(Axis, ColourAxis, DefaultGroupBy, OrdinalValued):
        name = "channel"
        filename_prefix = "w"
        metadata_aliases = ("channel", "channelnumber")
        metadata_fallback = ImageSetOrdinal()

    class ZIndex(Axis, StackAxis, OrdinalValued):
        name = "z_index"
        filename_prefix = "z"
        filename_padding = 3
        metadata_aliases = ("zindex", "z", "zplane", "zslice", "plane", "slice")
        metadata_collection_field = "z_indexes"

    class Timepoint(Axis, TimeAxis, OrdinalValued):
        name = "timepoint"
        filename_prefix = "t"
        filename_padding = 3
        metadata_aliases = ("timepoint", "time", "framenumber", "frame")

    class Well(Axis, PartitionAxis, LabelValued):
        """A plate well, spelled ``<row letter><two-digit column>`` (``A01``)."""

        name = "well"
        metadata_aliases = (
            "well",
            "wellrow",
            "row",
            "wellcolumn",
            "wellcol",
            "column",
            "col",
        )
        metadata_fallback = ConstantValue("A01")

        @classmethod
        def grid_coordinates(cls, value: object) -> tuple[str, str]:
            """Split ``A01`` into its row letters and column digits."""

            match = re.match(r"^([A-Za-z]+)([0-9]+)$", str(value))
            if match is None:
                return str(value), ""
            return match.group(1), match.group(2)

        @classmethod
        def metadata_value(cls, lookup: MetadataLookup) -> str | None:
            """The well field, or a well composed from its row and column fields."""

            def first(*aliases: str) -> str | None:
                for alias in aliases:
                    value = lookup(alias)
                    if value is not None:
                        return value
                return None

            direct = first("well")
            if direct is not None:
                return direct
            row = first("wellrow", "row")
            column = first("wellcolumn", "wellcol", "column", "col")
            if row is None or column is None:
                return None
            return f"{row.strip().upper()}{int(column):02d}"
