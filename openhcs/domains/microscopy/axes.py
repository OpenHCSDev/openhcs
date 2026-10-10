"""The microscopy axis family: the axes of a high-content screening plate."""

import re

from openhcs.core.axes import (
    Axis,
    AxisFamily,
    ColourAxis,
    ConstantValue,
    DefaultGroupBy,
    DefaultVariable,
    GridAddressed,
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
        "openhcs.interop.cellprofiler.dataset_scope",
        "openhcs.interop.cellprofiler.pipeline_importer",
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
        label = "Ch"
        filename_prefix = "w"
        metadata_aliases = ("channel", "channelnumber")
        metadata_fallback = ImageSetOrdinal()

    class ZIndex(Axis, StackAxis, OrdinalValued):
        name = "z_index"
        label = "Z"
        filename_prefix = "z"
        filename_padding = 3
        metadata_aliases = ("zindex", "z", "zplane", "zslice", "plane", "slice")
        metadata_collection_field = "z_indexes"

    class Timepoint(Axis, TimeAxis, OrdinalValued):
        name = "timepoint"
        label = "T"
        filename_prefix = "t"
        filename_padding = 3
        metadata_aliases = ("timepoint", "time", "framenumber", "frame")

    class Well(Axis, PartitionAxis, GridAddressed, LabelValued):
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
        default_grid = (8, 12)  # a 96-well plate

        @classmethod
        def grid_coordinates(cls, value: object) -> tuple[str, str]:
            """Split ``A01`` into its row letters and column digits."""

            match = re.match(r"^([A-Za-z]+)([0-9]+)$", str(value))
            if match is None:
                raise ValueError(f"{value!r} is not a well spelled <row letters><column>.")
            return match.group(1), match.group(2)

        @classmethod
        def grid_position(cls, row_label: str, column_label: str) -> tuple[int, int]:
            """Rows count A=1 … Z=26, AA=27; columns are the column number."""

            if not row_label.isalpha() or not column_label.isdecimal():
                raise ValueError(f"Not a well row and column: {row_label!r}, {column_label!r}.")
            row = 0
            for letter in row_label.upper():
                row = row * 26 + (ord(letter) - ord("A") + 1)
            return row, int(column_label)

        @classmethod
        def row_label(cls, row: int) -> str:
            """Inverse of the row count in :meth:`grid_position` (1=A, 27=AA)."""

            label = ""
            while row > 0:
                row, remainder = divmod(row - 1, 26)
                label = chr(ord("A") + remainder) + label
            return label

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
