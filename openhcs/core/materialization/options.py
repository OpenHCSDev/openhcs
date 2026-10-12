"""Typed writer options.

Greenfield design:
- the abstraction boundary is the *output format* (CSV/JSON/ROI_ZIP/TIFF/etc)
- options types are used for dispatch (metaprogramming-friendly)
"""

from __future__ import annotations

import csv
import io
from dataclasses import dataclass, field
from abc import ABC
from pathlib import Path
from typing import Any, Callable, ClassVar, Dict, List, Optional

from metaclass_registry import AutoRegisterMeta

from openhcs.core.runtime_tabular_values import ColumnarRows
from openhcs.core.runtime_measurements import RuntimeMeasurementFeature
from openhcs.core.materialization.path_scopes import (
    MaterializationRelativePathScope,
    SharedMaterializationRelativePathScope,
)


class MaterializedFilenameIdentity(ABC, metaclass=AutoRegisterMeta):
    """What a materialized artifact's filename is built from; ``name`` is its spelling."""

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type[MaterializedFilenameIdentity]]] = {}

    name: ClassVar[str | None] = None


class NameBySourceIdentity(MaterializedFilenameIdentity):
    """The source image the artifact was computed from."""

    name = "source_identity"


class NameByArtifactName(MaterializedFilenameIdentity):
    """The artifact's declared name."""

    name = "artifact_name"


@dataclass(frozen=True)
class FileOutputOptions:
    """Common filename + strip behavior."""

    filename_suffix: str = ""
    strip_roi_suffix: bool = False
    strip_pkl: bool = True
    filename_identity: type[MaterializedFilenameIdentity] = NameBySourceIdentity

    @property
    def primary_output_suffix(self) -> str:
        """Suffix for this writer's primary materialized output."""
        return self.filename_suffix


@dataclass(frozen=True)
class SourceOptions:
    """Select a sub-value from the input before writing.

    The selector is a dot-path. For dicts, keys are used. For objects, attributes.
    Example: source="branch_data".
    """

    source: Optional[str] = None


@dataclass(frozen=True)
class TabularExtractionOptions:
    """Generic extraction options for tabular writers."""

    fields: Optional[List[str]] = None
    row_field: Optional[str] = None
    row_columns: Dict[str, str] = field(default_factory=dict)
    row_unpacker: Optional[Callable[[Any], List[Dict[str, Any]]]] = None

    def declares_fields(self) -> bool:
        """Whether the columns are restricted to a declared list (possibly empty)."""
        return self.fields is not None

    def has_fields(self) -> bool:
        """Whether at least one column is declared."""
        return bool(self.fields)

    def extracts_rows(self) -> bool:
        """Whether rows come from a row field or an unpacker, not the value itself."""
        return self.row_unpacker is not None or self.row_field is not None

    def requests_extraction(self) -> bool:
        """Whether any extraction option is set."""
        return any((self.fields, self.row_field, self.row_unpacker, self.row_columns))


@dataclass(frozen=True)
class CsvOptions(FileOutputOptions, SourceOptions, TabularExtractionOptions):
    """CSV writer options."""

    filename_suffix: str = "_details.csv"

    def csv_schema(
        self,
        rows: ColumnarRows,
    ) -> tuple[tuple[str, ...], tuple[tuple[str, ...], ...]]:
        """Declare physical columns and their contextual CSV headers."""
        columns = tuple(field.name for field in rows.fields)
        return columns, (columns,)

    def header_rows(self, rows: ColumnarRows) -> tuple[tuple[str, ...], ...]:
        return self.csv_schema(rows)[1]

    def read_csv(self, text: str):
        """Read formatting-ready lexemes with this writer's dialect."""
        return csv.reader(io.StringIO(text, newline=""))

    def render_parts(
        self,
        rows: ColumnarRows,
        *,
        schema: tuple[tuple[str, ...], tuple[tuple[str, ...], ...]] | None = None,
    ) -> tuple[str, str]:
        """Derive header and complete CSV through this writer's format owner."""
        from openhcs.core.materialization.core import _render_csv_rows

        columns, _headers = self.csv_schema(rows) if schema is None else schema
        return _render_csv_rows((), columns), self.render(rows)

    def render(self, data: Any) -> str:
        """Render through the existing CSV format owner."""
        from openhcs.core.materialization.core import _render_csv

        return _render_csv(data, self)


@dataclass(frozen=True)
class JsonOptions(FileOutputOptions, SourceOptions, TabularExtractionOptions):
    """JSON writer options."""

    filename_suffix: str = ".json"
    indent: int = 2
    wrap_list: bool = False


@dataclass(frozen=True)
class ROIOptions(FileOutputOptions, SourceOptions):
    """ROI ZIP writer options."""

    min_area: int = 10
    extract_contours: bool = True
    roi_suffix: str = "_rois.roi.zip"
    summary_suffix: str = "_segmentation_summary.txt"

    @property
    def primary_output_suffix(self) -> str:
        return self.roi_suffix


@dataclass(frozen=True, kw_only=True)
class PointROIOptions(FileOutputOptions, SourceOptions):
    """Persist typed 3D object-location measurements as point ROIs."""

    z_feature: RuntimeMeasurementFeature
    y_feature: RuntimeMeasurementFeature
    x_feature: RuntimeMeasurementFeature
    filename_suffix: str = "_points.roi.zip"

    def __post_init__(self) -> None:
        features = (self.z_feature, self.y_feature, self.x_feature)
        if not all(
            isinstance(feature, RuntimeMeasurementFeature) for feature in features
        ):
            raise TypeError(
                "PointROIOptions coordinates require runtime measurement features."
            )
        if len({feature.measurement_row_field_name for feature in features}) != 3:
            raise ValueError("PointROIOptions coordinates require distinct row fields.")


@dataclass(frozen=True)
class SWCOptions(FileOutputOptions, SourceOptions):
    """SWC writer options for a rooted neuronal morphology forest."""

    filename_suffix: str = ".swc"
    root_type: int = 1
    process_type: int = 2

    def __post_init__(self) -> None:
        if self.root_type < 0 or self.process_type < 0:
            raise ValueError("SWC node type codes must be nonnegative integers.")


@dataclass(frozen=True)
class SpatialGraphROIOptions(FileOutputOptions, SourceOptions):
    """Polyline ROI ZIP writer options for spatial graph edges."""

    graph_suffix: str = ".graph.roi.zip"

    @property
    def primary_output_suffix(self) -> str:
        return self.graph_suffix


@dataclass(frozen=True)
class TiffStackOptions(FileOutputOptions, SourceOptions):
    """TIFF stack writer options (per-slice TIFF + summary)."""

    normalize_uint8: bool = False
    slice_pattern: str = "_slice_{index:03d}.tif"
    summary_suffix: str = "_summary.txt"
    empty_summary: str = "No images generated (empty data)\n"

    @property
    def primary_output_suffix(self) -> str:
        return Path(self.slice_pattern.format(index=0)).suffix


@dataclass(frozen=True)
class TextOptions(FileOutputOptions, SourceOptions):
    """Text writer options."""

    filename_suffix: str = ".txt"


@dataclass(frozen=True)
class ImageFileOptions(FileOutputOptions, SourceOptions):
    """One image file written through the registered image format family."""

    relative_path_template: str | None = None
    relative_path_scope: MaterializationRelativePathScope = field(
        default_factory=SharedMaterializationRelativePathScope
    )

    def names_files_by_template(self) -> bool:
        """Whether each file is named from ``relative_path_template``."""
        return self.relative_path_template is not None


@dataclass(frozen=True)
class FileBundleOptions(FileOutputOptions):
    """A validated mapping of relative output paths to bytes, text or typed outputs."""

    filename_identity: type[MaterializedFilenameIdentity] = NameByArtifactName
