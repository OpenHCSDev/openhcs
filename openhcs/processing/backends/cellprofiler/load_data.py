"""
Converted from CellProfiler: LoadData
Original: cellprofiler_core.modules.loaddata

LoadData names a pipeline's images in a CSV file instead of in its settings: one
row per image set, ``Image_FileName_<Name>`` (and optionally
``Image_PathName_<Name>`` or ``Image_URL_<Name>``) columns naming the file of
each image, ``Image_ObjectsFileName_<Name>`` columns naming label files, and
``Metadata_<Key>`` columns describing the image set.

In OpenHCS that is a source declaration, made when the pipeline is imported:

- every image and objects name becomes a named source binding, so later modules
  resolve it;
- the rows become the source sets, paired exactly as listed (``PairAsListed``):
  set N holds the files row N names, and a listed file the plate lacks is an
  error when the plate is opened, never a silently shifted pairing;
- every ``Metadata_<Key>`` column becomes the set's metadata field ``<Key>``,
  typed as CellProfiler types the column (integer, else float, else text), with
  ``Well`` composed from row and column tags when the CSV has no well column.

Settings (CellProfiler 4 revision 6):

- *Input data file location* / *Name of the file*: honoured. The CSV is an input
  file of the pipeline and is resolved like every other one: *Default Input
  Folder* is the folder holding the ``.cppipe`` (or the importer's
  ``source_root``), its sub-folder choice a folder below it, *Elsewhere...* the
  written folder, *URL* a downloaded file. The *Default Output Folder* choices
  are refused: nothing has been written when a pipeline is imported.
- *Load images based on this data?*: ``Yes`` only. ``No`` attaches the CSV's
  columns to image sets other modules build, which is refused.
- *Base image location*: every choice is read as "the plate". OpenHCS loads
  images from the plate it is pointed at, so the folder written here (often a
  path on the acquisition machine) locates nothing; a listed file is found in the
  plate by its name, and by as many of its trailing folders as it takes to tell
  it from files of the same name.
- *Process just a range of rows?* / *Rows to process*: honoured, with
  CellProfiler's numbering (rows count from 1, without the header).
- *Group images by metadata?* / *Select metadata tags for grouping*: honoured as
  the grouping fields of the source declaration.
- *Rescale intensities?*: ``Yes`` only (the scaling OpenHCS applies to every
  source image). ``No`` is refused.

Refused, each with a message naming the column: ``Series_``/``Frame_`` columns
(planes inside a multi-plane file), columns that are neither image, objects nor
``Metadata_`` columns (CellProfiler copies them to per-image measurements), and
a CSV combined with another module that names images.

Not covered: images are declared grayscale, so a colour file is read as one
channel where CellProfiler keeps its colours.
"""

from __future__ import annotations

import csv
import re
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, replace
from pathlib import Path
from typing import ClassVar
from urllib.parse import unquote, urlsplit

from openhcs.core.axes import AxisFamily, ColourAxis
from openhcs.core.config import SourceBindingsConfig
from openhcs.core.runtime_tabular_values import FieldSpec
from openhcs.core.source_bindings import (
    ComponentSelector,
    FromPipelineStart,
    ListedMetadata,
    ListedSourceFile,
    ListedSourceSet,
    MatchedSource,
    NamedSourceBinding,
    PairAsListed,
    PrimaryPlaneRole,
    SourceFileName,
    SourceFilterClause,
    SourceSelector,
    TextContainsRegex,
)
from openhcs.core.source_metadata import SourceMetadataScalar
from openhcs.interop.cellprofiler.module_artifact_declarations import (
    SourceSetupCellProfilerModule,
)
from openhcs.interop.cellprofiler.parser import ModuleBlock
from openhcs.interop.cellprofiler.settings_binder import (
    CellProfilerSettingValue,
    SettingsBinder,
    SettingToKeywordBinding,
    SourceFileSettingBinding,
    parse_cellprofiler_bool,
)
from openhcs.processing.backends.cellprofiler.infrastructure import (
    CellProfilerSourceImageType,
)

_FILE_LOCATION_SETTING = "Input data file location"
_FILE_NAME_SETTING = "Name of the file"

_WELL_ROW_TAGS = frozenset({"wellrow", "well_row", "row"})
_WELL_COLUMN_TAGS = frozenset(
    {"wellcol", "well_col", "wellcolumn", "well_column", "column", "col"}
)
"""CellProfiler's spellings of the metadata tags that hold a well's row and column."""


def _folder_choice(module: ModuleBlock, setting_name: str) -> tuple[str, str]:
    """Split a CellProfiler folder setting into its choice and its written folder."""

    choice, _, folder = module.get_setting(setting_name).partition("|")
    return choice.strip(), folder.strip()


@dataclass(frozen=True, slots=True)
class LoadDataFileBinding(SourceFileSettingBinding):
    """The CSV file LoadData reads, named by a folder setting and a file name."""

    def bind(
        self,
        module: ModuleBlock,
        kwargs: dict[str, CellProfilerSettingValue],
        binder: SettingsBinder,
    ) -> None:
        choice, folder = _folder_choice(module, _FILE_LOCATION_SETTING)
        name = module.get_setting(_FILE_NAME_SETTING).strip()
        if not name or name == "None":
            raise ValueError(
                f"{module.name}({module.module_num}) names no CSV file in "
                f"{_FILE_NAME_SETTING!r}."
            )
        if choice in ("Default Input Folder", "URL"):
            location = name
        elif choice in ("Default Input Folder sub-folder", "Elsewhere..."):
            separator = "\\" if "\\" in folder and "/" not in folder else "/"
            location = folder.rstrip("/\\") + separator + name if folder else name
        else:
            raise ValueError(
                f"{module.name}({module.module_num}) {_FILE_LOCATION_SETTING!r} is "
                f"{choice!r}; the CSV must be in the Default Input Folder (the "
                "pipeline's folder), a sub-folder of it, Elsewhere... or at a URL."
            )
        try:
            kwargs[self.require_parameter_name()] = binder.resolve_source_file(location)
        except FileNotFoundError as error:
            raise FileNotFoundError(
                f"{module.name}({module.module_num}) names its images in the CSV "
                f"file {location!r} ({_FILE_LOCATION_SETTING!r}: {choice!r}, "
                f"{_FILE_NAME_SETTING!r}: {name!r}), looked for from "
                f"{binder.source_root}. {error}"
            ) from error


def _only_yes(
    setting_name: str, parameter_name: str, reason: str
) -> SettingToKeywordBinding:
    """A yes/no setting OpenHCS carries out only when it says yes."""

    def parse(value: str) -> bool:
        if not parse_cellprofiler_bool(value):
            raise ValueError(f"LoadData {setting_name!r}: {value!r} {reason}")
        return True

    return SettingToKeywordBinding(setting_name, parameter_name, parse)


def _base_image_location(value: str) -> str:
    choice = value.partition("|")[0].strip()
    if choice not in (
        "Default Input Folder",
        "Default Output Folder",
        "Default Input Folder sub-folder",
        "Default Output Folder sub-folder",
        "Elsewhere...",
        "None",
    ):
        raise ValueError(f"LoadData 'Base image location' has unknown choice {choice!r}.")
    return choice


def _row_range(value: str) -> tuple[int, int]:
    try:
        first, last = (int(part) for part in value.split(","))
    except ValueError as error:
        raise ValueError(
            f"LoadData 'Rows to process' must be two integers 'first,last', got {value!r}."
        ) from error
    if first < 1 or last < first:
        raise ValueError(
            f"LoadData 'Rows to process' must satisfy 1 <= first <= last, got {value!r}."
        )
    return first, last


def _grouping_tags(value: str) -> tuple[str, ...]:
    return tuple(tag.strip() for tag in value.split(",") if tag.strip())


def _listed_path(folder: str, name: str) -> str:
    """One listed file as ``/``-separated path parts, whatever spelled it.

    CSVs carry Windows paths, ``file:`` and ``http:`` URLs and bare names; only
    the trailing parts identify the file inside a plate.
    """

    text = f"{folder}/{name}" if folder else name
    if re.match(r"[A-Za-z][A-Za-z0-9+.-]*://", text) or text.casefold().startswith("file:"):
        text = unquote(urlsplit(text).path)
    return "/".join(part for part in text.replace("\\", "/").split("/") if part)


def _typed_column(tag: str, values: Sequence[str]) -> tuple[SourceMetadataScalar, ...]:
    """Type one metadata column as CellProfiler does: integer, else float, else text."""

    if tag.casefold() not in _WELL_COLUMN_TAGS:
        for number in (int, float):
            try:
                return tuple(number(value) for value in values)
            except ValueError:
                continue
    return tuple(values)


@dataclass(frozen=True, slots=True)
class _NamedFiles:
    """The CSV columns locating the files of one image or objects name."""

    name: str
    source_type: CellProfilerSourceImageType
    file_column: int | None = None
    folder_column: int | None = None
    url_column: int | None = None

    def listed_path(self, row: Sequence[str]) -> str:
        if self.file_column is not None:
            folder = "" if self.folder_column is None else row[self.folder_column]
            return _listed_path(folder, row[self.file_column])
        if self.url_column is not None:
            return _listed_path("", row[self.url_column])
        raise ValueError(
            f"LoadData needs a FileName_{self.name} or URL_{self.name} column to "
            f"match the PathName_{self.name} column."
        )


_FILE_COLUMN_FIELDS: Mapping[str, tuple[CellProfilerSourceImageType, str]] = {
    "FileName": (CellProfilerSourceImageType.GRAYSCALE, "file_column"),
    "PathName": (CellProfilerSourceImageType.GRAYSCALE, "folder_column"),
    "URL": (CellProfilerSourceImageType.GRAYSCALE, "url_column"),
    "ObjectsFileName": (CellProfilerSourceImageType.OBJECTS, "file_column"),
    "ObjectsPathName": (CellProfilerSourceImageType.OBJECTS, "folder_column"),
    "ObjectsURL": (CellProfilerSourceImageType.OBJECTS, "url_column"),
}
"""CellProfiler's column categories that locate a file, and what each one holds."""

_PLANE_COLUMN_CATEGORIES = frozenset(
    {"Series", "Frame", "Channel", "ObjectsSeries", "ObjectsFrame", "ObjectsChannel"}
)


@dataclass(frozen=True, slots=True)
class LoadDataTable:
    """The image sets one LoadData CSV lists, read once at import."""

    path: Path
    names: tuple[_NamedFiles, ...]
    metadata_columns: Mapping[str, int]
    rows: tuple[tuple[str, ...], ...]

    @classmethod
    def read(cls, path: Path, row_range: tuple[int, int] | None) -> LoadDataTable:
        with path.open(newline="", encoding="utf-8-sig") as handle:
            reader = csv.reader(handle)
            header = [cls._column_name(field) for field in next(reader, ())]
            if not header:
                raise ValueError(f"LoadData CSV file {path} is empty.")
            rows: list[tuple[str, ...]] = []
            for number, row in enumerate(reader, start=1):
                if row_range is not None and not row_range[0] <= number <= row_range[1]:
                    continue
                if not row:
                    continue
                if len(row) < len(header):
                    raise ValueError(
                        f"LoadData CSV file {path} line {number + 1} has {len(row)} "
                        f"values, expected {len(header)}."
                    )
                rows.append(tuple(row[: len(header)]))
        if not rows:
            raise ValueError(f"LoadData CSV file {path} lists no image sets.")

        names: dict[tuple[CellProfilerSourceImageType, str], _NamedFiles] = {}
        metadata_columns: dict[str, int] = {}
        plane_columns: list[str] = []
        other_columns: list[str] = []
        for index, column in enumerate(header):
            category, _, feature = column.partition("_")
            if category in _FILE_COLUMN_FIELDS and feature:
                source_type, field_name = _FILE_COLUMN_FIELDS[category]
                key = (source_type, feature)
                names[key] = replace(
                    names.get(key, _NamedFiles(feature, source_type)),
                    **{field_name: index},
                )
            elif category in _PLANE_COLUMN_CATEGORIES and feature:
                plane_columns.append(column)
            elif category == "Metadata" and feature:
                metadata_columns[feature] = index
            else:
                other_columns.append(column)
        if not names:
            raise ValueError(
                f"LoadData CSV file {path} has no Image_FileName_<Name> or "
                "Image_URL_<Name> column, so it names no image."
            )
        if plane_columns:
            raise ValueError(
                f"LoadData CSV file {path} selects planes inside multi-plane files "
                f"with columns {plane_columns!r}; OpenHCS lists whole files only."
            )
        if other_columns:
            raise ValueError(
                f"LoadData CSV file {path} has columns {other_columns!r} that are "
                "neither image, objects nor Metadata_ columns. CellProfiler copies "
                "them to per-image measurements; OpenHCS carries Metadata_ columns only."
            )
        return cls(path, tuple(names.values()), metadata_columns, tuple(rows))

    @staticmethod
    def _column_name(field: str) -> str:
        """CellProfiler's column name: file columns lose their ``Image_`` prefix."""

        name = field.strip()
        unprefixed = name.removeprefix("Image_")
        return unprefixed if unprefixed.partition("_")[0] in _FILE_COLUMN_FIELDS else name

    def metadata(self) -> Mapping[str, tuple[SourceMetadataScalar, ...]]:
        """Each metadata tag's typed values, one per row; ``Well`` composed if absent."""

        columns: dict[str, tuple[str, ...]] = {
            tag: tuple(row[index] for row in self.rows)
            for tag, index in self.metadata_columns.items()
        }
        folded = {tag.casefold(): tag for tag in columns}
        row_tag = next((folded[tag] for tag in folded if tag in _WELL_ROW_TAGS), None)
        column_tag = next(
            (folded[tag] for tag in folded if tag in _WELL_COLUMN_TAGS), None
        )
        typed = {tag: _typed_column(tag, values) for tag, values in columns.items()}
        if "well" not in folded and row_tag is not None and column_tag is not None:
            typed["Well"] = tuple(
                row + column
                for row, column in zip(columns[row_tag], columns[column_tag], strict=True)
            )
        return typed

    def source_sets(self) -> tuple[ListedSourceSet, ...]:
        metadata = self.metadata()
        return tuple(
            ListedSourceSet(
                files=tuple(
                    ListedSourceFile(alias=named.name, path=named.listed_path(row))
                    for named in self.names
                ),
                metadata=tuple(
                    ListedMetadata(field=tag, value=values[index])
                    for tag, values in metadata.items()
                ),
            )
            for index, row in enumerate(self.rows)
        )

    def bindings(self, first_channel: int) -> tuple[NamedSourceBinding, ...]:
        """One binding per name, selecting exactly the files its column lists."""

        colour_axis = AxisFamily.active().one(ColourAxis)
        bindings: list[NamedSourceBinding] = []
        channel = first_channel
        for named in self.names:
            file_names = dict.fromkeys(
                named.listed_path(row).rpartition("/")[2] for row in self.rows
            )
            binding = named.source_type.binding(
                named.name,
                SourceSelector(
                    filters=(
                        SourceFilterClause(
                            subject=SourceFileName,
                            match_type=TextContainsRegex,
                            value="^(?:" + "|".join(map(re.escape, file_names)) + ")$",
                        ),
                    )
                ),
                FromPipelineStart,
                source_set_role=MatchedSource,
            )
            if named.source_type.projection_role is PrimaryPlaneRole:
                # CellProfiler image names are the colour axis of the active family.
                binding = replace(
                    binding,
                    component_identity=(
                        ComponentSelector(component=colour_axis, value=str(channel)),
                    ),
                )
                channel += 1
            bindings.append(binding)
        return tuple(bindings)


class LoadDataModule(SourceSetupCellProfilerModule):
    module_name = "LoadData"
    validated = True
    supported_revision: ClassVar[int] = 6
    setting_bindings: ClassVar[tuple[SettingToKeywordBinding, ...]] = (
        LoadDataFileBinding(_FILE_NAME_SETTING, "table_path"),
        _only_yes(
            "Load images based on this data?",
            "loads_images",
            "would only attach the CSV's columns to image sets other modules "
            "build, which OpenHCS does not do.",
        ),
        SettingToKeywordBinding(
            "Base image location", "base_image_location", _base_image_location
        ),
        SettingToKeywordBinding(
            "Process just a range of rows?", "wants_rows", parse_cellprofiler_bool
        ),
        SettingToKeywordBinding("Rows to process", "row_range", _row_range),
        SettingToKeywordBinding(
            "Group images by metadata?", "wants_groups", parse_cellprofiler_bool
        ),
        SettingToKeywordBinding(
            "Select metadata tags for grouping", "grouping_tags", _grouping_tags
        ),
        _only_yes(
            "Rescale intensities?",
            "rescales_intensities",
            "would scale by the file format's maximum instead of the image's "
            "own metadata; OpenHCS scales every source image one way.",
        ),
    )

    @classmethod
    def contribute_source_bindings(
        cls,
        module: ModuleBlock,
        config: SourceBindingsConfig,
        binder: SettingsBinder,
    ) -> SourceBindingsConfig:
        if module.variable_revision_number != cls.supported_revision:
            raise ValueError(
                f"{module.name}({module.module_num}) is written at settings revision "
                f"{module.variable_revision_number}; OpenHCS reads revision "
                f"{cls.supported_revision} (CellProfiler 4). Re-save the pipeline "
                "in CellProfiler 4."
            )
        if config.binding_declarations:
            raise ValueError(
                f"{module.name}({module.module_num}) lists complete image sets, so it "
                "cannot be combined with other modules that name images; the "
                "pipeline already names "
                f"{tuple(binding.alias for binding in config.binding_declarations)!r}."
            )
        settings = binder.bind_declared(module, cls.setting_bindings)
        table_path = settings["table_path"]
        row_range = settings.get("row_range") if settings.get("wants_rows") else None
        if not isinstance(table_path, Path):
            raise TypeError("LoadData CSV file did not resolve to a path.")
        if row_range is not None and not isinstance(row_range, tuple):
            raise TypeError("LoadData row range did not parse to a pair.")
        table = LoadDataTable.read(table_path, row_range)

        metadata = table.metadata()
        grouping_fields = config.grouping_metadata_fields
        if settings.get("wants_groups"):
            grouping_tags = settings.get("grouping_tags", ())
            if not isinstance(grouping_tags, tuple):
                raise TypeError("LoadData grouping tags did not parse to a tuple.")
            unknown = tuple(tag for tag in grouping_tags if tag not in metadata)
            if unknown or not grouping_tags:
                raise ValueError(
                    f"{module.name}({module.module_num}) groups image sets by "
                    f"metadata tags {grouping_tags!r}, but the CSV file "
                    f"{table.path} has only {tuple(metadata)!r} "
                    "(its Metadata_ columns)."
                )
            grouping_fields = tuple(str(tag) for tag in grouping_tags)
        return replace(
            config,
            bindings=table.bindings(first_channel=1),
            match_plan=PairAsListed(source_sets=table.source_sets()),
            metadata_fields=FieldSpec.merge_exact(
                (
                    config.metadata_fields,
                    tuple(
                        FieldSpec(tag, type(values[0]), required=False)
                        for tag, values in metadata.items()
                    ),
                ),
                context="CellProfiler LoadData metadata columns",
            ),
            grouping_metadata_fields=grouping_fields,
        )
