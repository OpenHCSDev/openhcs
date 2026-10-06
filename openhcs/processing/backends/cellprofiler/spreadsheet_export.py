"""CellProfiler-compatible spreadsheet projection over runtime artifacts."""

from __future__ import annotations

import re
import statistics
from collections import OrderedDict
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, replace
from enum import Enum
from numbers import Real
from pathlib import Path, PurePosixPath
from typing import cast, TYPE_CHECKING, ClassVar, TypeVar

import numpy as np

from openhcs.core._tabular_native import render_csv as _render_native_csv
from openhcs.core.artifacts import (
    ArtifactInputPlan,
    ArtifactSpec,
    ArtifactSpecCollection,
    ArtifactType,
    MeasurementBearingArtifactType,
    RelationshipsArtifactType,
    SpecialArtifactType,
)
from openhcs.core.callable_contract import FunctionStepExecutionScope
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.equivalence import (
    measurement_qualifier_field_names,
)
from openhcs.core.measurement_row_materialization import (
    MeasurementSparseColumnarRows,
    MEASUREMENT_SPARSE_CELL,
    is_structural_missing_measurement_cell,
    MeasurementRowsAxisProjection,
    WideMeasurementRowAccumulator,
)
from openhcs.core.pipeline.function_contracts import (
    execution_scope,
    runtime_bound_parameters,
)
from openhcs.core.runtime_tabular_values import (
    ColumnarRows,
    FieldSpec,
)
from openhcs.core.runtime_measurements import (
    MeasurementRowAxisField,
    MeasurementScope,
    MeasurementSubject,
    measurement_axis_integer_value,
)
from openhcs.core.runtime_identifier import (
    normalize_runtime_identifier,
)
from openhcs.core.runtime_stores import RuntimeArtifactBatch, StoredRuntimeValue
from openhcs.core.runtime_measurements import (
    MeasurementTable,
)
from openhcs.core.runtime_relationships import (
    ObjectRelationship,
)
from openhcs.core.source_image_provenance import (
    source_component_metadata_consensus,
)
from openhcs.interop.cellprofiler.database_column_dialect import (
    CellProfilerDatabaseColumnDialect,
)
from openhcs.interop.cellprofiler.image_set_numbering import (
    CellProfilerImageSetNumbering,
)
from openhcs.interop.cellprofiler.module_settings import (
    BoundModuleSettings,
)
from openhcs.interop.cellprofiler.module_artifact_declarations import (
    ArtifactExportModule,
)
from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.interop.cellprofiler.measurement_dialect import (
    CELLPROFILER_MEASUREMENT_DIALECT,
)
from openhcs.interop.cellprofiler.parser import ModuleBlock
from openhcs.interop.cellprofiler.setting_names import (
    SettingNameFamily,
    block_setting_value,
    is_blank_symbol_name,
    repeating_setting_blocks,
)
from openhcs.interop.cellprofiler.settings_binder import (
    SettingToKeywordBinding,
    parse_cellprofiler_bool,
)
from openhcs.processing.materialization import (
    CsvOptions,
    FileBundleOptions,
    MaterializationSpec,
    WriteMode,
)

from openhcs.processing.materialization.core import ColumnarCsvOutput

if TYPE_CHECKING:
    from openhcs.core.function_patterns import FunctionInvocationKey
    from openhcs.core.invocation_artifacts import ArtifactDeclarationStepContext


_METADATA_TEMPLATE = re.compile(r"\{(?P<name>[A-Za-z_][A-Za-z0-9_]*)\}")
_CELLPROFILER_METADATA_TEMPLATE = re.compile(r"\\g<(?P<name>[A-Za-z_][A-Za-z0-9_]*)>")
_EnumT = TypeVar("_EnumT", bound=Enum)


class SpreadsheetDelimiter(str, Enum):
    """Supported CellProfiler spreadsheet delimiters."""

    COMMA = ","
    TAB = "\t"

    @classmethod
    def from_cellprofiler(cls, value: str) -> "SpreadsheetDelimiter":
        """Parse one CellProfiler delimiter setting."""

        normalized = value.strip().casefold()
        if normalized in {'comma (",")', "comma", ","}:
            return cls.COMMA
        if normalized in {"tab", "\\t"}:
            return cls.TAB
        raise ValueError(f"Unsupported spreadsheet delimiter {value!r}.")

    @property
    def default_suffix(self) -> str:
        """Return the conventional suffix for this delimiter."""

        return ".csv" if self is SpreadsheetDelimiter.COMMA else ".txt"


class SpreadsheetNanRepresentation(str, Enum):
    """How non-finite numeric values appear in spreadsheet cells."""

    NAN = "nan"
    NULL = "null"

    @classmethod
    def from_cellprofiler(cls, value: str) -> "SpreadsheetNanRepresentation":
        """Parse one CellProfiler NaN/Inf representation setting."""

        normalized = value.strip().casefold()
        if normalized == "nan":
            return cls.NAN
        if normalized in {"null", "nulls"}:
            return cls.NULL
        raise ValueError(f"Unsupported spreadsheet NaN representation {value!r}.")


class CellProfilerSpreadsheetRowField(str, Enum):
    """CellProfiler-owned spreadsheet row fields."""

    IMAGE_NUMBER = "image_number"


@dataclass(frozen=True, slots=True)
class SpreadsheetColumnSelection:
    """One CellProfiler subject/measurement column selection."""

    subject: str
    feature: str

    def __post_init__(self) -> None:
        if not self.subject.strip() or not self.feature.strip():
            raise ValueError(
                "SpreadsheetColumnSelection subject and feature must be non-empty."
            )

    @classmethod
    def from_cellprofiler(
        cls,
        value: str,
    ) -> tuple["SpreadsheetColumnSelection", ...]:
        """Parse CellProfiler's comma-separated ``subject|feature`` value."""

        selections: list[SpreadsheetColumnSelection] = []
        for token in value.split(","):
            token = token.strip()
            if not token:
                continue
            parts = tuple(part.strip() for part in token.split("|", 1))
            if len(parts) != 2:
                raise ValueError(
                    "Spreadsheet measurement selections must use "
                    f"'subject|feature', got {token!r}."
                )
            subject, feature = parts
            if subject.casefold() == "none" and feature.casefold() == "none":
                continue
            selections.append(cls(subject, feature))
        return tuple(selections)

    def matches(self, subject: str, feature: str) -> bool:
        """Return whether this selection addresses one projected column."""

        return normalize_runtime_identifier(
            self.subject
        ) == normalize_runtime_identifier(subject) and normalize_runtime_identifier(
            self.feature
        ) == normalize_runtime_identifier(
            feature
        )


@dataclass(frozen=True, slots=True)
class SpreadsheetFileSelection:
    """One output file and the measurement subjects rendered into it."""

    subjects: tuple[str, ...]
    file_name: str

    def __post_init__(self) -> None:
        subjects = tuple(dict.fromkeys(subject.strip() for subject in self.subjects))
        if not subjects or any(not subject for subject in subjects):
            raise ValueError(
                "SpreadsheetFileSelection.subjects must contain non-empty names."
            )
        file_name = self.file_name.strip()
        if not file_name:
            raise ValueError("SpreadsheetFileSelection.file_name cannot be empty.")
        object.__setattr__(self, "subjects", subjects)
        object.__setattr__(self, "file_name", file_name)

    def combined_rows(
        self,
        selected_tables: tuple[tuple[str, ColumnarRows], ...],
    ) -> ColumnarRows:
        if len(selected_tables) == 1:
            return selected_tables[0][1]
        image_field = CellProfilerSpreadsheetRowField.IMAGE_NUMBER.value
        grouped: list[tuple[str, ColumnarRows, OrderedDict[object, list[int]]]] = []
        image_counts: OrderedDict[object, int] = OrderedDict()
        for subject, rows in selected_tables:
            rows_by_image: OrderedDict[object, list[int]] = OrderedDict()
            if image_field not in rows.columns and len(rows):
                raise ValueError(
                    "Combined spreadsheet subjects require a producer-declared "
                    f"{image_field!r} on every {subject!r} row."
                )
            image_numbers = (
                rows.column_values(image_field) if image_field in rows.columns else ()
            )
            for index, image_number in enumerate(image_numbers):
                if is_structural_missing_measurement_cell(image_number):
                    raise ValueError(
                        "Combined spreadsheet subjects require a producer-declared "
                        f"{image_field!r} on every {subject!r} row."
                    )
                indexes = rows_by_image.setdefault(image_number, [])
                indexes.append(index)
                image_counts[image_number] = max(
                    image_counts.get(image_number, 0), len(indexes)
                )
            grouped.append((subject, rows, rows_by_image))

        offsets: dict[object, int] = {}
        image_values: list[object] = []
        for image_number, count in image_counts.items():
            offsets[image_number] = len(image_values)
            image_values.extend([image_number] * count)
        columns: dict[str, np.ndarray] = {}
        if image_values:
            columns[image_field] = ColumnarRows.column_array(image_values)
        for subject, rows, rows_by_image in grouped:
            source_indexes = np.asarray(
                [index for indexes in rows_by_image.values() for index in indexes],
                dtype=np.intp,
            )
            target_indexes = np.asarray(
                [
                    offsets[image_number] + ordinal
                    for image_number, indexes in rows_by_image.items()
                    for ordinal in range(len(indexes))
                ],
                dtype=np.intp,
            )
            for field_name in rows.columns:
                if field_name == image_field:
                    continue
                values = ColumnarRows.column_array(rows.column_values(field_name))[
                    source_indexes
                ]
                present = np.fromiter(
                    (not is_structural_missing_measurement_cell(value) for value in values),
                    dtype=bool,
                    count=len(values),
                )
                if not np.any(present):
                    continue
                name = f"{subject}_{field_name}"
                if name not in columns:
                    columns[name] = np.empty(len(image_values), dtype=object)
                    columns[name].fill(MEASUREMENT_SPARSE_CELL)
                columns[name][target_indexes[present]] = values[present]
        # Native headers follow the first row where a field is present, then
        # the declared subject/field order within that row.
        names = tuple(
            sorted(
                columns,
                key=lambda name: next(
                    index
                    for index, value in enumerate(columns[name])
                    if not is_structural_missing_measurement_cell(value)
                ),
            )
        )
        return MeasurementSparseColumnarRows(
            {name: columns[name] for name in names},
            fields=tuple(FieldSpec(name, required=False) for name in names),
        )

    def header_rows(
        self, rows: ColumnarRows, *, active_subjects: tuple[str, ...],
    ) -> tuple[tuple[str, ...], ...]:
        """Derive native headers in their existing first-present field order."""
        return self.csv_schema(
            tuple(rows.iter_row_mappings()), active_subjects=active_subjects,
        )[1]

    def csv_schema(
        self, row_mappings: Sequence[Mapping[str, object]], *,
        active_subjects: tuple[str, ...],
    ) -> tuple[tuple[str, ...], tuple[tuple[str, ...], ...]]:
        """Own both physical column order and contextual header projection."""
        columns = tuple(
            dict.fromkeys(field_name for row in row_mappings for field_name in row)
        )
        header_rows = (columns,)
        if len(active_subjects) > 1:
            bindings = []
            subjects = sorted(active_subjects, key=len, reverse=True)
            image_field = CellProfilerSpreadsheetRowField.IMAGE_NUMBER.value
            for name in columns:
                if name == image_field:
                    bindings.append(("Image", name))
                    continue
                subject = next(
                    (subject for subject in subjects if name.startswith(f"{subject}_")),
                    None,
                )
                if subject is None:
                    raise ValueError(
                        f"Combined spreadsheet column {name!r} has no declared subject."
                    )
                bindings.append((subject, name[len(subject) + 1 :]))
            header_rows = tuple(zip(*bindings))
        return columns, header_rows

    def prepare_csv(
        self,
        rows: ColumnarRows,
        *,
        active_subjects: tuple[str, ...],
        delimiter: SpreadsheetDelimiter,
        nan_representation: SpreadsheetNanRepresentation,
    ) -> ColumnarCsvOutput:
        """Retain correlated rows and declared formatting until materialization."""
        return ColumnarCsvOutput(
            path=self.file_name,
            content=rows,
            options=CellProfilerSpreadsheetCsvOptions(
                selection=self,
                active_subjects=active_subjects,
                delimiter=delimiter,
                nan_representation=nan_representation,
            ),
        )

    def render_csv(
        self,
        rows: ColumnarRows,
        *,
        active_subjects: tuple[str, ...],
        delimiter: SpreadsheetDelimiter,
        nan_representation: SpreadsheetNanRepresentation,
    ) -> str:
        """Realized view of this selection's canonical typed CSV output."""
        output = self.prepare_csv(
            rows, active_subjects=active_subjects, delimiter=delimiter,
            nan_representation=nan_representation,
        )
        return output.options.render(output.content)


@dataclass(frozen=True, kw_only=True)
class CellProfilerSpreadsheetCsvOptions(CsvOptions):
    """CellProfiler CSV dialect and header semantics on the writer-option family."""

    selection: SpreadsheetFileSelection
    active_subjects: tuple[str, ...]
    delimiter: SpreadsheetDelimiter
    nan_representation: SpreadsheetNanRepresentation

    def header_rows(self, rows: ColumnarRows) -> tuple[tuple[str, ...], ...]:
        return self.selection.header_rows(rows, active_subjects=self.active_subjects)

    def render(self, data: ColumnarRows) -> str:
        row_mappings = tuple(data.iter_row_mappings())
        columns, headers = self.selection.csv_schema(
            row_mappings, active_subjects=self.active_subjects,
        )
        return _render_native_csv(
            row_mappings, columns, self.delimiter.value, Real,
            self.nan_representation is SpreadsheetNanRepresentation.NULL, headers,
        )


def cellprofiler_metadata_template(value: str) -> str:
    """Translate CellProfiler metadata references into a public string template."""

    return _CELLPROFILER_METADATA_TEMPLATE.sub(
        lambda match: "{" + match.group("name") + "}",
        value.strip(),
    )


def cellprofiler_output_directory(value: str) -> str:
    """Parse a CellProfiler output-folder setting as a relative bundle directory."""

    location, separator, relative = value.partition("|")
    if not separator:
        raise ValueError(
            "Spreadsheet output location must contain a CellProfiler folder choice."
        )
    if location.strip().casefold() not in {
        "default output folder",
        "default output folder sub-folder",
    }:
        raise ValueError(
            "Spreadsheet export supports only Default Output Folder locations, got "
            f"{location!r}."
        )
    normalized = cellprofiler_metadata_template(relative).replace("\\", "/")
    if normalized in {"", "."}:
        return ""
    return normalized.strip("/")


def prepare_spreadsheet_bundle(
    artifact_batch: RuntimeArtifactBatch,
    *,
    delimiter: SpreadsheetDelimiter = SpreadsheetDelimiter.COMMA,
    add_image_metadata: bool = False,
    add_image_file_names: bool = False,
    select_measurements: bool = False,
    selected_columns: tuple[SpreadsheetColumnSelection, ...] = (),
    calculate_aggregate_means: bool = False,
    calculate_aggregate_medians: bool = False,
    calculate_aggregate_standard_deviations: bool = False,
    output_directory: str = "",
    export_all_measurement_types: bool = True,
    file_selections: tuple[SpreadsheetFileSelection, ...] = (),
    nan_representation: SpreadsheetNanRepresentation = (
        SpreadsheetNanRepresentation.NAN
    ),
    add_filename_prefix: bool = True,
    filename_prefix: str = "MyExpt_",
    context: ProcessingContext | None = None,
) -> dict[str, ColumnarCsvOutput]:
    """Prepare exactly the measurement records selected by ``artifact_batch``."""

    if not isinstance(artifact_batch, RuntimeArtifactBatch):
        raise TypeError("artifact_batch must be RuntimeArtifactBatch.")
    delimiter = _coerce_enum(SpreadsheetDelimiter, delimiter)
    nan_representation = _coerce_enum(
        SpreadsheetNanRepresentation,
        nan_representation,
    )
    selected_columns = tuple(selected_columns)
    if any(
        not isinstance(selection, SpreadsheetColumnSelection)
        for selection in selected_columns
    ):
        raise TypeError(
            "selected_columns must contain SpreadsheetColumnSelection values."
        )
    file_selections = tuple(file_selections)
    if any(
        not isinstance(selection, SpreadsheetFileSelection)
        for selection in file_selections
    ):
        raise TypeError("file_selections must contain SpreadsheetFileSelection values.")

    image_numbers = CellProfilerImageSetNumbering(
        artifact_batch.source_image_set_identity_policy
    )
    tables, object_subjects = _measurement_tables(
        artifact_batch,
        image_numbers,
        add_image_metadata=add_image_metadata,
        add_image_file_names=add_image_file_names,
    )
    relationship_rows = _relationship_rows(artifact_batch, image_numbers)
    if relationship_rows:
        tables["Object relationships"] = relationship_rows
    source_image_rows = tables.get(
        "Image", MeasurementSparseColumnarRows({}, fields=())
    )

    tables = _selected_table_columns(
        tables,
        selected_columns=selected_columns,
        enabled=bool(select_measurements),
    )
    tables = _with_requested_aggregates(
        tables,
        object_subjects=object_subjects,
        mean=bool(calculate_aggregate_means),
        median=bool(calculate_aggregate_medians),
        standard_deviation=bool(calculate_aggregate_standard_deviations),
    )
    tables = _with_image_columns_on_objects(
        tables,
        object_subjects=object_subjects,
        image_rows=source_image_rows,
        add_metadata=bool(add_image_metadata),
        add_file_names=bool(add_image_file_names),
    )

    selections = (
        _automatic_file_selections(tables, delimiter)
        if export_all_measurement_types
        else file_selections
    )
    prefix = filename_prefix if add_filename_prefix else ""
    bundle: dict[str, ColumnarCsvOutput] = {}
    for selection in selections:
        selected_tables = tuple(
            (subject, tables[subject])
            for subject in selection.subjects
            if subject in tables
        )
        if not selected_tables:
            continue
        rows = selection.combined_rows(selected_tables)
        path_template = _bundle_path_template(
            output_directory=output_directory,
            prefix=prefix,
            file_name=selection.file_name,
        )
        for relative_path, selected_rows in _rows_by_resolved_path(
            path_template,
            rows,
            image_rows=source_image_rows,
        ):
            if relative_path in bundle:
                raise ValueError(
                    f"Spreadsheet export produced duplicate path {relative_path!r}."
                )
            bundle[relative_path] = selection.prepare_csv(
                selected_rows,
                active_subjects=tuple(subject for subject, _ in selected_tables),
                delimiter=delimiter,
                nan_representation=nan_representation,
            )
    if context is not None:
        image_numbers.observe_export_paths(context, tuple(bundle))
    return bundle


def render_spreadsheet_bundle(
    artifact_batch: RuntimeArtifactBatch, **kwargs: object,
) -> dict[str, str | bytes]:
    """Realized view of the canonical schema-bearing spreadsheet bundle."""
    return {
        path: output.options.render(output.content)
        for path, output in prepare_spreadsheet_bundle(artifact_batch, **kwargs).items()
    }


def _measurement_tables(
    artifact_batch: RuntimeArtifactBatch,
    image_numbers: CellProfilerImageSetNumbering,
    *,
    add_image_metadata: bool,
    add_image_file_names: bool,
) -> tuple[
    OrderedDict[str, ColumnarRows],
    tuple[str, ...],
]:
    accumulator = WideMeasurementRowAccumulator(
        CELLPROFILER_MEASUREMENT_DIALECT.row_identity_contract
    )
    source_metadata_by_image_number: OrderedDict[
        int,
        list[tuple[Mapping[str, object], Mapping[str, object]]],
    ] = OrderedDict()
    all_tables: list[MeasurementTable] = []
    for spec in artifact_batch.input_specs:
        if not issubclass(spec.artifact_type, MeasurementBearingArtifactType):
            continue
        records_by_axis = artifact_batch.records(spec.ref())
        records = tuple(
            record
            for axis_records in records_by_axis.values()
            for record in axis_records
        )
        record_tables = tuple(
            (record, table)
            for record in records
            for table in spec.artifact_type.measurement_tables(
                record, CELLPROFILER_MEASUREMENT_DIALECT
            )
        )
        tables = tuple(table for _record, table in record_tables)
        all_tables.extend(tables)
        slice_axis = MeasurementRowAxisField.SLICE_INDEX
        MeasurementTable.shared_row_axis_domain(spec.name, tables, slice_axis)
        for record, table in record_tables:
            image_numbers_by_slice = image_numbers.for_source_slices(
                scope=record.key.scope,
                provenance=table.source_provenance,
                slice_indices=image_numbers.source_slices_for_measurement_table(table),
                owner=table.name,
            )
            accumulator.add_declared_rows(
                image_numbers.project_measurement_rows(
                    scope=record.key.scope,
                    table=table,
                ),
                CELLPROFILER_MEASUREMENT_DIALECT,
                default_subject=_measurement_subject_name(table),
                default_scope=table.subject.scope,
                source_image_name=table.source_image_name,
                object_id_field=table.subject.object_id_field,
                qualifier_field_names=measurement_qualifier_field_names(
                    CELLPROFILER_MEASUREMENT_DIALECT
                ),
            )
            for (
                image_number,
                original_metadata,
                acquisition,
                file_values,
            ) in _source_metadata_measurement_rows(
                table,
                image_numbers_by_slice,
                add_image_metadata=add_image_metadata,
                add_image_file_names=add_image_file_names,
            ):
                source_metadata_by_image_number.setdefault(
                    image_number,
                    [],
                ).append((original_metadata, acquisition))
                if file_values:
                    accumulator.add_declared_rows(
                        MeasurementSparseColumnarRows.from_rows(
                            ({slice_axis.value: image_number, **file_values},),
                            fields=(
                                FieldSpec(slice_axis.value, int),
                                *(
                                    FieldSpec(name, str, required=False)
                                    for name in file_values
                                ),
                            ),
                        ),
                        CELLPROFILER_MEASUREMENT_DIALECT,
                        default_subject="Image",
                        default_scope=MeasurementScope.IMAGE,
                    )
    for table in CellProfilerModule.derive_experiment_measurement_tables(all_tables):
        accumulator.add_declared_rows(
            table.rows,
            CELLPROFILER_MEASUREMENT_DIALECT,
            default_subject=_measurement_subject_name(table),
            default_scope=table.subject.scope,
            source_image_name=table.source_image_name,
            object_id_field=table.subject.object_id_field,
            qualifier_field_names=measurement_qualifier_field_names(
                CELLPROFILER_MEASUREMENT_DIALECT
            ),
        )
    source_metadata_rows = tuple(
        {
            MeasurementRowAxisField.SLICE_INDEX.value: image_number,
            **{
                f"Metadata_{field_name}": value
                for field_name, value in consensus.items()
            },
        }
        for image_number, metadata_rows in source_metadata_by_image_number.items()
        for consensus in (_source_metadata_consensus(metadata_rows),)
        if consensus is not None
    )
    if source_metadata_rows:
        metadata_field_names = tuple(
            dict.fromkeys(
                field_name
                for row in source_metadata_rows
                for field_name in row
                if field_name != MeasurementRowAxisField.SLICE_INDEX.value
            )
        )
        accumulator.add_declared_rows(
            MeasurementSparseColumnarRows.from_rows(
                source_metadata_rows,
                fields=(
                    FieldSpec(MeasurementRowAxisField.SLICE_INDEX.value, int),
                    *(
                        FieldSpec(field_name, str, required=False)
                        for field_name in metadata_field_names
                    ),
                ),
            ),
            CELLPROFILER_MEASUREMENT_DIALECT,
            default_subject="Image",
            default_scope=MeasurementScope.IMAGE,
        )
    return (
        OrderedDict(
            (subject, _cellprofiler_rows(rows))
            for subject, rows in accumulator.columnar_rows_by_subject().items()
        ),
        accumulator.object_subjects(),
    )


def _source_metadata_consensus(
    rows: Sequence[tuple[Mapping[str, object], Mapping[str, object]]],
) -> Mapping[str, object] | None:
    """Fold each existing source role without treating absent extraction as data.

    Original fields previously participated only when extraction existed.
    Preserve that rule while independently folding requested acquisition facts;
    original spelling/values remain authoritative when namespaces overlap.
    """
    original = source_component_metadata_consensus(
        tuple(row[0] for row in rows if row[0])
    )
    acquisition = source_component_metadata_consensus(tuple(row[1] for row in rows))
    if original is None and acquisition is None:
        return None
    return {**(acquisition or {}), **(original or {})}


def _source_metadata_measurement_rows(
    table: MeasurementTable,
    image_numbers_by_slice: Mapping[int, int],
    *,
    add_image_metadata: bool,
    add_image_file_names: bool,
) -> tuple[
    tuple[int, Mapping[str, object], Mapping[str, object], Mapping[str, str]], ...
]:
    """Project producer-owned source metadata into CellProfiler Image rows."""

    rows: list[
        tuple[int, Mapping[str, object], Mapping[str, object], Mapping[str, str]]
    ] = []
    dialect = CellProfilerDatabaseColumnDialect()
    image_subject = MeasurementSubject(MeasurementScope.IMAGE, "Image")
    for slice_index in image_numbers_by_slice:
        provenance = table.source_provenance.for_source_plane(slice_index)
        metadata = dialect.source_metadata_values(
            provenance.source_component_metadata,
            None,
        )
        acquisition = {}
        if add_image_metadata:
            acquisition.update(
                dialect.source_acquisition_values(provenance.source_component_metadata)
            )
            acquisition.update(
                dialect.source_metadata_values(
                    None,
                    Path(provenance.source_path)
                    if provenance.source_path is not None else None,
                )
            )
        file_values: dict[str, str] = {}
        for name in (
            provenance.represented_source_image_names if add_image_file_names else ()
        ):
            named_source = provenance.for_source_image(name)
            if named_source.source_path is None:
                continue
            file_values.update(
                (
                    dialect.source_measurement_field(
                        image_subject, FieldSpec(field, str)
                    ).name,
                    value,
                )
                for field, value in dialect.source_image_file_values(
                    Path(named_source.source_path),
                    name,
                ).items()
            )
        if metadata or acquisition or file_values:
            rows.append(
                (image_numbers_by_slice[slice_index], metadata, acquisition, file_values)
            )
    return tuple(rows)


def _relationship_rows(
    artifact_batch: RuntimeArtifactBatch,
    image_numbers: CellProfilerImageSetNumbering,
) -> ColumnarRows:
    rows: list[Mapping[str, object]] = []
    for record in _records_in_contract_order(
        artifact_batch,
        RelationshipsArtifactType,
    ):
        relationship = cast(ObjectRelationship, record.data)
        image_numbers_by_slice = image_numbers.for_source_slices(
            scope=record.key.scope,
            provenance=relationship.source_provenance,
            slice_indices=relationship.payload.slice_indices,
            owner=relationship.name,
        )
        rows.extend(
            MeasurementRowsAxisProjection.from_rows(
                relationship.row_mappings()
            ).remap_runtime_slice_indices(image_numbers_by_slice)
        )
    names = tuple(dict.fromkeys(name for row in rows for name in row))
    # Relationship rows are separate edges, not sparse fragments to coalesce.
    return _cellprofiler_rows(
        MeasurementSparseColumnarRows(
            {
                name: tuple(row.get(name, MEASUREMENT_SPARSE_CELL) for row in rows)
                for name in names
            },
            fields=tuple(FieldSpec(name, required=False) for name in names),
        )
    )


def _cellprofiler_rows(rows: ColumnarRows) -> ColumnarRows:
    """Project declared image coordinates once while retaining sparse columns."""
    slice_field = MeasurementRowAxisField.SLICE_INDEX.value
    image_field = CellProfilerSpreadsheetRowField.IMAGE_NUMBER.value
    if slice_field not in rows.columns:
        return rows
    source_values = rows.column_values(slice_field)
    values = np.empty(len(source_values), dtype=object)
    for index, value in enumerate(source_values):
        if is_structural_missing_measurement_cell(value):
            values[index] = value
            continue
        number = measurement_axis_integer_value(
            value, MeasurementRowAxisField.SLICE_INDEX
        )
        if number is None:
            raise ValueError(
                "CellProfiler spreadsheet export requires an integer "
                f"{slice_field!r}, got {value!r}."
            )
        values[index] = number
    return MeasurementSparseColumnarRows(
        {
            image_field if name == slice_field else name: (
                values if name == slice_field else rows.column_values(name)
            )
            for name in rows.columns
        },
        fields=tuple(
            replace(field, name=image_field) if field.name == slice_field else field
            for field in rows.fields
        ),
        object_row_identity=rows.object_row_identity,
    )


def _records_in_contract_order(
    artifact_batch: RuntimeArtifactBatch,
    artifact_type: type[ArtifactType],
) -> tuple[StoredRuntimeValue, ...]:
    return tuple(
        record
        for spec in artifact_batch.specs_of_type(artifact_type)
        for records in artifact_batch.records(spec.ref()).values()
        for record in records
    )


def _measurement_subject_name(table: MeasurementTable) -> str:
    subject = table.subject
    if subject is None:
        return table.name
    if subject.scope is MeasurementScope.IMAGE:
        return "Image"
    if subject.scope is MeasurementScope.EXPERIMENT:
        return "Experiment"
    if subject.scope is MeasurementScope.OBJECT:
        if subject.name is None:
            raise ValueError(f"Object measurement table {table.name!r} has no subject.")
        return subject.name
    return subject.name or table.name


def _selected_table_columns(
    tables: OrderedDict[str, ColumnarRows],
    *,
    selected_columns: tuple[SpreadsheetColumnSelection, ...],
    enabled: bool,
) -> OrderedDict[str, ColumnarRows]:
    if not enabled:
        return tables
    axis_fields = (
        *MeasurementRowAxisField.field_names(),
        CellProfilerSpreadsheetRowField.IMAGE_NUMBER.value,
    )
    selected = OrderedDict()
    for subject, rows in tables.items():
        fields = tuple(
            field
            for field in rows.fields
            if subject == "Object relationships"
            or field.name in axis_fields
            or any(
                selection.matches(subject, field.name) for selection in selected_columns
            )
        )
        selected[subject] = MeasurementSparseColumnarRows(
            {field.name: rows.column_values(field.name) for field in fields},
            fields=fields,
            object_row_identity=rows.object_row_identity,
        )
    return selected


def _with_requested_aggregates(
    tables: OrderedDict[str, ColumnarRows],
    *,
    object_subjects: tuple[str, ...],
    mean: bool,
    median: bool,
    standard_deviation: bool,
) -> OrderedDict[str, ColumnarRows]:
    if not (mean or median or standard_deviation):
        return tables
    image_field = CellProfilerSpreadsheetRowField.IMAGE_NUMBER.value
    image = tables.get("Image")
    image_numbers = (
        ()
        if image is None or image_field not in image.columns
        else image.column_values(image_field)
    )
    image_indexes = {
        value: index
        for index, value in enumerate(image_numbers)
        if not is_structural_missing_measurement_cell(value)
    }
    columns = (
        {}
        if image is None
        else {
            name: ColumnarRows.column_array(image.column_values(name)).astype(
                object, copy=True
            )
            for name in image.columns
        }
    )
    fields = [] if image is None else list(image.fields)
    for subject in object_subjects:
        rows = tables.get(subject)
        if rows is None:
            continue
        if image_field not in rows.columns:
            raise ValueError(
                f"Object measurement aggregation requires image_number in every {subject!r} row."
            )
        groups: OrderedDict[object, list[int]] = OrderedDict()
        for index, number in enumerate(rows.column_values(image_field)):
            if is_structural_missing_measurement_cell(number):
                raise ValueError(
                    f"Object measurement aggregation requires image_number in every {subject!r} row."
                )
            groups.setdefault(number, []).append(index)
        for number, indexes in groups.items():
            image_index = image_indexes.get(number)
            if image_index is None:
                raise ValueError(
                    "Object measurement aggregation requires a producer-declared "
                    f"Image measurement row for {image_field}={number!r}."
                )
            for feature, values in _numeric_features(
                rows, np.asarray(indexes, dtype=np.intp)
            ):
                for prefix, enabled, calculate in (
                    ("Mean", mean, statistics.fmean),
                    ("Median", median, statistics.median),
                    ("StDev", standard_deviation, statistics.pstdev),
                ):
                    if not enabled:
                        continue
                    name = f"{prefix}_{subject}_{feature}"
                    if name not in columns:
                        columns[name] = np.full(
                            len(image_numbers),
                            MEASUREMENT_SPARSE_CELL,
                            dtype=object,
                        )
                        fields.append(FieldSpec(name, required=False))
                    # Retain the existing statistics owner and float-cell semantics.
                    columns[name][image_index] = calculate(
                        float(value) for value in values
                    )
    updated = OrderedDict(tables)
    updated["Image"] = MeasurementSparseColumnarRows(columns, fields=tuple(fields))
    return updated


def _numeric_features(
    rows: ColumnarRows,
    indexes: np.ndarray,
) -> tuple[tuple[str, np.ndarray], ...]:
    """Derive numerical columns in first-present-cell order for one image."""
    axis_fields = frozenset(
        (
            *MeasurementRowAxisField.field_names(),
            CellProfilerSpreadsheetRowField.IMAGE_NUMBER.value,
        )
    )
    features = []
    for position, name in enumerate(rows.columns):
        if name in axis_fields:
            continue
        values = ColumnarRows.column_array(rows.column_values(name))[indexes]
        if values.dtype.hasobject:
            present = np.fromiter(
                (not is_structural_missing_measurement_cell(value) for value in values),
                dtype=bool,
                count=len(values),
            )
            locations = np.flatnonzero(present)
            if not len(locations):
                continue
            first = int(locations[0])
            values = values[present]
            if not all(
                isinstance(value, Real) and not isinstance(value, bool)
                for value in values
            ):
                continue
        else:
            if not len(values) or values.dtype.kind not in "iuf":
                continue
            first = 0
        features.append((first, position, name, values))
    return tuple(
        (name, values)
        for _first, _position, name, values in sorted(
            features, key=lambda value: value[:2]
        )
    )


def _with_image_columns_on_objects(
    tables: OrderedDict[str, ColumnarRows],
    *,
    object_subjects: tuple[str, ...],
    image_rows: ColumnarRows,
    add_metadata: bool,
    add_file_names: bool,
) -> OrderedDict[str, ColumnarRows]:
    if not (add_metadata or add_file_names):
        return tables
    # Image metadata is small; retain its existing naming policy, without rebuilding
    # complete object row dictionaries just to project the selected columns.
    image_field = CellProfilerSpreadsheetRowField.IMAGE_NUMBER.value
    image_columns_by_number = {
        row[image_field]: _image_columns_for_objects(
            row,
            add_metadata=add_metadata,
            add_file_names=add_file_names,
        )
        for row in image_rows.iter_row_mappings()
        if image_field in row
    }
    updated = OrderedDict(tables)
    for subject in object_subjects:
        rows = tables.get(subject)
        if rows is None:
            continue
        columns = {
            name: ColumnarRows.column_array(rows.column_values(name)).copy()
            for name in rows.columns
        }
        fields = list(rows.fields)
        for index, number in enumerate(rows.column_values(image_field)):
            additions = image_columns_by_number.get(number, {})
            for name, value in additions.items():
                if name not in columns:
                    columns[name] = np.full(
                        rows.row_count(), MEASUREMENT_SPARSE_CELL, dtype=object
                    )
                    fields.append(FieldSpec(name, required=False))
                if is_structural_missing_measurement_cell(columns[name][index]):
                    columns[name][index] = value
        updated[subject] = MeasurementSparseColumnarRows(
            columns, fields=tuple(fields), object_row_identity=rows.object_row_identity
        )
    return updated


def _image_columns_for_objects(
    image_row: Mapping[str, object],
    *,
    add_metadata: bool,
    add_file_names: bool,
) -> Mapping[str, object]:
    result = {}
    for field_name, value in image_row.items():
        normalized = normalize_runtime_identifier(field_name)
        selected = (
            add_metadata and normalized.startswith(("metadata_", "image_metadata_"))
        ) or (
            add_file_names
            and normalized.startswith(
                (
                    "file_name_",
                    "path_name_",
                    "filename_",
                    "pathname_",
                    "url_",
                    "image_file_name_",
                    "image_path_name_",
                    "image_filename_",
                    "image_pathname_",
                    "image_url_",
                )
            )
        )
        if not selected:
            continue
        output_name = (
            field_name
            if normalized.startswith(("metadata_", "image_"))
            else f"Image_{field_name}"
        )
        result.setdefault(output_name, value)
    return result


def _automatic_file_selections(
    tables: Mapping[str, ColumnarRows],
    delimiter: SpreadsheetDelimiter,
) -> tuple[SpreadsheetFileSelection, ...]:
    return tuple(
        SpreadsheetFileSelection(
            subjects=(subject,),
            file_name=f"{subject}{delimiter.default_suffix}",
        )
        for subject in tables
    )


def _bundle_path_template(
    *,
    output_directory: str,
    prefix: str,
    file_name: str,
) -> str:
    relative_directory = output_directory.strip().replace("\\", "/").strip("/")
    path = PurePosixPath(relative_directory) / f"{prefix}{file_name}"
    return str(path)


def _rows_by_resolved_path(
    path_template: str,
    rows: ColumnarRows,
    *,
    image_rows: ColumnarRows,
) -> tuple[tuple[str, ColumnarRows], ...]:
    tokens = tuple(
        match.group("name") for match in _METADATA_TEMPLATE.finditer(path_template)
    )
    if not tokens:
        return ((path_template, rows),)
    image_field = CellProfilerSpreadsheetRowField.IMAGE_NUMBER.value
    image_row_mappings = tuple(image_rows.iter_row_mappings())
    image_rows_by_number = {
        row[image_field]: row for row in image_row_mappings if image_field in row
    }
    grouped: OrderedDict[str, list[int]] = OrderedDict()
    for index, row in enumerate(rows.iter_row_mappings()):
        metadata_row = dict(image_rows_by_number.get(row.get(image_field), {}))
        metadata_row.update(row)
        replacements = {}
        for token in tokens:
            value = _optional_metadata_value(metadata_row, token)
            if value is None:
                plate_values = tuple(
                    dict.fromkeys(
                        candidate
                        for image_row in image_row_mappings
                        for candidate in (_optional_metadata_value(image_row, token),)
                        if candidate is not None
                    )
                )
                if len(plate_values) != 1:
                    raise ValueError(
                        "Spreadsheet path template cannot resolve metadata field "
                        f"{token!r} for an unscoped row; plate values are "
                        f"{plate_values!r}."
                    )
                value = plate_values[0]
            replacements[token] = value
        relative_path = path_template.format_map(replacements)
        grouped.setdefault(relative_path, []).append(index)
    return tuple(
        (
            path,
            MeasurementSparseColumnarRows(
                {
                    name: ColumnarRows.column_array(rows.column_values(name))[
                        np.asarray(indexes, dtype=np.intp)
                    ]
                    for name in rows.columns
                },
                fields=rows.fields,
                object_row_identity=rows.object_row_identity,
            ),
        )
        for path, indexes in grouped.items()
    )


def _optional_metadata_value(
    row: Mapping[str, object],
    token: str,
) -> str | None:
    candidates = {
        normalize_runtime_identifier(token),
        normalize_runtime_identifier(f"Metadata_{token}"),
        normalize_runtime_identifier(f"Image_Metadata_{token}"),
    }
    for field_name, value in row.items():
        if normalize_runtime_identifier(field_name) in candidates:
            return str(value)
    return None


def _coerce_enum(enum_type: type[_EnumT], value: object) -> _EnumT:
    if isinstance(value, enum_type):
        return value
    return enum_type(value)


@execution_scope(FunctionStepExecutionScope.PLATE)
@runtime_bound_parameters(RuntimeArtifactBatch)
def export_to_spreadsheet(
    *,
    delimiter: SpreadsheetDelimiter = SpreadsheetDelimiter.COMMA,
    add_image_metadata: bool = False,
    add_image_file_names: bool = False,
    select_measurements: bool = False,
    selected_columns: tuple[SpreadsheetColumnSelection, ...] = (),
    calculate_aggregate_means: bool = False,
    calculate_aggregate_medians: bool = False,
    calculate_aggregate_standard_deviations: bool = False,
    output_directory: str = "",
    export_all_measurement_types: bool = True,
    file_selections: tuple[SpreadsheetFileSelection, ...] = (),
    nan_representation: SpreadsheetNanRepresentation = (
        SpreadsheetNanRepresentation.NAN
    ),
    add_filename_prefix: bool = True,
    filename_prefix: str = "MyExpt_",
    artifact_batch: RuntimeArtifactBatch,
    context: ProcessingContext | None = None,
) -> dict[str, ColumnarCsvOutput]:
    """Render one plate's exact contract-selected spreadsheet file bundle.

    Args:
        add_image_metadata: Copy Image metadata into object rows, projecting
            declared acquisition components from sourced measurement tables
            when requested. Absent coordinates are not synthesized.
        add_image_file_names: Project named source paths and filenames from
            measurement provenance and copy them into object rows. Source
            image pixels are not reloaded. Existing Image features are retained
            regardless of these flags.
        file_selections: Explicit output files and their measurement subjects
            when automatic export of all measurement types is disabled.
    """

    return prepare_spreadsheet_bundle(
        artifact_batch,
        context=context,
        delimiter=delimiter,
        add_image_metadata=add_image_metadata,
        add_image_file_names=add_image_file_names,
        select_measurements=select_measurements,
        selected_columns=selected_columns,
        calculate_aggregate_means=calculate_aggregate_means,
        calculate_aggregate_medians=calculate_aggregate_medians,
        calculate_aggregate_standard_deviations=(
            calculate_aggregate_standard_deviations
        ),
        output_directory=output_directory,
        export_all_measurement_types=export_all_measurement_types,
        file_selections=file_selections,
        nan_representation=nan_representation,
        add_filename_prefix=add_filename_prefix,
        filename_prefix=filename_prefix,
    )


class ExportToSpreadsheetModule(ArtifactExportModule):
    """Executable plate-scoped CellProfiler spreadsheet export declaration."""

    module_name = "ExportToSpreadsheet"
    function_name = "export_to_spreadsheet"
    validated = True
    confidence = 1.0

    delimiter_setting: ClassVar[SettingNameFamily] = SettingNameFamily(
        "Select the column delimiter"
    )
    add_metadata_setting: ClassVar[SettingNameFamily] = SettingNameFamily(
        "Add image metadata columns to your object data file?"
    )
    add_file_names_setting: ClassVar[SettingNameFamily] = SettingNameFamily(
        "Add image file and folder names to your object data file?"
    )
    select_measurements_setting: ClassVar[SettingNameFamily] = SettingNameFamily(
        "Select the measurements to export",
        ("Select measurements to export",),
    )
    aggregate_means_setting: ClassVar[SettingNameFamily] = SettingNameFamily(
        "Calculate the per-image mean values for object measurements?"
    )
    aggregate_medians_setting: ClassVar[SettingNameFamily] = SettingNameFamily(
        "Calculate the per-image median values for object measurements?"
    )
    aggregate_standard_deviations_setting: ClassVar[SettingNameFamily] = (
        SettingNameFamily(
            "Calculate the per-image standard deviation values for object measurements?"
        )
    )
    output_directory_setting: ClassVar[SettingNameFamily] = SettingNameFamily(
        "Output file location"
    )
    gene_pattern_setting: ClassVar[SettingNameFamily] = SettingNameFamily(
        "Create a GenePattern GCT file?"
    )
    gene_name_source_setting: ClassVar[SettingNameFamily] = SettingNameFamily(
        "Select source of sample row name"
    )
    gene_image_setting: ClassVar[SettingNameFamily] = SettingNameFamily(
        "Select the image to use as the identifier"
    )
    gene_metadata_setting: ClassVar[SettingNameFamily] = SettingNameFamily(
        "Select the metadata to use as the identifier"
    )
    export_all_setting: ClassVar[SettingNameFamily] = SettingNameFamily(
        "Export all measurement types?"
    )
    selected_columns_setting: ClassVar[SettingNameFamily] = SettingNameFamily(
        "Press button to select measurements"
    )
    nan_representation_setting: ClassVar[SettingNameFamily] = SettingNameFamily(
        "Representation of Nan/Inf"
    )
    add_prefix_setting: ClassVar[SettingNameFamily] = SettingNameFamily(
        "Add a prefix to file names?"
    )
    prefix_setting: ClassVar[SettingNameFamily] = SettingNameFamily("Filename prefix")
    overwrite_setting: ClassVar[SettingNameFamily] = SettingNameFamily(
        "Overwrite existing files without warning?"
    )
    excel_size_limit_setting: ClassVar[SettingNameFamily] = SettingNameFamily(
        "Limit output to a size that is allowed in Excel"
    )
    data_to_export_setting: ClassVar[SettingNameFamily] = SettingNameFamily(
        "Data to export"
    )
    combine_with_previous_setting: ClassVar[SettingNameFamily] = SettingNameFamily(
        "Combine these object measurements with those of the previous object?"
    )
    file_name_setting: ClassVar[SettingNameFamily] = SettingNameFamily("File name")
    automatic_file_name_setting: ClassVar[SettingNameFamily] = SettingNameFamily(
        "Use the object name for the file name?"
    )

    setting_bindings = (
        SettingToKeywordBinding(
            delimiter_setting,
            "delimiter",
            SpreadsheetDelimiter.from_cellprofiler,
        ),
        SettingToKeywordBinding(
            add_metadata_setting,
            "add_image_metadata",
            parse_cellprofiler_bool,
        ),
        SettingToKeywordBinding(
            add_file_names_setting,
            "add_image_file_names",
            parse_cellprofiler_bool,
        ),
        SettingToKeywordBinding(
            select_measurements_setting,
            "select_measurements",
            parse_cellprofiler_bool,
        ),
        SettingToKeywordBinding(
            selected_columns_setting,
            "selected_columns",
            SpreadsheetColumnSelection.from_cellprofiler,
        ),
        SettingToKeywordBinding(
            aggregate_means_setting,
            "calculate_aggregate_means",
            parse_cellprofiler_bool,
        ),
        SettingToKeywordBinding(
            aggregate_medians_setting,
            "calculate_aggregate_medians",
            parse_cellprofiler_bool,
        ),
        SettingToKeywordBinding(
            aggregate_standard_deviations_setting,
            "calculate_aggregate_standard_deviations",
            parse_cellprofiler_bool,
        ),
        SettingToKeywordBinding(
            output_directory_setting,
            "output_directory",
            cellprofiler_output_directory,
        ),
        SettingToKeywordBinding(
            export_all_setting,
            "export_all_measurement_types",
            parse_cellprofiler_bool,
        ),
        SettingToKeywordBinding(
            nan_representation_setting,
            "nan_representation",
            SpreadsheetNanRepresentation.from_cellprofiler,
        ),
        SettingToKeywordBinding(
            add_prefix_setting,
            "add_filename_prefix",
            parse_cellprofiler_bool,
        ),
        SettingToKeywordBinding(prefix_setting, "filename_prefix", str),
        SettingToKeywordBinding(
            overwrite_setting,
            parse=parse_cellprofiler_bool,
        ),
    )

    @classmethod
    def uses_cellprofiler_runtime_adapter(cls) -> bool:
        """Spreadsheet rendering runs through the generic plate executor."""

        return False

    @classmethod
    def ignored_settings_for(
        cls,
        module: ModuleBlock,
    ) -> tuple[str | SettingNameFamily, ...]:
        """Return inactive CP rows that do not participate in CSV rendering."""

        ignored: list[str | SettingNameFamily] = []
        gene_pattern = module.get_setting(cls.gene_pattern_setting.canonical, "")
        if not gene_pattern or not parse_cellprofiler_bool(gene_pattern):
            ignored.extend(
                (
                    cls.gene_pattern_setting,
                    cls.gene_name_source_setting,
                    cls.gene_image_setting,
                    cls.gene_metadata_setting,
                )
            )
        excel_size_limit = module.get_setting(
            cls.excel_size_limit_setting.canonical,
            "No",
        )
        if not parse_cellprofiler_bool(excel_size_limit):
            ignored.append(cls.excel_size_limit_setting)
        return tuple(ignored)

    @classmethod
    def postprocess_bound_settings(
        cls,
        module: ModuleBlock,
        bound: BoundModuleSettings,
    ) -> BoundModuleSettings:
        """Parse repeated export rows and reject unsupported active behavior."""

        gene_pattern = module.get_setting(cls.gene_pattern_setting.canonical, "No")
        if parse_cellprofiler_bool(gene_pattern):
            raise ValueError(
                "ExportToSpreadsheet GenePattern GCT output is not declared by the "
                "OpenHCS file-bundle contract."
            )
        excel_size_limit = module.get_setting(
            cls.excel_size_limit_setting.canonical,
            "No",
        )
        if parse_cellprofiler_bool(excel_size_limit):
            raise ValueError(
                "ExportToSpreadsheet Excel row and column truncation is not "
                "declared by the OpenHCS file-bundle contract."
            )
        kwargs = dict(bound.kwargs)
        kwargs["file_selections"] = cls._file_selections(
            module,
            delimiter=kwargs.get("delimiter", SpreadsheetDelimiter.COMMA),
            export_all=bool(kwargs.get("export_all_measurement_types", True)),
        )
        unmapped = dict(bound.unmapped_kwargs)
        for setting in (
            cls.data_to_export_setting,
            cls.combine_with_previous_setting,
            cls.file_name_setting,
            cls.automatic_file_name_setting,
        ):
            unmapped.pop(cls.normalize_setting_name(setting.canonical), None)
        return BoundModuleSettings(
            kwargs,
            unmapped,
            bound.setting_coverage,
        )

    @classmethod
    def _file_selections(
        cls,
        module: ModuleBlock,
        *,
        delimiter: SpreadsheetDelimiter,
        export_all: bool,
    ) -> tuple[SpreadsheetFileSelection, ...]:
        """Collapse CP's repeated output rows into typed file selections."""

        if export_all:
            return ()
        selections: list[SpreadsheetFileSelection] = []
        for block in repeating_setting_blocks(
            module.iter_settings(),
            start_name=cls.data_to_export_setting,
        ):
            subject = block_setting_value(block, cls.data_to_export_setting).strip()
            if not subject or is_blank_symbol_name(subject):
                continue
            combine = parse_cellprofiler_bool(
                block_setting_value(
                    block,
                    cls.combine_with_previous_setting,
                    default="No",
                )
            )
            automatic = parse_cellprofiler_bool(
                block_setting_value(
                    block,
                    cls.automatic_file_name_setting,
                    default="Yes",
                )
            )
            file_name = (
                f"{subject}{delimiter.default_suffix}"
                if automatic
                else cellprofiler_metadata_template(
                    block_setting_value(block, cls.file_name_setting)
                )
            )
            if not file_name:
                raise ValueError(
                    f"ExportToSpreadsheet subject {subject!r} has no output file name."
                )
            if combine:
                if not selections:
                    raise ValueError(
                        "ExportToSpreadsheet cannot combine its first data row with "
                        "a previous output."
                    )
                previous = selections[-1]
                selections[-1] = SpreadsheetFileSelection(
                    subjects=(*previous.subjects, subject),
                    file_name=previous.file_name,
                )
            else:
                selections.append(SpreadsheetFileSelection((subject,), file_name))
        return tuple(selections)

    @classmethod
    def artifact_contract_inputs(
        cls,
        module: ModuleBlock,
        *,
        invocation_key: "FunctionInvocationKey",
        step_context: "ArtifactDeclarationStepContext",
    ) -> tuple[ArtifactSpec, ...]:
        """Select the exact ordered tables exported by this plate module."""

        del (
            module,
            invocation_key,
        )
        return ArtifactSpecCollection(
            spec.for_plan_type(ArtifactInputPlan)
            for spec in step_context.available_artifacts.specs
            if issubclass(spec.artifact_type, MeasurementBearingArtifactType)
            or spec.artifact_type is RelationshipsArtifactType
        ).unique(conflict_context="ExportToSpreadsheet input")

    @classmethod
    def artifact_contract_outputs(
        cls,
        module: ModuleBlock,
        *,
        invocation_key: "FunctionInvocationKey",
        step_context: "ArtifactDeclarationStepContext",
        artifact_inputs: ArtifactSpecCollection,
    ) -> tuple[ArtifactSpec, ...]:
        """Declare the materialized spreadsheet bundle."""
        return (
            ArtifactSpec.output(
                cls._file_bundle_artifact_name(
                    module,
                    invocation_key=invocation_key,
                    step_context=step_context,
                ),
                SpecialArtifactType,
                materialization=MaterializationSpec(
                    FileBundleOptions(),
                    write_mode=(
                        WriteMode.OVERWRITE
                        if parse_cellprofiler_bool(
                            module.get_setting(cls.overwrite_setting.canonical, "Yes")
                        )
                        else WriteMode.ERROR
                    ),
                ),
            ),
        )

    @classmethod
    def _file_bundle_artifact_name(
        cls,
        module: ModuleBlock,
        *,
        invocation_key: "FunctionInvocationKey",
        step_context: "ArtifactDeclarationStepContext",
    ) -> str:
        step_index = step_context.step_index
        if not isinstance(step_index, int):
            raise TypeError(
                "ExportToSpreadsheet requires an integer step index for its file "
                "bundle identity."
            )
        suffix = str(step_index + 1)
        if invocation_key.position:
            suffix = f"{suffix}_{invocation_key.position + 1}"
        return f"{module.name}_{suffix}_files"
