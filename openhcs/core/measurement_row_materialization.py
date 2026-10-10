"""Measurement row materialization and columnar view semantics."""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import (
    Callable,
    Iterable,
    Iterator,
    Mapping,
    MutableMapping,
    Sequence,
)
from dataclasses import dataclass, field, fields as dataclass_fields, is_dataclass
from dataclasses import replace as dataclass_replace
from functools import lru_cache
from itertools import chain
from types import MappingProxyType
from typing import Any, ClassVar, TYPE_CHECKING, TypeAlias, cast

from metaclass_registry import AutoRegisterMeta
from openhcs.constants.constants import AllComponents
from openhcs.core.alias_property import AliasProperty
import numpy as np

from metaclass_registry.strategies import NominalTypeStrategyFamilyMixin
from openhcs.core.runtime_identifier import normalize_runtime_identifier
from openhcs.core.runtime_measurements import (
    MeasurementRowAxisField,
    MeasurementRowValueField,
    MeasurementScalarLiteral,
    MeasurementScope,
    RuntimeMeasurementRowIdentityContract,
    measurement_axis_integer_domain,
    measurement_axis_integer_value,
)
from openhcs.core.runtime_tabular_values import (
    FieldSpec,
    MeasurementObjectRowIdentity,
    measurement_row_mapping,
)
from openhcs.core.runtime_tabular_values import (
    ColumnarRows,
)
from openhcs.core.runtime_measurements import (
    MeasurementTable,
)
from openhcs.core.source_image_provenance import SourceImageProvenance
from openhcs.core.source_matching import source_component_metadata_value

from enum import Enum


@lru_cache(maxsize=32768)
def normalized_measurement_row_fields(
    fields: tuple[str, ...],
) -> Mapping[str, str]:
    """Return normalized field-name lookup for one measurement row shape."""
    return MappingProxyType(
        {normalize_runtime_identifier(field): field for field in fields}
    )


def normalized_measurement_row_fields_for_row(
    row: Mapping[str, object],
) -> Mapping[str, str]:
    """Return cached normalized field names for one row mapping."""
    return normalized_measurement_row_fields(tuple(str(field) for field in row))


def is_structural_missing_measurement_cell(value: object) -> bool:
    """Return whether a columnar value marks structural absence, not a value."""
    return isinstance(value, MeasurementSparseCell)


def columnar_row_values(rows: ColumnarRows, column: str) -> Sequence[object]:
    """Return one column from a nominal columnar payload."""
    return rows.column_values(column)


def projected_columnar_fields(
    rows: ColumnarRows,
    field_spec: FieldSpec,
) -> tuple[FieldSpec, ...]:
    """Return fields for a projection that adds or replaces one exact column."""
    return FieldSpec.merge_exact(
        (rows.fields, (field_spec,)),
        context="projected column fields",
    )


def column_mapping_row_count(columns: Mapping[str, Sequence[object]]) -> int:
    """Return row count for a concrete column mapping."""
    if not columns:
        return 0
    return len(next(iter(columns.values())))


def iter_measurement_rows(
    measurement_tables: Iterable[MeasurementTable],
) -> Iterator[object]:
    """Yield row payloads from measurement tables without materializing them."""
    for table in measurement_tables:
        yield from table.rows.iter_row_mappings()


def measurement_rows(
    measurement_tables: tuple[MeasurementTable, ...],
) -> tuple[object, ...]:
    """Flatten row payloads from measurement tables."""
    return tuple(iter_measurement_rows(measurement_tables))


def measurement_table_axis_values(
    table: MeasurementTable,
    axis: MeasurementRowAxisField,
) -> set[int]:
    """Return declared row-axis values for one measurement table."""
    axis_field = axis.value
    if isinstance(table.rows, ColumnarRows):
        column_names = tuple(str(column) for column in table.rows.columns)
        if axis_field not in column_names:
            return set()
        return set(
            measurement_axis_integer_domain(
                columnar_row_values(table.rows, axis_field),
                axis,
            )
        )
    return {
        axis_integer
        for row in measurement_rows((table,))
        for row_mapping in (measurement_row_mapping(row),)
        for axis_integer in (
            measurement_axis_integer_value(row_mapping.get(axis_field), axis),
        )
        if axis_integer is not None
    }


if TYPE_CHECKING:
    from openhcs.core.equivalence.policy import RuntimeMeasurementDialect


MeasurementFeatureNameProjection: TypeAlias = Callable[
    [str, tuple[tuple[str, object], ...]],
    str,
]


class ObjectMeasurementColumnarRows(ColumnarRows, ABC):
    """Object measurement columns spanning their declared label domain."""

    @property
    def covers_declared_object_measurement_domain(self) -> bool:
        """Object-measurement carriers span their declared label domain."""
        return True

    def __len__(self) -> int:
        return self.row_count()

    def __iter__(self):
        yield from self.iter_row_mappings()


class MeasurementRowDeclaredValue(ABC, metaclass=AutoRegisterMeta):
    """Nominal declaration for values projected from a measurement row."""

    __registry_key__ = "__name__"
    __skip_if_no_key__ = True
    declares_row_value: ClassVar[bool] = False

    @classmethod
    def declared_value_types(cls) -> tuple[type["MeasurementRowDeclaredValue"], ...]:
        """Return registered concrete row-value declarations."""
        return tuple(
            dict.fromkeys(
                declaration_type
                for declaration_type in cls.__registry__.values()
                if declaration_type.declares_row_value
                and not declaration_type.__abstractmethods__
            )
        )

    @classmethod
    def values_for_row(
        cls,
        row: Mapping[str, object],
        *,
        normalized_fields: Mapping[str, str] | None = None,
    ) -> Mapping[type["MeasurementRowDeclaredValue"], object | None]:
        """Return every declared row value keyed by its declaration type."""
        return MappingProxyType(
            {
                declaration_type: declaration_type.value_from_row(
                    row,
                    normalized_fields=normalized_fields,
                )
                for declaration_type in cls.declared_value_types()
            }
        )

    @classmethod
    @abstractmethod
    def value_from_row(
        cls,
        row: Mapping[str, object],
        *,
        normalized_fields: Mapping[str, str] | None = None,
        object_id_field: str | None = None,
    ) -> object | None:
        """Return this declared value from one measurement row."""


class MeasurementRowTextValue(MeasurementRowDeclaredValue):
    """Shared declaration for normalized text values stored in row fields."""

    field_names: ClassVar[tuple[str, ...]] = ()

    @staticmethod
    def normalize_value(value: object) -> str | None:
        """Read the shared text ownership law from one physical column cell."""
        if value is None or is_structural_missing_measurement_cell(value):
            return None
        return str(value).strip() or None

    @classmethod
    def domain_from_column(
        cls, rows: ColumnarRows, column_name: str
    ) -> tuple[str | None, ...]:
        """Read distinct ownership text from physical segments in row order.

        Built-in text cells can be admitted before normalization. Other atomic
        cells retain the existing text conversion law, including unhashable
        arrays or lists. Missing physical segments own the default subject.
        """
        if column_name not in rows.columns:
            return (None,)
        raw_domain: dict[str | None, None] = {}
        row_stop = 0
        for offset, values in rows.column_value_segments(column_name):
            if offset > row_stop:
                raw_domain.setdefault(None, None)
            for value in values:
                text = (
                    value
                    if type(value) is str or type(value) is np.str_
                    else cls.normalize_value(value)
                )
                raw_domain.setdefault(text, None)
            row_stop = offset + len(values)
        if row_stop < rows.row_count():
            raw_domain.setdefault(None, None)
        return tuple(dict.fromkeys(cls.normalize_value(value) for value in raw_domain))

    @classmethod
    def value_from_row(
        cls,
        row: Mapping[str, object],
        *,
        normalized_fields: Mapping[str, str] | None = None,
        object_id_field: str | None = None,
    ) -> str | None:
        del object_id_field
        for field_name in cls.field_names:
            value = measurement_row_declared_field_value(
                row,
                field_name,
                normalized_fields,
            )
            normalized = cls.normalize_value(value)
            if normalized is not None:
                return normalized
        return None


class MeasurementRowObjectName(MeasurementRowTextValue):
    """Object owner encoded on a measurement row."""

    declares_row_value = True
    field_names = (MeasurementRowAxisField.OBJECT_NAME.value,)


class MeasurementRowSourceImageName(MeasurementRowTextValue):
    """Source-image owner encoded on a measurement row."""

    declares_row_value = True
    field_names = (MeasurementRowAxisField.SOURCE_IMAGE_NAME.value,)


class MeasurementRowObjectLabel(MeasurementRowDeclaredValue):
    """Resolved object label encoded on a measurement row."""

    declares_row_value = True

    @classmethod
    def value_from_row(
        cls,
        row: Mapping[str, object],
        *,
        normalized_fields: Mapping[str, str] | None = None,
        object_id_field: str | None = None,
    ) -> int | None:
        if object_id_field is not None:
            value = measurement_row_declared_field_value(
                row,
                object_id_field,
                normalized_fields,
            )
            if value is not None:
                return measurement_object_label_value(value)
        for key in MeasurementRowAxisField.object_id_field_names():
            value = measurement_row_declared_field_value(row, key, normalized_fields)
            if value is not None:
                return measurement_object_label_value(value)
        return None


class MeasurementRowObjectIdentityRole(MeasurementRowDeclaredValue):
    """Explicit OpenHCS object-row identity role encoded on a row."""

    declares_row_value = True

    @classmethod
    def explicit_value_from_row(
        cls,
        row: Mapping[str, object],
        *,
        normalized_fields: Mapping[str, str] | None = None,
    ) -> MeasurementObjectRowIdentity | None:
        """Return only the identity role explicitly encoded on the row."""
        value = measurement_row_declared_field_value(
            row,
            MeasurementRowAxisField.OBJECT_ROW_IDENTITY.value,
            normalized_fields,
        )
        if value in MeasurementObjectRowIdentity._value2member_map_:
            return MeasurementObjectRowIdentity(value)
        return None

    @classmethod
    def value_from_row(
        cls,
        row: Mapping[str, object],
        *,
        normalized_fields: Mapping[str, str] | None = None,
        object_id_field: str | None = None,
    ) -> MeasurementObjectRowIdentity | None:
        del object_id_field
        explicit_identity = cls.explicit_value_from_row(
            row,
            normalized_fields=normalized_fields,
        )
        if explicit_identity is not None:
            return explicit_identity
        if (
            measurement_row_declared_field_value(
                row,
                MeasurementRowAxisField.OBJECT_LABEL.value,
                normalized_fields,
            )
            is not None
        ):
            return MeasurementObjectRowIdentity.LABEL_ID
        return None

    @classmethod
    def resolve_value_from_row(
        cls,
        row: Mapping[str, object],
        *,
        carrier_identity: MeasurementObjectRowIdentity | None,
        normalized_fields: Mapping[str, str] | None = None,
    ) -> MeasurementObjectRowIdentity | None:
        """Resolve row identity with the nominal columnar carrier as authority."""
        explicit_identity = cls.explicit_value_from_row(
            row,
            normalized_fields=normalized_fields,
        )
        if (
            explicit_identity is not None
            and carrier_identity is not None
            and explicit_identity is not carrier_identity
        ):
            raise ValueError(
                "Measurement row identity conflicts with its nominal columnar "
                f"carrier: {explicit_identity.value!r} != "
                f"{carrier_identity.value!r}."
            )
        if carrier_identity is not None:
            return carrier_identity
        return cls.value_from_row(
            row,
            normalized_fields=normalized_fields,
        )


@dataclass(frozen=True, slots=True)
class MeasurementProjectedColumnarRows(ColumnarRows):
    """Columnar measurement rows with projected row-axis values."""

    columns: Mapping[str, Sequence[Any]]
    fields: tuple[FieldSpec, ...] = ()
    declared_object_measurement_domain_covered: bool = False
    object_row_identity: MeasurementObjectRowIdentity | None = None

    def __post_init__(self) -> None:
        self.validate_fields()

    @classmethod
    def from_columnar_rows(
        cls,
        rows: ColumnarRows,
        *,
        row_indices: Sequence[int] | None = None,
        declared_object_measurement_domain_covered: bool,
        object_row_identity: MeasurementObjectRowIdentity | None,
    ) -> "MeasurementProjectedColumnarRows":
        """Project declared columns without reconstructing row mappings."""
        fields = rows.fields
        if row_indices is None:
            columns = {
                field_spec.name: rows.column_values(field_spec.name)
                for field_spec in fields
            }
        else:
            selected_indices = tuple(int(row_index) for row_index in row_indices)
            row_count = rows.row_count()
            invalid_indices = tuple(
                row_index
                for row_index in selected_indices
                if row_index < 0 or row_index >= row_count
            )
            if invalid_indices:
                raise IndexError(
                    "Columnar row projection indices are outside the row domain: "
                    f"{invalid_indices!r} for {row_count} rows."
                )
            numpy_indices = np.asarray(selected_indices, dtype=np.intp)

            def selected_values(field_spec: FieldSpec) -> Sequence[Any]:
                values = rows.column_values(field_spec.name)
                if isinstance(values, np.ndarray):
                    return values[numpy_indices]
                return tuple(values[row_index] for row_index in selected_indices)

            columns = {
                field_spec.name: selected_values(field_spec) for field_spec in fields
            }
        return cls(
            MappingProxyType(columns),
            fields=fields,
            declared_object_measurement_domain_covered=(
                declared_object_measurement_domain_covered
            ),
            object_row_identity=object_row_identity,
        )

    @property
    def covers_declared_object_measurement_domain(self) -> bool:
        """Return whether projection preserved complete object-domain rows."""
        return bool(self.declared_object_measurement_domain_covered)

    def __len__(self) -> int:
        return column_mapping_row_count(self.columns)

    def __iter__(self):
        yield from self.iter_row_mappings()

    def __getitem__(
        self, row_index: int | slice
    ) -> Mapping[str, object] | tuple[Mapping[str, object], ...]:
        if not isinstance(row_index, (int, slice)):
            raise TypeError(
                f"{type(self).__name__} indices must be integers or slices, got "
                f"{type(row_index).__name__}."
            )
        if isinstance(row_index, slice):
            return tuple(
                self._row_mapping_at(selected_index)
                for selected_index in range(*row_index.indices(len(self)))
            )
        selected_index = row_index if row_index >= 0 else len(self) + row_index
        if selected_index < 0 or selected_index >= len(self):
            raise IndexError(row_index)
        return self._row_mapping_at(selected_index)

    def _row_mapping_at(self, row_index: int) -> Mapping[str, object]:
        return {
            field_name: value
            for field_name, values in self.columns.items()
            for value in (values[row_index],)
            if not is_structural_missing_measurement_cell(value)
        }

    def iter_row_mappings(self):
        columns = tuple(str(column) for column in self.columns)
        column_values = tuple(self.column_values(column) for column in columns)
        for row_index in range(len(self)):
            yield {
                field_name: values[row_index]
                for field_name, values in zip(columns, column_values, strict=True)
                if not is_structural_missing_measurement_cell(values[row_index])
            }

    def row_mappings(self) -> tuple[Mapping[str, object], ...]:
        return tuple(self.iter_row_mappings())


@dataclass(frozen=True, slots=True)
class MeasurementSparseCell:
    """Structural missing-cell marker for sparse columnar row materialization."""


MEASUREMENT_SPARSE_CELL = MeasurementSparseCell()


@dataclass(frozen=True, slots=True)
class ColumnarRowColumnOverlay(Mapping[str, Sequence[Any]]):
    """Lazy column mapping that overlays projected columns on an existing table."""

    base_columns: Mapping[str, Sequence[Any]]
    overlay_columns: Mapping[str, Sequence[Any]]
    column_names: tuple[str, ...] = field(init=False)

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "column_names",
            tuple(
                dict.fromkeys(
                    (
                        *(str(column) for column in self.base_columns),
                        *(str(column) for column in self.overlay_columns),
                    )
                )
            ),
        )

    def __getitem__(self, column_name: str) -> Sequence[Any]:
        if column_name in self.overlay_columns:
            return self.overlay_columns[column_name]
        return self.base_columns[column_name]

    def __contains__(self, column_name: object) -> bool:
        return column_name in self.column_names

    def __iter__(self):
        return iter(self.column_names)

    def __len__(self) -> int:
        return len(self.column_names)


@dataclass(frozen=True, slots=True)
class MeasurementSparseColumnarRows(ColumnarRows):
    """Columnar measurement rows whose missing cells are structural, not values."""

    columns: Mapping[str, Sequence[Any]]
    fields: tuple[FieldSpec, ...] = ()
    missing_cell: object = MEASUREMENT_SPARSE_CELL
    declared_object_measurement_domain_covered: bool = False
    object_row_identity: MeasurementObjectRowIdentity | None = None

    def __post_init__(self) -> None:
        self.validate_fields()

    @staticmethod
    def present_mask(
        values: np.ndarray,
        *,
        missing_cell: object = MEASUREMENT_SPARSE_CELL,
    ) -> np.ndarray:
        """Derive physical presence without boxing dense typed scalar columns."""
        if not values.dtype.hasobject and missing_cell is MEASUREMENT_SPARSE_CELL:
            return np.ones(len(values), dtype=bool)
        return np.fromiter(
            (
                value is not missing_cell
                and not is_structural_missing_measurement_cell(value)
                for value in values
            ),
            dtype=bool,
            count=len(values),
        )

    @classmethod
    def from_rows(
        cls,
        rows: Sequence[object],
        *,
        fields: tuple[FieldSpec, ...],
        declared_object_measurement_domain_covered: bool = False,
        missing_cell: object = MEASUREMENT_SPARSE_CELL,
        object_row_identity: MeasurementObjectRowIdentity | None = None,
    ) -> "MeasurementSparseColumnarRows":
        """Return a sparse columnar view over heterogeneous measurement rows."""
        row_mappings = coalesced_sparse_measurement_row_mappings(
            tuple(measurement_row_mapping(row) for row in rows),
            missing_cell=missing_cell,
        )
        field_names = tuple(field_spec.name for field_spec in fields)
        declared_names = frozenset(field_names)
        undeclared_names = tuple(
            dict.fromkeys(
                field_name
                for row_mapping in row_mappings
                for field_name in row_mapping
                if field_name not in declared_names
            )
        )
        if undeclared_names:
            raise ValueError(
                "Sparse measurement rows contain columns absent from their "
                f"declared fields: {undeclared_names!r}."
            )
        return cls(
            MappingProxyType(
                {
                    field_name: tuple(
                        row_mapping.get(field_name, missing_cell)
                        for row_mapping in row_mappings
                    )
                    for field_name in field_names
                }
            ),
            fields=fields,
            missing_cell=missing_cell,
            declared_object_measurement_domain_covered=(
                declared_object_measurement_domain_covered
            ),
            object_row_identity=object_row_identity,
        )

    @classmethod
    def from_columnar_batches(
        cls,
        batches: Sequence[ColumnarRows],
        *,
        declared_object_measurement_domain_covered: bool = False,
        missing_cell: object = MEASUREMENT_SPARSE_CELL,
        identity_fields: Sequence[str] | None = None,
        values_equal: Callable[[object, object], bool] | None = None,
    ) -> "MeasurementSparseColumnarRows":
        """Return sparse rows coalesced across columnar batches."""
        fields = FieldSpec.merge_exact(
            (batch.fields for batch in batches),
            context="columnar batch fields",
        )
        names = tuple(field.name for field in fields)
        identities = (
            tuple(
                field.value for field in MeasurementRowAxisField if field.value in names
            )
            if identity_fields is None
            else tuple(identity_fields)
        )
        undeclared = tuple(name for name in identities if name not in names)
        if undeclared:
            raise ValueError(
                f"Columnar join identities are undeclared: {undeclared!r}."
            )
        equal = (
            _measurement_sparse_cell_values_equal
            if values_equal is None
            else values_equal
        )
        row_domain: dict[tuple[tuple[str, object], ...], int] = {}
        segments: list[tuple[np.ndarray, Mapping[str, Sequence[object]]]] = []
        passthrough = 0
        for batch in batches:
            for count, columns in batch.columnar_row_batches():
                identity_columns = tuple(
                    (name, columns[name]) for name in identities if name in columns
                )
                first_segment = segments[0] if segments else None
                aligned = (
                    first_segment is not None
                    and len(first_segment[0]) == count
                    and all(
                        name in first_segment[1]
                        and np.array_equal(values, first_segment[1][name])
                        for name, values in identity_columns
                    )
                    and tuple(name for name in identities if name in first_segment[1])
                    == tuple(name for name, _values in identity_columns)
                    and bool(identity_columns)
                    and (
                        any(
                            isinstance(values, np.ndarray)
                            and not values.dtype.hasobject
                            for _name, values in identity_columns
                        )
                        or all(
                            any(
                                not is_structural_missing_measurement_cell(
                                    values[index]
                                )
                                for _name, values in identity_columns
                            )
                            for index in range(count)
                        )
                    )
                )
                if aligned:
                    destinations = first_segment[0]
                else:
                    destinations = np.empty(count, dtype=np.intp)
                    for index in range(count):
                        identity = tuple(
                            (name, values[index])
                            for name, values in identity_columns
                            if not is_structural_missing_measurement_cell(values[index])
                        )
                        if not identity:
                            identity = (("__row_index__", passthrough),)
                            passthrough += 1
                        destinations[index] = row_domain.setdefault(
                            identity, len(row_domain)
                        )
                segments.append((destinations, columns))
        columns: dict[str, np.ndarray] = {}
        for destinations, source_columns in segments:
            complete_projection = np.unique(
                destinations, return_index=True, return_inverse=True
            )
            for name, values in source_columns.items():
                values = ColumnarRows.column_array(values)
                present = cls.present_mask(values, missing_cell=missing_cell)
                indexes = destinations[present]
                admitted = values[present]
                unique, first, inverse = (
                    complete_projection
                    if bool(np.all(present))
                    else np.unique(indexes, return_index=True, return_inverse=True)
                )
                selected = admitted[first]
                repeated = np.arange(len(admitted)) != first[inverse]
                if values_equal is not None or not equal(admitted, selected[inverse]):
                    for value, previous in zip(
                        admitted[repeated], selected[inverse][repeated], strict=True
                    ):
                        if not equal(previous, value):
                            raise ValueError(
                                f"Conflicting sparse measurement values for field {name!r}: {previous!r} vs {value!r}."
                            )
                target = columns.get(name)
                if target is None:
                    if len(unique) == len(row_domain):
                        columns[name] = selected.copy()
                    else:
                        target = np.full(len(row_domain), missing_cell, dtype=object)
                        target[unique] = selected
                        columns[name] = target
                    continue
                previous = target[unique]
                overlap = (
                    np.ones(len(previous), dtype=bool)
                    if not target.dtype.hasobject
                    and missing_cell is MEASUREMENT_SPARSE_CELL
                    else np.fromiter(
                        (
                            not is_structural_missing_measurement_cell(value)
                            and value is not missing_cell
                            for value in previous
                        ),
                        dtype=bool,
                        count=len(previous),
                    )
                )
                if values_equal is not None or not equal(
                    previous[overlap], selected[overlap]
                ):
                    for left, right in zip(
                        previous[overlap], selected[overlap], strict=True
                    ):
                        if not equal(left, right):
                            raise ValueError(
                                f"Conflicting sparse measurement values for field {name!r}: {left!r} vs {right!r}."
                            )
                if target.dtype != selected.dtype:
                    target = target.astype(object)
                    columns[name] = target
                target[unique] = selected
        columns = {
            name: columns.get(
                name, np.full(len(row_domain), missing_cell, dtype=object)
            )
            for name in names
        }
        return cls(
            MappingProxyType(columns),
            fields=fields,
            declared_object_measurement_domain_covered=(
                declared_object_measurement_domain_covered
            ),
            missing_cell=missing_cell,
            object_row_identity=ColumnarRows.common_object_row_identity(batches),
        )

    @property
    def covers_declared_object_measurement_domain(self) -> bool:
        """Return whether these sparse rows were completed over object domain."""
        return bool(self.declared_object_measurement_domain_covered)

    def __len__(self) -> int:
        return column_mapping_row_count(self.columns)

    def __iter__(self):
        yield from self.iter_row_mappings()

    def __getitem__(
        self, row_index: int | slice
    ) -> Mapping[str, object] | tuple[Mapping[str, object], ...]:
        if not isinstance(row_index, (int, slice)):
            raise TypeError(
                f"{type(self).__name__} indices must be integers or slices, got "
                f"{type(row_index).__name__}."
            )
        return self.row_mappings()[row_index]

    def iter_row_mappings(self):
        columns = self.columns
        for row_index in range(len(self)):
            yield {
                field_name: value
                for field_name, values in columns.items()
                for value in (values[row_index],)
                if not is_structural_missing_measurement_cell(value)
            }

    def row_mappings(self) -> tuple[Mapping[str, object], ...]:
        return tuple(self)


def coalesced_sparse_measurement_row_mappings(
    row_mappings: Sequence[Mapping[str, object]],
    *,
    missing_cell: object = MEASUREMENT_SPARSE_CELL,
) -> tuple[Mapping[str, object], ...]:
    """Merge sparse feature fragments that share the same row-axis identity."""
    if not row_mappings:
        return ()
    identity_fields = tuple(
        field.value
        for field in MeasurementRowAxisField
        if any(field.value in row for row in row_mappings)
    )
    if not identity_fields:
        return tuple(row_mappings)

    coalesced: dict[tuple[tuple[str, object], ...], dict[str, object]] = {}
    order: list[tuple[tuple[str, object], ...]] = []
    passthrough_index = 0
    for row in row_mappings:
        identity = tuple(
            (field_name, row[field_name])
            for field_name in identity_fields
            if field_name in row
            and not is_structural_missing_measurement_cell(row[field_name])
        )
        if not identity:
            identity = (("__row_index__", passthrough_index),)
            passthrough_index += 1
        merged = coalesced.get(identity)
        if merged is None:
            merged = {}
            coalesced[identity] = merged
            order.append(identity)
        for field_name, value in row.items():
            if value is missing_cell or is_structural_missing_measurement_cell(value):
                continue
            existing = merged.get(field_name, missing_cell)
            if (
                existing is not missing_cell
                and not is_structural_missing_measurement_cell(existing)
                and not _measurement_sparse_cell_values_equal(existing, value)
            ):
                raise ValueError(
                    "Conflicting sparse measurement values for row identity "
                    f"{identity!r}, field {field_name!r}: {existing!r} vs {value!r}."
                )
            merged[field_name] = value
    return tuple(MappingProxyType(coalesced[identity]) for identity in order)


def measurement_column_carries_scalar_values(values: Sequence[object]) -> bool:
    """Return whether a column carries scalar measurement values."""

    saw_none = False
    for value in values:
        if is_structural_missing_measurement_cell(value):
            continue
        if value is None:
            saw_none = True
            continue
        return MeasurementScalarLiteral(value).token is not None
    return saw_none


def wide_measurement_feature_columns(
    columns: Mapping[str, Sequence[object]],
    *,
    object_id_field: str | None = None,
    qualifier_field_names: Iterable[str] = (),
) -> tuple[tuple[str, Sequence[object]], ...]:
    """Return scalar feature columns after excluding declared row structure."""

    object_id_fields = tuple(
        dict.fromkeys(
            (
                *((object_id_field,) if object_id_field is not None else ()),
                *MeasurementRowAxisField.object_id_field_names(),
            )
        )
    )
    folded_axis_fields = frozenset(
        (
            MeasurementRowAxisField.OBJECT_NAME.value,
            MeasurementRowAxisField.SOURCE_IMAGE_NAME.value,
            MeasurementRowAxisField.OBJECT_ROW_IDENTITY.value,
            *object_id_fields,
            *qualifier_field_names,
        )
    )
    return tuple(
        (field_name, values)
        for field_name, values in columns.items()
        if field_name not in MeasurementRowAxisField.field_names()
        and field_name not in MeasurementRowValueField.field_names()
        and field_name not in folded_axis_fields
        and measurement_column_carries_scalar_values(values)
    )


@dataclass(slots=True)
class WideMeasurementRowAccumulator:
    """Admit projected batches and derive each completed subject once on consumption."""

    row_identity_contract: RuntimeMeasurementRowIdentityContract
    required_subjects: frozenset[str] | None = None
    _batches_by_subject: dict[str, list[ColumnarRows]] = field(
        default_factory=dict, init=False, repr=False
    )
    _object_subjects: list[str] = field(default_factory=list, init=False, repr=False)

    def __post_init__(self) -> None:
        if not isinstance(
            self.row_identity_contract,
            RuntimeMeasurementRowIdentityContract,
        ):
            raise TypeError(
                "WideMeasurementRowAccumulator requires a "
                "RuntimeMeasurementRowIdentityContract."
            )

    def _admit_subject(self, subject: str, scope: MeasurementScope) -> bool:
        if scope is MeasurementScope.OBJECT and subject not in self._object_subjects:
            self._object_subjects.append(subject)
        return self.required_subjects is None or subject in self.required_subjects

    @staticmethod
    def _long_form_fields(
        column_names: Iterable[str],
    ) -> tuple[tuple[str, ...], tuple[str, ...]]:
        names = frozenset(column_names)
        features = tuple(
            name
            for name in MeasurementRowAxisField.feature_name_field_names_ordered()
            if name in names
        )
        values = tuple(
            name
            for name in MeasurementRowValueField.field_names_ordered()
            if name in names
        )
        if features and not values:
            raise ValueError("Long-form measurement columns have no value column.")
        return features, values

    def admits_declared_rows(
        self,
        rows: ColumnarRows,
        *,
        default_subject: str,
        default_scope: MeasurementScope,
    ) -> bool:
        """Admit subject demand before projecting or copying measurement cells.

        Object ownership can override the table declaration. Keep its complete
        ordered subject roster even when none of those subjects is requested;
        image-reference means may demand their values later.
        """
        if self.required_subjects is None:
            return True
        if not rows.row_count():
            return False
        self._long_form_fields(rows.columns)
        field_name = MeasurementRowAxisField.OBJECT_NAME.value
        object_names = MeasurementRowObjectName.domain_from_column(rows, field_name)
        admitted = False
        for name in object_names:
            subject = name or default_subject
            scope = MeasurementRowOwnership(object_name=name).scope(default_scope)
            if self._admit_subject(subject, scope):
                admitted = True
        return admitted

    def add(
        self,
        rows: Sequence[object] | ColumnarRows,
        project_feature_name: MeasurementFeatureNameProjection,
        *,
        default_subject: str,
        default_scope: MeasurementScope = MeasurementScope.ARTIFACT,
        object_id_field: str | None = None,
        qualifier_field_names: Iterable[str] = (),
        missing_cell: object = MEASUREMENT_SPARSE_CELL,
    ) -> None:
        """Add one measurement payload without materializing input row mappings."""
        if not isinstance(rows, ColumnarRows):
            rows = self._columnar_rows(rows, missing_cell)
        row_count = rows.row_count()
        if row_count == 0:
            return
        columns = {
            str(column): rows.column_values(str(column)) for column in rows.columns
        }
        feature_columns = wide_measurement_feature_columns(
            columns,
            object_id_field=object_id_field,
            qualifier_field_names=qualifier_field_names,
        )
        self._add_columns(
            columns,
            row_count,
            feature_columns,
            project_feature_name,
            default_subject=default_subject,
            default_scope=default_scope,
            object_id_field=object_id_field,
            qualifier_field_names=qualifier_field_names,
            missing_cell=missing_cell,
        )

    def add_declared_rows(
        self,
        rows: ColumnarRows,
        dialect: RuntimeMeasurementDialect,
        *,
        default_subject: str,
        default_scope: MeasurementScope = MeasurementScope.ARTIFACT,
        object_id_field: str | None = None,
        qualifier_field_names: Iterable[str] = (),
        missing_cell: object = MEASUREMENT_SPARSE_CELL,
    ) -> None:
        """Admit correlated physical batches using a declared export grammar.

        Opaque callbacks retain add()'s complete, writable column admission.
        Here snapshots are call-local and no sparse union arrays are retained.
        """
        names = tuple(str(column) for column in rows.columns)
        batches = tuple(
            (
                count,
                {
                    name: np.array(
                        values,
                        copy=True,
                        dtype=None if isinstance(values, np.ndarray) else object,
                    )
                    for name, values in columns.items()
                },
            )
            for count, columns in rows.columnar_row_batches()
        )
        eligible = frozenset(
            name
            for name, _values in wide_measurement_feature_columns(
                {
                    name: chain.from_iterable(
                        tuple(
                            columns[name]
                            for _count, columns in batches
                            if name in columns
                        )
                    )
                    for name in names
                },
                object_id_field=object_id_field,
                qualifier_field_names=qualifier_field_names,
            )
        )
        structural_names = tuple(name for name in names if name not in eligible)
        for count, source_columns in batches:
            if not count:
                continue
            columns = {
                name: source_columns[name]
                for name in names
                if name in source_columns
                and (
                    name not in eligible
                    or (
                        source_columns[name].size
                        and not source_columns[name].dtype.hasobject
                    )
                    or any(
                        not is_structural_missing_measurement_cell(value)
                        for value in source_columns[name]
                    )
                )
            }
            for name in structural_names:
                if name not in columns:
                    values = np.empty(count, dtype=object)
                    values.fill(MEASUREMENT_SPARSE_CELL)
                    columns[name] = values
            columns = {name: columns[name] for name in names if name in columns}
            self._add_columns(
                columns,
                count,
                tuple(
                    (name, values)
                    for name, values in columns.items()
                    if name in eligible
                ),
                dialect.projected_feature_name,
                default_subject=default_subject,
                default_scope=default_scope,
                object_id_field=object_id_field,
                qualifier_field_names=qualifier_field_names,
                missing_cell=missing_cell,
            )

    def _add_columns(
        self,
        columns: Mapping[str, Sequence[object]],
        row_count: int,
        feature_columns: tuple[tuple[str, Sequence[object]], ...],
        project_feature_name: MeasurementFeatureNameProjection,
        *,
        default_subject: str,
        default_scope: MeasurementScope,
        object_id_field: str | None,
        qualifier_field_names: Iterable[str],
        missing_cell: object,
    ) -> None:
        if not row_count:
            return
        image_fields = self.row_identity_contract.selected_image_identity_fields(
            frozenset(normalize_runtime_identifier(name) for name in columns)
        )
        identity_columns = tuple(
            (name, values)
            for name, values in columns.items()
            if normalize_runtime_identifier(name) in image_fields
        )
        object_fields = tuple(
            dict.fromkeys(
                (
                    *((object_id_field,) if object_id_field else ()),
                    *MeasurementRowAxisField.object_id_field_names(),
                )
            )
        )
        object_columns = tuple(
            columns[name] for name in object_fields if name in columns
        )
        qualifiers = tuple(
            (name, columns[name])
            for name in dict.fromkeys(qualifier_field_names)
            if name in columns
        )
        object_names = columns.get(MeasurementRowAxisField.OBJECT_NAME.value)
        feature_names, value_names = self._long_form_fields(columns)
        feature_fields = tuple(columns[name] for name in feature_names)
        value_fields = tuple(columns[name] for name in value_names)
        normalized_features = None
        if feature_fields:
            if self.required_subjects is None:
                normalized_features = np.fromiter(
                    (
                        (
                            MEASUREMENT_SPARSE_CELL
                            if is_structural_missing_measurement_cell(value)
                            else str(value)
                        )
                        for value in feature_fields[0]
                    ),
                    dtype=object,
                    count=row_count,
                )
            else:
                normalized_features = np.empty(row_count, dtype=object)
        cohorts: dict[tuple[str, tuple[tuple[str, object], ...]], list[int]] = {}
        labels = np.full(row_count, missing_cell, dtype=object)
        for index in range(row_count):
            name = (
                None
                if object_names is None
                else MeasurementRowObjectName.normalize_value(object_names[index])
            )
            subject = name or default_subject
            scope = MeasurementRowOwnership(object_name=name).scope(default_scope)
            if not self._admit_subject(subject, scope):
                continue
            if self.required_subjects is not None:
                if normalized_features is not None:
                    value = feature_fields[0][index]
                    normalized_features[index] = (
                        MEASUREMENT_SPARSE_CELL
                        if is_structural_missing_measurement_cell(value)
                        else str(value)
                    )
            for values in object_columns:
                label = measurement_object_label_value(values[index])
                if label is not None:
                    labels[index] = label
                    break
            qualification = tuple(
                (name, values[index])
                for name, values in qualifiers
                if not is_structural_missing_measurement_cell(values[index])
            )
            cohorts.setdefault((subject, qualification), []).append(index)
        for (subject, qualification), selected in cohorts.items():
            indexes = np.asarray(selected, dtype=np.intp)
            output = {
                name: ColumnarRows.column_array(values)[indexes]
                for name, values in identity_columns
            }
            if object_columns:
                output[self.row_identity_contract.object_identity_output_field] = (
                    labels[indexes]
                )
            identity_names = tuple(output)
            first_present: dict[str, tuple[int, int]] = {}

            def admit(
                name: str, values: Sequence[object], mask: np.ndarray | None = None
            ) -> None:
                projected = project_feature_name(name, qualification)
                incoming = ColumnarRows.column_array(values)[indexes]
                if mask is not None:
                    incoming = incoming.astype(object, copy=True)
                    incoming[~mask[indexes]] = missing_cell
                first = next(
                    (
                        position
                        for position, value in enumerate(incoming)
                        if not is_structural_missing_measurement_cell(value)
                    ),
                    None,
                )
                if first is None:
                    return
                first_present.setdefault(projected, (first, len(first_present)))
                if projected in output:
                    previous = output[projected]
                    for position, value in enumerate(incoming):
                        if is_structural_missing_measurement_cell(value):
                            continue
                        if not is_structural_missing_measurement_cell(
                            previous[position]
                        ) and not _measurement_sparse_cell_values_equal(
                            previous[position], value
                        ):
                            raise ValueError(
                                f"Conflicting measurement values for field {projected!r}."
                            )
                        previous[position] = value
                else:
                    output[projected] = incoming

            for name, values in feature_columns:
                admit(name, values)
            if feature_fields:
                names = normalized_features
                values = value_fields[0]
                feature_names = tuple(
                    dict.fromkeys(
                        value
                        for value in names[indexes]
                        if not is_structural_missing_measurement_cell(value)
                    )
                )
                for name in feature_names:
                    if not name:
                        raise ValueError(
                            "Long-form measurement row has an empty feature name."
                        )
                    mask = names == name
                    for index in indexes[mask[indexes]]:
                        if is_structural_missing_measurement_cell(values[index]):
                            raise ValueError(
                                f"Long-form measurement feature {name!r} has no value."
                            )
                    admit(name, values, mask)
            output = {
                name: output[name]
                for name in (
                    *identity_names,
                    *sorted(
                        (name for name in output if name not in identity_names),
                        key=lambda name: first_present.get(
                            name, (len(indexes), len(first_present))
                        ),
                    ),
                )
            }
            batch = MeasurementSparseColumnarRows(
                MappingProxyType(output),
                fields=tuple(FieldSpec(name, required=False) for name in output),
                missing_cell=missing_cell,
            )
            self._batches_by_subject.setdefault(subject, []).append(batch)

    def columnar_rows_by_subject(
        self, *, subjects: frozenset[str] | None = None
    ) -> dict[str, ColumnarRows]:
        """Coalesce admitted batches in first-seen subject and identity order.

        Cross-batch duplicate values are validated by the columnar join when the
        completed table is consumed, before any exporter can render or persist it.
        """
        result: dict[str, ColumnarRows] = {}
        for subject, batches in self._batches_by_subject.items():
            if subjects is not None and subject not in subjects:
                continue
            names = frozenset(name for value in batches for name in value.columns)
            image_names = self.row_identity_contract.selected_image_identity_fields(
                frozenset(normalize_runtime_identifier(name) for name in names)
            )
            identities = tuple(
                dict.fromkeys(
                    (
                        *(
                            name
                            for value in batches
                            for name in value.columns
                            if normalize_runtime_identifier(name) in image_names
                        ),
                        *(
                            (self.row_identity_contract.object_identity_output_field,)
                            if self.row_identity_contract.object_identity_output_field
                            in names
                            else ()
                        ),
                    )
                )
            )
            result[subject] = MeasurementSparseColumnarRows.from_columnar_batches(
                batches, identity_fields=identities
            )
        return result

    def row_mappings_by_subject(self) -> dict[str, tuple[Mapping[str, object], ...]]:
        """Materialize mappings only for consumers requesting the row boundary."""
        return {
            subject: tuple(rows.iter_row_mappings())
            for subject, rows in self.columnar_rows_by_subject().items()
        }

    def object_subjects(self) -> tuple[str, ...]:
        """Return subjects carrying object-scoped measurement rows."""
        return tuple(self._object_subjects)

    @staticmethod
    def _columnar_rows(
        rows: Sequence[object],
        missing_cell: object,
    ) -> ColumnarRows:
        del missing_cell
        if not rows:
            return MeasurementSparseColumnarRows(
                MappingProxyType({}),
                fields=(),
            )
        row_type = type(rows[0])
        if is_dataclass(row_type):
            return DataclassMeasurementColumnarRows(rows, row_type=row_type)
        raise TypeError(
            "Measurement row mappings require an explicit schema-bearing "
            "ColumnarRows carrier."
        )


def _measurement_sparse_cell_values_equal(left: object, right: object) -> bool:
    """Return scalar truth for equality without treating arrays as ambiguous."""
    if left is right:
        return True
    try:
        if np.array_equal(
            np.asarray(left),
            np.asarray(right),
            equal_nan=True,
        ):
            return True
    except (TypeError, ValueError):
        pass
    try:
        equality = left == right
    except Exception:
        return False
    if isinstance(equality, bool):
        return equality
    if hasattr(equality, "all"):
        try:
            return bool(equality.all())
        except Exception:
            return False
    try:
        return bool(equality)
    except Exception:
        return False


class MeasurementRowsAxisProjection(
    NominalTypeStrategyFamilyMixin,
    ABC,
    metaclass=AutoRegisterMeta,
):
    """Project measurement rows along the OpenHCS runtime slice axis."""

    @classmethod
    def from_rows(
        cls,
        rows: Sequence[object] | ColumnarRows,
    ) -> "MeasurementRowsAxisProjection":
        projection_type = cls.strategy_types_for_nominal_value(rows)[0]
        return cast(MeasurementRowsAxisProjection, projection_type(rows=rows))

    @staticmethod
    def row_has_axis(row: Mapping[str, object]) -> bool:
        return MeasurementRowAxisField.SLICE_INDEX.value in row

    @property
    @abstractmethod
    def has_rows(self) -> bool:
        """Return whether this projection has row payloads to project."""

    @property
    @abstractmethod
    def row_count(self) -> int:
        """Return the number of measurement rows represented by this projection."""

    @property
    @abstractmethod
    def columns(self) -> Mapping[str, Sequence[Any]]:
        """Return column vectors when the underlying rows are columnar."""

    @abstractmethod
    def declares_axis_field(self, axis: MeasurementRowAxisField) -> bool:
        """Return whether the row representation declares ``axis``."""

    @abstractmethod
    def has_axisless_rows(self, axis: MeasurementRowAxisField) -> bool:
        """Return whether any represented row omits an exact ``axis`` value."""

    @property
    def has_axis(self) -> bool:
        """Return whether rows declare the runtime slice coordinate."""
        return self.declares_axis_field(MeasurementRowAxisField.SLICE_INDEX)

    @abstractmethod
    def present_axis_values(self, field_name: str) -> tuple[int, ...]:
        """Return present integer value domain for one measurement row-axis field."""

    @abstractmethod
    def project_runtime_slice_index(
        self,
        slice_index: int,
    ) -> Sequence[object] | ColumnarRows:
        """Return rows stamped into one runtime slice."""

    @abstractmethod
    def remap_runtime_slice_indices(
        self,
        values: Mapping[int, int],
        *,
        axisless_value: int | None = None,
    ) -> Sequence[object] | ColumnarRows:
        """Return rows with declared runtime-slice values remapped exactly."""


@dataclass(frozen=True, slots=True)
class SequenceMeasurementRowsAxisProjection(MeasurementRowsAxisProjection):
    """Row-axis projection for row-sequence measurement payloads."""

    value_type = Sequence
    rows: Sequence[object]

    @property
    def has_rows(self) -> bool:
        return bool(self.rows)

    @property
    def row_count(self) -> int:
        return len(self.rows)

    @property
    def columns(self) -> Mapping[str, Sequence[Any]]:
        return MappingProxyType({})

    def declares_axis_field(self, axis: MeasurementRowAxisField) -> bool:
        return any(axis.value in measurement_row_mapping(row) for row in self.rows)

    def has_axisless_rows(self, axis: MeasurementRowAxisField) -> bool:
        return any(
            measurement_axis_integer_value(
                measurement_row_mapping(row).get(axis.value),
                axis,
            )
            is None
            for row in self.rows
        )

    def project_runtime_slice_index(
        self,
        slice_index: int,
    ) -> Sequence[object]:
        """Stamp runtime-slice index while preserving row dataclass types."""
        slice_index_field = MeasurementRowAxisField.SLICE_INDEX.value
        projected_rows: list[object] = []
        for row in self.rows:
            row_mapping = measurement_row_mapping(row)
            if (
                is_dataclass(row)
                and slice_index_field in row_mapping
                and slice_index_field in dataclass_init_field_names(type(row))
            ):
                projected_rows.append(
                    dataclass_replace(row, **{slice_index_field: int(slice_index)})
                )
                continue
            projected_row = dict(row_mapping)
            projected_row[slice_index_field] = int(slice_index)
            projected_rows.append(projected_row)
        return projected_rows

    def remap_runtime_slice_indices(
        self,
        values: Mapping[int, int],
        *,
        axisless_value: int | None = None,
    ) -> Sequence[object]:
        slice_index_field = MeasurementRowAxisField.SLICE_INDEX.value
        projected_rows: list[object] = []
        for row in self.rows:
            row_mapping = measurement_row_mapping(row)
            slice_index = measurement_axis_integer_value(
                row_mapping.get(slice_index_field),
                MeasurementRowAxisField.SLICE_INDEX,
            )
            if slice_index is None:
                if axisless_value is None:
                    projected_rows.append(row)
                    continue
                projected_row = dict(row_mapping)
                projected_row[slice_index_field] = int(axisless_value)
                projected_rows.append(projected_row)
                continue
            if slice_index not in values:
                raise ValueError(
                    "Measurement row runtime-slice remapping has no value for "
                    f"slice_index={slice_index}."
                )
            projected_index = int(values[slice_index])
            if (
                is_dataclass(row)
                and slice_index_field in row_mapping
                and slice_index_field in dataclass_init_field_names(type(row))
            ):
                projected_rows.append(
                    dataclass_replace(row, **{slice_index_field: projected_index})
                )
                continue
            projected_row = dict(row_mapping)
            projected_row[slice_index_field] = projected_index
            projected_rows.append(projected_row)
        return projected_rows

    def present_axis_values(self, field_name: str) -> tuple[int, ...]:
        """Return present integer axis values for one measurement row field."""
        axis = MeasurementRowAxisField(field_name)
        return tuple(
            dict.fromkeys(
                integer_value
                for row in (measurement_row_mapping(row) for row in self.rows)
                for integer_value in (
                    measurement_axis_integer_value(row.get(field_name), axis),
                )
                if integer_value is not None
            )
        )


def dataclass_init_field_names(row_type: type[object]) -> frozenset[str]:
    """Return constructor-backed dataclass field names for row replacement."""
    return frozenset(field.name for field in dataclass_fields(row_type) if field.init)


@dataclass(frozen=True, slots=True)
class ColumnarMeasurementRowsAxisProjection(MeasurementRowsAxisProjection):
    """Row-axis projection for nominal columnar measurement payloads."""

    value_type = ColumnarRows
    rows: ColumnarRows
    _columns: Mapping[str, Sequence[Any]] = field(
        init=False,
        repr=False,
        compare=False,
    )

    def __post_init__(self) -> None:
        columns = self.rows.columns
        if isinstance(columns, Mapping) and all(
            isinstance(column, str) for column in columns
        ):
            object.__setattr__(self, "_columns", columns)
            return
        object.__setattr__(
            self,
            "_columns",
            MappingProxyType(
                {
                    str(column): columnar_row_values(self.rows, str(column))
                    for column in self.rows.columns
                }
            ),
        )

    @property
    def has_rows(self) -> bool:
        return self.rows.row_count() > 0

    @property
    def row_count(self) -> int:
        return self.rows.row_count()

    @property
    def columns(self) -> Mapping[str, Sequence[Any]]:
        return self._columns

    def declares_axis_field(self, axis: MeasurementRowAxisField) -> bool:
        return axis.value in self.columns

    @staticmethod
    def _integer_column(values: Sequence[object]) -> np.ndarray | None:
        """Admit a numeric integer vector without retaining mutable source state."""
        column = np.asarray(values)
        return column if column.ndim == 1 and column.dtype.kind in "biu" else None

    def has_axisless_rows(self, axis: MeasurementRowAxisField) -> bool:
        values = self.columns.get(axis.value)
        if values is None:
            return self.has_rows
        if self._integer_column(values) is not None:
            return False
        return any(
            measurement_axis_integer_value(value, axis) is None for value in values
        )

    def present_axis_values(self, field_name: str) -> tuple[int, ...]:
        """Return present integer axis values in their source encounter order."""
        values = self.columns.get(field_name, ())
        integers = self._integer_column(values)
        if integers is not None:
            domain, first_positions = np.unique(integers, return_index=True)
            return tuple(int(value) for value in domain[np.argsort(first_positions)])
        return measurement_axis_integer_domain(
            values, MeasurementRowAxisField(field_name)
        )

    def project_runtime_slice_index(
        self,
        slice_index: int,
    ) -> ColumnarRows:
        slice_index_field = MeasurementRowAxisField.SLICE_INDEX.value
        return MeasurementProjectedColumnarRows(
            ColumnarRowColumnOverlay(
                self.columns,
                MappingProxyType(
                    {slice_index_field: (int(slice_index),) * self.rows.row_count()}
                ),
            ),
            fields=projected_columnar_fields(
                self.rows,
                FieldSpec(slice_index_field, int),
            ),
            declared_object_measurement_domain_covered=(
                self.rows.covers_declared_object_measurement_domain
            ),
            object_row_identity=self.rows.object_row_identity,
        )

    def remap_runtime_slice_indices(
        self,
        values: Mapping[int, int],
        *,
        axisless_value: int | None = None,
    ) -> ColumnarRows:
        slice_index_field = MeasurementRowAxisField.SLICE_INDEX.value
        if slice_index_field not in self.columns:
            if axisless_value is None:
                return self.rows
            return self.project_runtime_slice_index(axisless_value)
        source_values = self.columns[slice_index_field]
        integers = self._integer_column(source_values)
        if integers is not None:
            domain, inverse = np.unique(integers, return_inverse=True)
            remapped = []
            for value in domain:
                slice_index = int(value)
                if slice_index not in values:
                    raise ValueError(
                        "Measurement row runtime-slice remapping has no value for "
                        f"slice_index={slice_index!r}."
                    )
                remapped.append(int(values[slice_index]))
            integer_bounds = np.iinfo(np.int64)
            dtype = (
                np.int64
                if all(
                    integer_bounds.min <= value <= integer_bounds.max
                    for value in remapped
                )
                else object
            )
            projected_values = np.asarray(remapped, dtype=dtype)[inverse]
        else:
            projected_values = []
            for value in self.columns[slice_index_field]:
                if is_structural_missing_measurement_cell(value):
                    projected_values.append(
                        value if axisless_value is None else int(axisless_value)
                    )
                    continue
                slice_index = measurement_axis_integer_value(
                    value,
                    MeasurementRowAxisField.SLICE_INDEX,
                )
                if slice_index is None:
                    if axisless_value is None:
                        projected_values.append(value)
                        continue
                    projected_values.append(int(axisless_value))
                    continue
                if slice_index not in values:
                    raise ValueError(
                        "Measurement row runtime-slice remapping has no value for "
                        f"slice_index={slice_index!r}."
                    )
                projected_values.append(int(values[slice_index]))
        return MeasurementProjectedColumnarRows(
            ColumnarRowColumnOverlay(
                self.columns,
                MappingProxyType({slice_index_field: projected_values}),
            ),
            fields=projected_columnar_fields(
                self.rows,
                FieldSpec(slice_index_field, int),
            ),
            declared_object_measurement_domain_covered=(
                self.rows.covers_declared_object_measurement_domain
            ),
            object_row_identity=self.rows.object_row_identity,
        )


def measurement_row_object_name(row: Mapping[str, object]) -> str | None:
    """Return the object owner encoded on one measurement row."""
    return cast(str | None, MeasurementRowObjectName.value_from_row(row))


def measurement_row_source_image_name(row: Mapping[str, object]) -> str | None:
    """Return the source-image owner encoded on one measurement row."""
    return cast(str | None, MeasurementRowSourceImageName.value_from_row(row))


def measurement_object_label_value(value: object) -> int | None:
    """Return the integer object label represented by one scalar value."""
    if value is None:
        return None
    if isinstance(value, bool):
        return int(value)
    if isinstance(value, (int, np.integer)):
        return int(value)
    if isinstance(value, (float, np.floating)):
        if not np.isfinite(value):
            return None
        integer = int(value)
        return integer if float(integer) == float(value) else None
    if isinstance(value, str):
        stripped = value.strip()
        if not stripped:
            return None
        signless = stripped[1:] if stripped[:1] in ("+", "-") else stripped
        if signless.isdecimal():
            return int(stripped)
    return MeasurementScalarLiteral(value).integer_value


def measurement_object_label(
    row: Mapping[str, object],
    *,
    object_id_field: str | None = None,
) -> int | None:
    """Return the resolved object label encoded on a measurement row."""
    return cast(
        int | None,
        MeasurementRowObjectLabel.value_from_row(
            row,
            object_id_field=object_id_field,
        ),
    )


def measurement_row_has_object_identity(
    row: Mapping[str, object],
    *,
    object_id_field: str | None = None,
) -> bool:
    """Return whether a measurement row carries resolved object identity."""
    return measurement_object_label(row, object_id_field=object_id_field) is not None


def measurement_row_has_long_form_measurement_fields(
    row: Mapping[str, object],
) -> bool:
    """Return whether a row carries long-form measurement feature/value fields."""
    if any(
        field in row for field in MeasurementRowAxisField.feature_name_field_names()
    ) and any(field in row for field in MeasurementRowValueField.field_names()):
        return True
    normalized_fields = frozenset(
        normalize_runtime_identifier(str(field)) for field in row
    )
    return bool(
        normalized_fields
        & MeasurementRowAxisField.normalized_feature_name_field_names()
    ) and bool(normalized_fields & MeasurementRowValueField.normalized_field_names())


def measurement_row_declared_field_value(
    row: Mapping[str, object],
    field_name: str,
    normalized_fields: Mapping[str, str] | None,
) -> object | None:
    """Return a declared row value using cached normalized fields when available."""
    resolved_field = field_name if field_name in row else None
    if resolved_field is None:
        if normalized_fields is None:
            normalized_fields = normalized_measurement_row_fields_for_row(row)
        resolved_field = normalized_fields.get(normalize_runtime_identifier(field_name))
    if resolved_field is None:
        return None
    value = row[resolved_field]
    return None if is_structural_missing_measurement_cell(value) else value


@dataclass(frozen=True, slots=True)
class MeasurementRowQualifier:
    """One typed ownership qualifier attached to a measurement row."""

    field_name: str
    value: str

    @classmethod
    def optional(
        cls,
        *,
        field_name: str,
        value: str | None,
    ) -> "MeasurementRowQualifier | None":
        if value is None:
            return None
        normalized = value.strip()
        if not normalized:
            raise ValueError(f"{field_name} cannot be empty.")
        return cls(field_name=field_name, value=normalized)

    def apply(self, row: MutableMapping[str, object]) -> None:
        row[self.field_name] = self.value

    def field_spec(self) -> FieldSpec:
        """Return the output field declared by this string qualifier."""
        return FieldSpec(self.field_name, str)


@dataclass(frozen=True, slots=True)
class MeasurementRowOwnership:
    """Shared object/source ownership qualifiers for measurement rows."""

    object_name: str | None = None
    source_image_name: str | None = None

    def scope(self, default: MeasurementScope) -> MeasurementScope:
        """Return the semantic row scope declared by this ownership."""

        if self.object_name is not None:
            return MeasurementScope.OBJECT
        if default is not MeasurementScope.ARTIFACT:
            return default
        if self.source_image_name is not None:
            return MeasurementScope.IMAGE
        return default

    @staticmethod
    def rows_declare_source_image(field_names: Iterable[str]) -> bool:
        """Return whether row fields own source-image qualification."""

        return MeasurementRowAxisField.SOURCE_IMAGE_NAME.value in field_names

    @property
    def qualifiers(self) -> tuple[MeasurementRowQualifier, ...]:
        return tuple(
            qualifier
            for qualifier in (
                MeasurementRowQualifier.optional(
                    field_name=MeasurementRowAxisField.OBJECT_NAME.value,
                    value=self.object_name,
                ),
                MeasurementRowQualifier.optional(
                    field_name=MeasurementRowAxisField.SOURCE_IMAGE_NAME.value,
                    value=self.source_image_name,
                ),
            )
            if qualifier is not None
        )

    def annotate_rows(
        self, rows: Sequence[object] | ColumnarRows
    ) -> Sequence[object] | ColumnarRows:
        """Attach ownership qualifiers, copying only non-mutable row values."""
        qualifiers = self.qualifiers
        if not qualifiers:
            return rows
        if isinstance(rows, ColumnarRows):
            return QualifiedMeasurementColumnarRows(rows, qualifiers)
        if (
            rows
            and is_dataclass(type(rows[0]))
            and all(type(row) is type(rows[0]) for row in rows)
        ):
            return QualifiedMeasurementColumnarRows(
                DataclassMeasurementColumnarRows(rows),
                qualifiers,
            )
        return [self.annotate_row(row, qualifiers=qualifiers) for row in rows]

    def annotate_row(
        self,
        row: object,
        *,
        qualifiers: Sequence[MeasurementRowQualifier] | None = None,
    ) -> Mapping[str, object]:
        if qualifiers is None:
            qualifiers = self.qualifiers
        annotated_row: MutableMapping[str, object] = (
            row
            if isinstance(row, MutableMapping)
            else dict(measurement_row_mapping(row))
        )
        for qualifier in qualifiers:
            qualifier.apply(annotated_row)
        return annotated_row


@dataclass(slots=True)
class MeasurementColumnarRowsView(ColumnarRows, ABC):
    """Base for columnar measurement views that derive columns from another table."""

    _columns: Mapping[str, Sequence[object]] = field(
        init=False,
        repr=False,
        compare=False,
    )
    _fields: tuple[FieldSpec, ...] = field(
        init=False,
        repr=False,
        compare=False,
    )
    object_row_identity: MeasurementObjectRowIdentity | None = field(
        default=None,
        init=False,
    )

    columns: ClassVar[AliasProperty[Mapping[str, Sequence[object]]]] = AliasProperty(
        "_columns"
    )
    fields: ClassVar[AliasProperty[tuple[FieldSpec, ...]]] = AliasProperty("_fields")

    def __len__(self) -> int:
        return column_mapping_row_count(self._columns)

    def iter_row_mappings(self) -> Iterator[Mapping[str, object]]:
        columns = tuple(str(column) for column in self.columns)
        column_values = tuple(self.column_values(column) for column in columns)
        for values in zip(*column_values, strict=True):
            yield {
                column: value
                for column, value in zip(columns, values, strict=True)
                if not is_structural_missing_measurement_cell(value)
            }


def columnar_row_count(rows: ColumnarRows) -> int:
    """Return row count for a nominal columnar payload."""
    return rows.row_count()


@dataclass(frozen=True, slots=True)
class ConcatenatedColumnarRowColumns(Mapping[str, Sequence[object]]):
    """Lazy mapping over columns concatenated from multiple columnar batches."""

    row_batches: tuple[ColumnarRows, ...]
    column_names: tuple[str, ...]
    _batch_columns: tuple[Mapping[str, object], ...] = field(
        init=False,
        repr=False,
        compare=False,
    )
    _batch_row_counts: tuple[int, ...] = field(
        init=False,
        repr=False,
        compare=False,
    )
    _column_cache: dict[str, Sequence[object]] = field(
        default_factory=dict,
        init=False,
        repr=False,
        compare=False,
    )

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "_batch_columns",
            tuple(
                MappingProxyType({str(column): column for column in row_batch.columns})
                for row_batch in self.row_batches
            ),
        )
        object.__setattr__(
            self,
            "_batch_row_counts",
            tuple(columnar_row_count(row_batch) for row_batch in self.row_batches),
        )

    @classmethod
    def from_row_batches(
        cls,
        row_batches: tuple[ColumnarRows, ...],
        fields: tuple[FieldSpec, ...],
    ) -> "ConcatenatedColumnarRowColumns":
        return cls(
            row_batches=row_batches,
            column_names=tuple(field_spec.name for field_spec in fields),
        )

    def __getitem__(self, column_name: str) -> Sequence[object]:
        if column_name not in self.column_names:
            raise KeyError(column_name)
        cached = self._column_cache.get(column_name)
        if cached is not None:
            return cached
        column_batches = tuple(
            (row_batch, batch_columns.get(column_name), row_count)
            for row_batch, batch_columns, row_count in zip(
                self.row_batches,
                self._batch_columns,
                self._batch_row_counts,
                strict=True,
            )
        )
        dense_columns = None
        if all(
            column_key is not None or not row_count
            for _row_batch, column_key, row_count in column_batches
        ):
            dense_columns = tuple(
                ColumnarRows.column_array(columnar_row_values(row_batch, column_key))
                for row_batch, column_key, _row_count in column_batches
                if column_key is not None
            )
            # Preserve the sparse join's object representation at a physical
            # dtype boundary, including declarations carried by empty batches.
            if not dense_columns or any(
                column.dtype != dense_columns[0].dtype for column in dense_columns[1:]
            ):
                dense_columns = None
        if dense_columns is not None:
            values = np.concatenate(dense_columns)
        else:
            values = np.empty(sum(self._batch_row_counts), dtype=object)
            values.fill(MEASUREMENT_SPARSE_CELL)
            row_offset = 0
            for row_batch, row_count, batch_columns in zip(
                self.row_batches,
                self._batch_row_counts,
                self._batch_columns,
                strict=True,
            ):
                column_key = batch_columns.get(column_name)
                if column_key is not None:
                    values[row_offset : row_offset + row_count] = columnar_row_values(
                        row_batch,
                        column_key,
                    )
                row_offset += row_count
        self._column_cache[column_name] = values
        return values

    def __contains__(self, column_name: object) -> bool:
        return column_name in self.column_names

    def __iter__(self):
        return iter(self.column_names)

    def __len__(self) -> int:
        return len(self.column_names)


@dataclass(slots=True)
class ConcatenatedColumnarRows(MeasurementColumnarRowsView):
    """Columnar table view over multiple columnar row batches."""

    row_batches: tuple[ColumnarRows, ...]

    def __post_init__(self) -> None:
        self.object_row_identity = ColumnarRows.common_object_row_identity(
            self.row_batches
        )
        self._fields = FieldSpec.merge_exact(
            (row_batch.fields for row_batch in self.row_batches),
            context="concatenated columnar row fields",
        )
        self._columns = ConcatenatedColumnarRowColumns.from_row_batches(
            self.row_batches,
            self._fields,
        )
        self.validate_fields()

    def __len__(self) -> int:
        return sum(columnar_row_count(row_batch) for row_batch in self.row_batches)

    def row_count(self) -> int:
        return len(self)

    def column_value_segments(
        self, column: str
    ) -> Iterable[tuple[int, Sequence[object]]]:
        if column not in self.columns:
            raise KeyError(column)
        cached = self.columns._column_cache.get(column)
        if cached is not None:
            yield 0, cached
            return
        offset = 0
        for row_batch in self.row_batches:
            if column in row_batch.columns:
                for local_offset, values in row_batch.column_value_segments(column):
                    yield offset + local_offset, values
            offset += row_batch.row_count()

    def bounded_column_values(self, column: str, row_stop: int) -> Sequence[object]:
        cached = self.columns._column_cache.get(column)
        if cached is not None:
            return cached[:row_stop]
        values = np.empty(min(max(0, row_stop), self.row_count()), dtype=object)
        values.fill(MEASUREMENT_SPARSE_CELL)
        for offset, segment in self.column_value_segments(column):
            if offset >= len(values):
                break
            count = min(len(segment), len(values) - offset)
            values[offset : offset + count] = segment[:count]
        return values

    def columnar_row_batches(
        self,
    ) -> Iterable[tuple[int, Mapping[str, Sequence[object]]]]:
        offset = 0
        for row_batch in self.row_batches:
            for count, columns in row_batch.columnar_row_batches():
                yield count, {
                    name: (
                        self.columns._column_cache[name][offset : offset + count]
                        if name in self.columns._column_cache
                        else columns[name]
                    )
                    for name in self.columns
                    if name in self.columns._column_cache or name in columns
                }
                offset += count

    @property
    def covers_declared_object_measurement_domain(self) -> bool:
        """Return whether every concatenated batch covers its declared domain."""
        return bool(self.row_batches) and all(
            row_batch.covers_declared_object_measurement_domain
            for row_batch in self.row_batches
        )

    def row_mappings(self) -> tuple[Mapping[str, object], ...]:
        return tuple(self.iter_row_mappings())

    def iter_row_mappings(self):
        for row_batch in self.row_batches:
            yield from row_batch.iter_row_mappings()


@dataclass(frozen=True, slots=True)
class ConcatenatedMeasurementRowsAxisProjection(ColumnarMeasurementRowsAxisProjection):
    """Project a concatenated table without erasing its batch schemas."""

    value_type = ConcatenatedColumnarRows
    rows: ConcatenatedColumnarRows

    def project_runtime_slice_index(
        self,
        slice_index: int,
    ) -> ConcatenatedColumnarRows:
        return ConcatenatedColumnarRows(
            tuple(
                MeasurementRowsAxisProjection.from_rows(
                    row_batch
                ).project_runtime_slice_index(slice_index)
                for row_batch in self.rows.row_batches
            )
        )

    def remap_runtime_slice_indices(
        self,
        values: Mapping[int, int],
        *,
        axisless_value: int | None = None,
    ) -> ConcatenatedColumnarRows:
        return ConcatenatedColumnarRows(
            tuple(
                MeasurementRowsAxisProjection.from_rows(
                    row_batch
                ).remap_runtime_slice_indices(
                    values,
                    axisless_value=axisless_value,
                )
                for row_batch in self.rows.row_batches
            )
        )


@dataclass(slots=True)
class DataclassMeasurementColumnarRows(ColumnarRows):
    """Columnar view over homogeneous dataclass measurement rows."""

    rows: Sequence[object]
    row_type: type[object] | None = None
    _columns: Mapping[str, Sequence[object]] = field(
        init=False,
        repr=False,
        compare=False,
    )
    columns: ClassVar[AliasProperty[Mapping[str, Sequence[object]]]] = AliasProperty(
        "_columns"
    )
    _fields: tuple[FieldSpec, ...] = field(
        init=False,
        repr=False,
        compare=False,
    )
    fields: ClassVar[AliasProperty[tuple[FieldSpec, ...]]] = AliasProperty("_fields")

    def __post_init__(self) -> None:
        row_type = self.row_type
        if row_type is None:
            if not self.rows:
                raise TypeError(
                    "DataclassMeasurementColumnarRows requires row_type for zero rows."
                )
            row_type = type(self.rows[0])
        if not is_dataclass(row_type):
            raise TypeError(
                "DataclassMeasurementColumnarRows requires dataclass rows, "
                f"got {row_type.__name__}."
            )
        if not all(type(row) is row_type for row in self.rows):
            raise TypeError(
                "DataclassMeasurementColumnarRows requires homogeneous row types."
            )
        self.row_type = row_type
        self._fields = FieldSpec.from_dataclass_type(row_type)
        column_names = tuple(field_spec.name for field_spec in self._fields)
        row_mappings = tuple(measurement_row_mapping(row) for row in self.rows)
        self._columns = {
            column_name: tuple(row[column_name] for row in row_mappings)
            for column_name in column_names
        }
        self.validate_fields()

    def __len__(self) -> int:
        return len(self.rows)

    def __iter__(self):
        yield from self.iter_row_mappings()

    def iter_row_mappings(self):
        columns = self._columns
        for row_index in range(len(self)):
            yield {
                field_name: values[row_index] for field_name, values in columns.items()
            }


@dataclass(slots=True)
class QualifiedMeasurementColumnarRows(MeasurementColumnarRowsView):
    """Columnar measurement rows with table-ownership qualifiers attached."""

    rows: ColumnarRows
    qualifiers: tuple[MeasurementRowQualifier, ...]

    def __post_init__(self) -> None:
        self.object_row_identity = self.rows.object_row_identity
        columns = dict(self.rows.columns)
        row_count = column_mapping_row_count(columns)
        qualifier_fields = tuple(
            qualifier.field_spec() for qualifier in self.qualifiers
        )
        self._fields = FieldSpec.merge_exact(
            (self.rows.fields, qualifier_fields),
            context="qualified columnar row fields",
        )
        for qualifier in self.qualifiers:
            columns[qualifier.field_name] = (qualifier.value,) * row_count
        self._columns = columns
        self.validate_fields()

    @property
    def covers_declared_object_measurement_domain(self) -> bool:
        """Return whether the owned row carrier still covers its object domain."""
        return self.rows.covers_declared_object_measurement_domain

    def __iter__(self):
        yield from self.iter_row_mappings()

    def iter_row_mappings(self):
        columns = self._columns
        for row_index in range(len(self)):
            yield {
                field_name: values[row_index] for field_name, values in columns.items()
            }


def measurement_rows_with_source_provenance(
    rows: ColumnarRows,
    provenance: SourceImageProvenance,
) -> ColumnarRows:
    """Attach exact source coordinates to measurement rows.

    Runtime-plane provenance owns biological coordinates. Rows carrying the
    canonical ``slice_index`` receive the matching plane's coordinates; axisless
    rows receive only values common to the complete represented stack. Existing
    producer-declared biological coordinate columns require exact consistency.
    Producer-declared source-image ownership is retained, with runtime provenance
    filling only missing source-image values.
    """

    row_count = rows.row_count()
    if row_count == 0 or not provenance.has_values:
        return rows

    projection = MeasurementRowsAxisProjection.from_rows(rows)
    if not isinstance(projection, ColumnarMeasurementRowsAxisProjection):
        raise TypeError(
            "Measurement source-provenance projection requires schema-bearing "
            "ColumnarRows."
        )
    source_provenance = provenance.with_common_scalar_identity_from_planes()
    slice_field = MeasurementRowAxisField.SLICE_INDEX.value
    slice_values = projection.columns.get(slice_field)
    coordinate_columns: dict[str, tuple[object, ...]] = {}

    def metadata_for_row(row_index: int):
        if slice_values is None:
            return source_provenance.source_component_metadata
        slice_index = measurement_axis_integer_value(
            slice_values[row_index],
            MeasurementRowAxisField.SLICE_INDEX,
        )
        if slice_index is None:
            return source_provenance.source_component_metadata
        if slice_index < 0 or (
            source_provenance.source_plane_count
            and slice_index >= source_provenance.source_plane_count
        ):
            raise ValueError(
                "Measurement row source coordinate projection has "
                f"slice_index={slice_index}, but provenance declares "
                f"{source_provenance.source_plane_count} runtime plane(s)."
            )
        return source_provenance.component_metadata_for_plane(slice_index)

    metadata_by_row = tuple(metadata_for_row(index) for index in range(row_count))
    for component in AllComponents:
        values = tuple(
            (
                MEASUREMENT_SPARSE_CELL
                if (
                    value := source_component_metadata_value(
                        metadata_by_row[row_index] or {},
                        component,
                    )
                )
                is None
                else value
            )
            for row_index in range(row_count)
        )
        if not all(is_structural_missing_measurement_cell(value) for value in values):
            coordinate_columns[component.value] = values

    def source_names_for_row(row_index: int) -> tuple[str, ...]:
        if slice_values is None:
            return source_provenance.represented_source_image_names
        slice_index = measurement_axis_integer_value(
            slice_values[row_index],
            MeasurementRowAxisField.SLICE_INDEX,
        )
        if slice_index is None:
            return source_provenance.represented_source_image_names
        return source_provenance.source_image_names_for_plane(slice_index)

    overlay_columns: dict[str, Sequence[object]] = {}
    added_fields: list[FieldSpec] = []
    for field_name, projected_values in coordinate_columns.items():
        existing_values = projection.columns.get(field_name)
        if existing_values is None:
            overlay_columns[field_name] = projected_values
            added_fields.append(FieldSpec(field_name, str, required=False))
            continue
        reconciled_values: list[object] = []
        for row_index, (existing, projected) in enumerate(
            zip(existing_values, projected_values, strict=True)
        ):
            if existing is None or is_structural_missing_measurement_cell(existing):
                reconciled_values.append(projected)
                continue
            if is_structural_missing_measurement_cell(projected):
                reconciled_values.append(existing)
                continue
            if str(existing) != str(projected):
                raise ValueError(
                    "Measurement row source coordinate conflicts with runtime "
                    f"provenance for field {field_name!r}, row {row_index}: "
                    f"{existing!r} != {projected!r}."
                )
            reconciled_values.append(existing)
        overlay_columns[field_name] = tuple(reconciled_values)

    source_names = tuple(
        MEASUREMENT_SPARSE_CELL if len(names) != 1 else names[0]
        for row_index in range(row_count)
        for names in (source_names_for_row(row_index),)
    )
    if not all(is_structural_missing_measurement_cell(value) for value in source_names):
        source_field = MeasurementRowAxisField.SOURCE_IMAGE_NAME.value
        existing_source_names = projection.columns.get(source_field)
        if existing_source_names is None:
            overlay_columns[source_field] = source_names
            added_fields.append(FieldSpec(source_field, str, required=False))
        else:
            overlay_columns[source_field] = tuple(
                (
                    projected
                    if existing is None
                    or is_structural_missing_measurement_cell(existing)
                    else existing
                )
                for existing, projected in zip(
                    existing_source_names,
                    source_names,
                    strict=True,
                )
            )

    if not overlay_columns:
        return rows

    return MeasurementProjectedColumnarRows(
        ColumnarRowColumnOverlay(
            projection.columns,
            MappingProxyType(overlay_columns),
        ),
        fields=FieldSpec.merge_exact(
            (rows.fields, tuple(added_fields)),
            context="source-provenance-qualified measurement fields",
        ),
        declared_object_measurement_domain_covered=(
            rows.covers_declared_object_measurement_domain
        ),
        object_row_identity=rows.object_row_identity,
    )


class MeasurementTableRowLayout(str, Enum):
    """Nominal row layout for measurement tables."""

    LONG = "long"
    WIDE = "wide"


def measurement_row_semantic_field_names() -> frozenset[str]:
    """Return fields that identify a payload as a measurement row."""
    return (
        frozenset(field.value for field in MeasurementRowAxisField)
        | MeasurementRowValueField.field_names()
    )


def measurement_table_row_layout_from_fields(
    fields: Iterable[FieldSpec],
) -> MeasurementTableRowLayout | None:
    """Return row layout declared by table fields when fields are authoritative."""
    return _measurement_table_row_layout_from_field_names(
        tuple((field.name for field in fields))
    )


@lru_cache(maxsize=256)
def _measurement_table_row_layout_from_field_names(
    field_names_tuple: tuple[str, ...],
) -> MeasurementTableRowLayout | None:
    """Return row layout declared by field names."""
    field_names = frozenset(field_names_tuple)
    if not field_names:
        return None
    has_feature_field = bool(
        field_names & MeasurementRowAxisField.feature_name_field_names()
    )
    has_value_field = bool(field_names & MeasurementRowValueField.field_names())
    if has_feature_field and (not has_value_field):
        raise ValueError(
            f"Long-form measurement table fields must declare both a feature field and a value field, got fields {sorted(field_names)!r}."
        )
    return (
        MeasurementTableRowLayout.LONG
        if has_feature_field
        else MeasurementTableRowLayout.WIDE
    )
