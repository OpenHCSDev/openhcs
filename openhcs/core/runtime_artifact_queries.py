"""Semantic queries over typed OpenHCS runtime artifacts."""

from __future__ import annotations

from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from types import MappingProxyType
from typing import TYPE_CHECKING, Any, cast

import numpy as np

from openhcs.core.artifacts import (
    ArtifactType,
    MeasurementsArtifactType,
    MeasurementBearingArtifactType,
    RelationshipsArtifactType,
    SpatialGridArtifactType,
)
from openhcs.core.measurement_row_materialization import (
    MeasurementColumnarRowsView,
    columnar_row_values,
    measurement_row_object_name,
    measurement_rows,
    measurement_table_axis_values,
)
from openhcs.core.measurement_feature_queries import (
    IndexedObjectMeasurementLabelPlaneBinding,
    MeasurementAxisValueProjection,
    MeasurementFeatureValueIndex,
    MeasurementObjectFeatureVectorBatchQuery,
    MeasurementTableFeatureQuery,
    ColumnarMeasurementTableSchema,
    MeasurementValueIndexResult,
)
from openhcs.core.process_local_cache import BoundedCache
from openhcs.core.runtime_measurements import (
    MeasurementRowAxisField,
    MeasurementSubject,
    MeasurementScope,
    ObjectLabelMeasurementValues,
)
from openhcs.core.runtime_object_label_domains import (
    ObjectLabelPlaneDomainStrategy,
    dense_object_label_id_domain,
)
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxisProjector,
    RuntimePlaneAxisValueProjection,
)
from openhcs.core.runtime_tabular_values import measurement_row_mapping
from openhcs.core.runtime_tabular_values import (
    ColumnarRows,
)
from openhcs.core.runtime_measurements import (
    MeasurementTable,
)
from openhcs.core.runtime_object_labels import (
    ObjectLabelValue,
)
from openhcs.core.runtime_relationships import (
    ObjectRelationship,
)
from openhcs.core.runtime_spatial_grid import (
    SpatialGrid,
)

if TYPE_CHECKING:
    from openhcs.core.runtime_stores import RuntimeValueStore, StoredRuntimeValue


class RuntimeMeasurementTablesQueryCache(
    BoundedCache[
        tuple[str, str | None],
        tuple[MeasurementTable, ...],
    ]
):
    """Store-owned measurement tables for one axis and component group."""


@dataclass(frozen=True, slots=True)
class RuntimeArtifactQueryContext:
    """Execution-scope view over a RuntimeValueStore."""

    store: RuntimeValueStore
    axis_id: str
    group_key: str | None = None
    match_group: bool = False

    def __post_init__(self) -> None:
        if not self.axis_id:
            raise ValueError("RuntimeArtifactQueryContext.axis_id cannot be empty.")

    def find(
        self,
        *,
        artifact_type: ArtifactType | None = None,
        name: str | None = None,
    ) -> tuple[StoredRuntimeValue, ...]:
        """Find runtime records in this execution scope."""
        return self.store.find(
            name=name,
            artifact_type=artifact_type,
            axis_id=self.axis_id,
            group_key=self.group_key,
            match_group=self.match_group,
        )

    def resolve(
        self,
        *,
        name: str,
        artifact_type: ArtifactType,
        purpose: str = "runtime artifact",
    ) -> StoredRuntimeValue:
        """Resolve exactly one runtime record in this execution scope."""
        records = self.find(name=name, artifact_type=artifact_type)
        if not records:
            raise RuntimeError(
                f"Missing {purpose} '{name}' ({artifact_type.value}) on axis "
                f"'{self.axis_id}'."
            )
        if len(records) > 1:
            raise RuntimeError(
                f"Ambiguous {purpose} '{name}' ({artifact_type.value}) on axis "
                f"'{self.axis_id}': {runtime_record_locations(records)}."
            )
        return records[0]


def runtime_record_locations(records: Sequence[StoredRuntimeValue]) -> tuple[str, ...]:
    """Return compact runtime-record identities without formatting payload data."""
    return tuple(
        f"{record.key.scope.value_text or '<none>'}@{record.location.backend}:{record.location.path}"
        for record in records
    )


@dataclass(frozen=True, slots=True)
class MeasurementObjectQuery:
    """Query for measurement tables describing one object set."""

    object_name: str

    def __post_init__(self) -> None:
        if not self.object_name:
            raise ValueError("MeasurementObjectQuery.object_name cannot be empty.")

    def matches(self, table: MeasurementTable) -> bool:
        if table.subject.scope is MeasurementScope.OBJECT:
            return table.subject.name == self.object_name
        if isinstance(table.rows, ColumnarRows):
            return self.object_name in ColumnarMeasurementTableSchema.from_table(
                table
            ).object_names(table)
        if not _measurement_table_may_declare_object_name(table):
            return False
        return any(
            measurement_row_object_name(measurement_row_mapping(row))
            == self.object_name
            for row in measurement_rows((table,))
        )


@dataclass(frozen=True, slots=True)
class MeasurementScopeQuery:
    """Query for measurement tables describing a semantic scope."""

    scope: MeasurementScope
    name: str | None = None

    def __post_init__(self) -> None:
        MeasurementScope(self.scope)
        if self.name == "":
            raise ValueError("MeasurementScopeQuery.name cannot be empty.")

    def matches(self, table: MeasurementTable) -> bool:
        if table.subject.scope is not MeasurementScope(self.scope):
            return False
        return self.name is None or table.subject.name == self.name


def runtime_measurement_tables(
    context: RuntimeArtifactQueryContext,
) -> tuple[MeasurementTable, ...]:
    """Return all measurement tables in a runtime query context."""
    cache_key = (context.axis_id, context.group_key)
    store_cache = context.store.query_cache(RuntimeMeasurementTablesQueryCache)
    records = tuple(
        record
        for record in context.find()
        if issubclass(record.key.artifact_type, MeasurementBearingArtifactType)
    )
    # Stored tables retain their carrier identity. Derived geometry views must
    # observe the current geometry rather than caching a detached row snapshot.
    stored_tables_only = all(
        record.key.artifact_type is MeasurementsArtifactType for record in records
    )
    cached = store_cache.cached_value(cache_key) if stored_tables_only else None
    if cached is not None:
        return cached
    from openhcs.core.equivalence.policy import DEFAULT_RUNTIME_MEASUREMENT_DIALECT

    tables = tuple(
        table
        for record in records
        for table in record.key.artifact_type.measurement_tables(
            record, DEFAULT_RUNTIME_MEASUREMENT_DIALECT
        )
    )
    return store_cache.store_value(cache_key, tables) if stored_tables_only else tables


def runtime_measurement_tables_for_object(
    context: RuntimeArtifactQueryContext,
    object_name: str,
) -> tuple[MeasurementTable, ...]:
    """Return measurement tables whose subject is one object set."""
    query = MeasurementObjectQuery(object_name)
    return tuple(
        table for table in runtime_measurement_tables(context) if query.matches(table)
    )


def runtime_measurement_tables_for_scope(
    context: RuntimeArtifactQueryContext,
    scope: MeasurementScope,
    name: str | None = None,
) -> tuple[MeasurementTable, ...]:
    """Return measurement tables whose subject matches one semantic scope."""
    query = MeasurementScopeQuery(scope, name)
    return tuple(
        table for table in runtime_measurement_tables(context) if query.matches(table)
    )


def runtime_relationship(
    context: RuntimeArtifactQueryContext,
    name: str,
) -> ObjectRelationship:
    """Return one relationship artifact as native OpenHCS relationship value."""
    record = context.resolve(
        name=name,
        artifact_type=RelationshipsArtifactType,
        purpose="relationship artifact",
    )
    return cast(ObjectRelationship, record.data)


def runtime_spatial_grid(
    context: RuntimeArtifactQueryContext,
    name: str,
) -> SpatialGrid:
    """Return one spatial-grid artifact as a native OpenHCS value."""
    record = context.resolve(
        name=name,
        artifact_type=SpatialGridArtifactType,
        purpose="spatial grid artifact",
    )
    return cast(SpatialGrid, record.data)


def _measurement_table_may_declare_object_name(table: MeasurementTable) -> bool:
    """Return whether table or row schema declares object ownership."""
    if table.subject.object_name is not None:
        return True
    return any(
        field.name == MeasurementRowAxisField.OBJECT_NAME.value
        for field in table.rows.fields
    )


@dataclass(frozen=True, slots=True)
class MeasurementTableAxisProjection(MeasurementAxisValueProjection):
    """Projection of one measurement table onto a declared row-axis value."""

    table: MeasurementTable | None = None

    def apply(self, table: MeasurementTable | None = None) -> MeasurementTable:
        """Return the table narrowed to this row-axis value."""
        target_table = self._target_table(table)
        rows = target_table.rows
        if self.field_name not in {field.name for field in rows.fields}:
            return target_table
        axis_mask = self.mask(columnar_row_values(rows, self.field_name))
        if bool(np.all(axis_mask)):
            return target_table
        return target_table.replace_fields(
            rows=AxisFilteredMeasurementColumnarRows(
                rows,
                self,
                axis_mask=axis_mask,
            ),
            source_provenance=self.table_source_provenance(target_table),
        )

    def table_projection(self, table: MeasurementTable) -> MeasurementTable:
        """Return one table narrowed to this row-axis value."""
        return self.apply(table)

    def tables(
        self,
        measurement_tables: tuple[MeasurementTable, ...],
    ) -> tuple[MeasurementTable, ...]:
        """Return measurement tables narrowed to this row-axis value."""
        return tuple(self.table_projection(table) for table in measurement_tables)

    def _target_table(self, table: MeasurementTable | None) -> MeasurementTable:
        target_table = self.table if table is None else table
        if target_table is None:
            raise ValueError(
                "MeasurementTableAxisProjection.apply requires a table when the "
                "projection was not constructed with one."
            )
        return target_table


def measurement_table_slice_indices(table: MeasurementTable) -> set[int]:
    """Return runtime slice indexes declared by one measurement table."""
    return measurement_table_axis_values(table, MeasurementRowAxisField.SLICE_INDEX)


@dataclass(frozen=True, slots=True)
class MeasurementLabelSliceAxisSelection:
    """Authoritative row-axis binding for label-stack measurement lookup."""

    row_axis: MeasurementRowAxisField
    row_axis_values: tuple[int, ...]
    required_row_axis_values: tuple[int, ...]
    plane_projection: RuntimePlaneAxisValueProjection

    @classmethod
    def for_labels(
        cls,
        *,
        row_axis: MeasurementRowAxisField,
        labels: ObjectLabelValue,
        plane_projector: RuntimePlaneAxisProjector,
    ) -> "MeasurementLabelSliceAxisSelection":
        """Bind label-domain semantics to the invocation's exact runtime axis."""
        domain_strategy = ObjectLabelPlaneDomainStrategy.for_enum_member(
            labels.object_label_domain().scope
        )
        projection = domain_strategy.measurement_projection(labels, plane_projector)
        return cls(
            row_axis=row_axis,
            row_axis_values=domain_strategy.measurement_axis_values(
                labels,
                projection,
            ),
            required_row_axis_values=(
                domain_strategy.required_measurement_axis_values(
                    labels,
                    projection,
                )
            ),
            plane_projection=projection,
        )

    def validate_observed_axis_values(
        self,
        observed: Iterable[int],
        *,
        required_axis_values: Iterable[int] | None = None,
    ) -> None:
        """Require rows for every non-empty label plane in the declared scope."""
        observed_values = tuple(sorted(dict.fromkeys(int(value) for value in observed)))
        required_values = tuple(
            sorted(
                dict.fromkeys(
                    self.required_row_axis_values
                    if required_axis_values is None
                    else (int(value) for value in required_axis_values)
                )
            )
        )
        full_axis_values = tuple(range(self.plane_projection.axis_size))
        selects_one_plane = self.plane_projection.plane_index is not None
        missing_values = tuple(
            value for value in required_values if value not in observed_values
        )
        unexpected_values = tuple(
            value
            for value in observed_values
            if value
            not in (full_axis_values if selects_one_plane else self.row_axis_values)
        )
        if missing_values or unexpected_values:
            raise ValueError(
                "Object-label measurement row axis does not match the declared "
                f"label domain: required {required_values!r}, allowed "
                f"{(full_axis_values if selects_one_plane else self.row_axis_values)!r}, "
                f"observed {observed_values!r}."
            )

    def value_index_for_slice(
        self,
        values_by_slice: Mapping[int, MeasurementValueIndexResult],
        slice_index: int,
    ) -> MeasurementValueIndexResult:
        """Return the measurement index for the exact declared label-plane axis."""
        if slice_index < 0 or slice_index >= len(self.row_axis_values):
            raise IndexError(slice_index)
        row_axis_value = self.row_axis_values[slice_index]
        try:
            return values_by_slice[row_axis_value]
        except KeyError as exc:
            raise ValueError(
                "Object-label measurement rows are missing declared axis value "
                f"{row_axis_value}."
            ) from exc


@dataclass(frozen=True, slots=True, kw_only=True)
class MeasurementLabelSliceFeatureQuery(MeasurementTableFeatureQuery):
    """Query one measurement feature against a stack of object-label planes."""

    row_axis: MeasurementRowAxisField = MeasurementRowAxisField.SLICE_INDEX
    plane_projector: RuntimePlaneAxisProjector

    def select_axis(
        self,
        labels: ObjectLabelValue,
    ) -> MeasurementLabelSliceAxisSelection:
        """Return the exact label-owned OpenHCS runtime row axis."""
        return MeasurementLabelSliceAxisSelection.for_labels(
            row_axis=self.row_axis,
            labels=labels,
            plane_projector=self.plane_projector,
        )

    def axis_values(self, axis: MeasurementRowAxisField) -> tuple[int, ...]:
        """Return sorted row-axis values on tables that can carry the feature."""
        values = {
            value
            for table in self.measurement_tables
            if self.table_may_carry_feature(table)
            for value in measurement_table_axis_values(table, axis)
        }
        return tuple(sorted(values))

    def values_for_labels(
        self,
        labels: ObjectLabelValue,
    ) -> tuple[Any, ...]:
        """Return measurement values aligned to each label plane."""
        import numpy as np

        label_planes = self.label_planes(labels)
        label_domains = tuple(
            dense_object_label_id_domain(label_plane) for label_plane in label_planes
        )
        if not any(label_domains):
            return tuple(
                ObjectLabelMeasurementValues(
                    label_domain,
                    np.empty(0, dtype=np.float64),
                ).values
                for label_domain in label_domains
            )
        axis_selection = self.select_axis(labels)
        indexed_values_by_plane = self.indexed_values_for_label_planes(
            label_planes,
            axis_selection=axis_selection,
        )
        return tuple(
            IndexedObjectMeasurementLabelPlaneBinding(
                measurement_tables=self.measurement_tables,
                object_name=self.object_name,
                feature_name=self.feature_name,
                labels=label_plane,
                dialect=self.dialect,
                indexed_values=indexed_values,
            ).values()
            for label_plane, indexed_values in zip(
                label_planes,
                indexed_values_by_plane,
                strict=True,
            )
        )

    def label_planes(
        self,
        labels: ObjectLabelValue,
    ) -> tuple[ObjectLabelValue, ...]:
        """Return planes selected by the nominal label domain and runtime axis."""
        if not isinstance(labels, ObjectLabelValue):
            raise TypeError(
                "Object-label measurement lookup requires ObjectLabelValue, got "
                f"{type(labels).__name__}."
            )
        domain_strategy = ObjectLabelPlaneDomainStrategy.for_enum_member(
            labels.object_label_domain().scope
        )
        return domain_strategy.measurement_planes(
            labels,
            domain_strategy.measurement_projection(labels, self.plane_projector),
        )

    def indexed_values_for_label_planes(
        self,
        label_planes: tuple[ObjectLabelValue, ...],
        *,
        axis_selection: MeasurementLabelSliceAxisSelection,
    ) -> tuple[MeasurementValueIndexResult, ...]:
        """Return feature indexes aligned to label planes through one axis authority."""
        batch_values_by_axis = self.object_batch_value_indexes_by_axis(
            axis_selection.row_axis,
        )
        if batch_values_by_axis is not None and self.object_name is not None:
            values_by_axis = {
                axis_value: values_by_object[self.object_name]
                for axis_value, values_by_object in batch_values_by_axis.items()
                if self.object_name in values_by_object
            }
            return self.axis_values_for_label_planes(
                values_by_axis,
                label_planes,
                axis_selection=axis_selection,
            )
        values_by_axis = self.value_indexes_by_axis(axis_selection.row_axis)
        if values_by_axis is not None:
            return self.axis_values_for_label_planes(
                values_by_axis,
                label_planes,
                axis_selection=axis_selection,
            )
        axis_selection.validate_observed_axis_values(())
        if len(label_planes) != 1:
            raise ValueError(
                "Axisless object measurements require one payload-scoped label value."
            )
        return (self.value_index(self.axisless_feature_tables()),)

    @staticmethod
    def axis_values_for_label_planes(
        values_by_axis: Mapping[int, MeasurementValueIndexResult],
        label_planes: tuple[ObjectLabelValue, ...],
        *,
        axis_selection: MeasurementLabelSliceAxisSelection,
    ) -> tuple[MeasurementValueIndexResult, ...]:
        """Bind declared measurement rows to the exact object-label plane domain."""
        if len(label_planes) != len(axis_selection.row_axis_values):
            raise ValueError(
                "Object-label plane count does not match its declared measurement axis: "
                f"{len(label_planes)} planes for {axis_selection.row_axis_values!r}."
            )
        axis_selection.validate_observed_axis_values(
            values_by_axis,
        )
        return tuple(
            (values_by_axis[axis_value] if axis_value in values_by_axis else ({}, []))
            for axis_value in axis_selection.row_axis_values
        )

    def object_batch_value_indexes_by_axis(
        self,
        row_axis: MeasurementRowAxisField,
    ) -> dict[int, Mapping[str, MeasurementValueIndexResult]] | None:
        """Return object-batch feature indexes for this query's object domain."""
        if self.object_name is None:
            return None
        return MeasurementObjectFeatureVectorBatchQuery(
            self.feature_name,
            (self.object_name,),
            dialect=self.dialect,
        ).value_indexes_by_axis(
            {self.object_name: self.measurement_tables},
            row_axis,
        )

    def axisless_feature_tables(self) -> tuple[MeasurementTable, ...]:
        """Return feature-bearing tables that declare no runtime row axis."""
        return tuple(
            table
            for table in self.measurement_tables
            if self.table_may_carry_feature(table)
            and not measurement_table_axis_values(table, self.row_axis)
        )

    def value_indexes_by_axis(
        self,
        row_axis: MeasurementRowAxisField,
    ) -> dict[int, MeasurementValueIndexResult] | None:
        """Return per-axis feature indexes without re-scanning tables per plane."""
        by_slice: dict[int, MeasurementValueIndexResult] = {}
        query_object_name = self.query_object_name

        for table in self.measurement_tables:
            if not self.table_may_carry_feature(table):
                continue
            if query_object_name is not None:
                table_object = table.subject.object_name
                if table_object not in (None, query_object_name):
                    continue

            slice_indices = measurement_table_axis_values(table, row_axis)
            if not slice_indices:
                continue

            for slice_index in sorted(slice_indices):
                table_index = MeasurementFeatureValueIndex.from_table(
                    MeasurementTableAxisProjection(
                        axis=row_axis,
                        value=slice_index,
                        table=table,
                    ).apply(),
                    self,
                )
                if not table_index.present:
                    continue
                target = by_slice.get(slice_index)
                if target is None:
                    target = ({}, [])
                    by_slice[slice_index] = target
                _merge_measurement_value_index(
                    target,
                    table_index.as_query_result(),
                )

        if by_slice:
            return by_slice
        return None


@dataclass(frozen=True, slots=True, kw_only=True)
class MeasurementLabelSliceFeatureBatchQuery(MeasurementLabelSliceFeatureQuery):
    """Query one feature for multiple object-label payloads through one table pass."""

    labels_by_object: Mapping[str, ObjectLabelValue]

    @property
    def object_names(self) -> tuple[str, ...]:
        """Return requested object names in caller order."""
        return tuple(dict.fromkeys(str(name) for name in self.labels_by_object))

    def values_by_object(self) -> Mapping[str, tuple[Any, ...]]:
        """Return label-plane-aligned vectors keyed by object name."""
        label_planes_by_object = {
            object_name: self.object_feature_query(object_name).label_planes(labels)
            for object_name, labels in self.labels_by_object.items()
        }
        object_names = self.object_names
        values_by_object: dict[str, tuple[Any, ...]] = {}
        axis_selections_by_object = {
            object_name: self.object_feature_query(object_name).select_axis(
                self.labels_by_object[object_name]
            )
            for object_name in object_names
        }
        batch_values_by_axis_by_row_axis = {
            row_axis: MeasurementObjectFeatureVectorBatchQuery(
                self.feature_name,
                tuple(
                    object_name
                    for object_name, axis_selection in axis_selections_by_object.items()
                    if axis_selection.row_axis is row_axis
                ),
                dialect=self.dialect,
            ).value_indexes_by_axis(
                {
                    object_name: self.measurement_tables
                    for object_name, axis_selection in axis_selections_by_object.items()
                    if axis_selection.row_axis is row_axis
                },
                row_axis,
            )
            for row_axis in tuple(
                dict.fromkeys(
                    axis_selection.row_axis
                    for axis_selection in axis_selections_by_object.values()
                )
            )
        }
        for object_name in object_names:
            label_planes = label_planes_by_object[object_name]
            object_query = self.object_feature_query(object_name)
            axis_selection = axis_selections_by_object[object_name]
            batch_values_by_axis = batch_values_by_axis_by_row_axis[
                axis_selection.row_axis
            ]
            if batch_values_by_axis is None:
                indexed_values_by_plane = object_query.indexed_values_for_label_planes(
                    label_planes,
                    axis_selection=axis_selection,
                )
            else:
                values_by_axis = {
                    axis_value: values_by_object[object_name]
                    for axis_value, values_by_object in batch_values_by_axis.items()
                    if object_name in values_by_object
                }
                indexed_values_by_plane = object_query.axis_values_for_label_planes(
                    values_by_axis,
                    label_planes,
                    axis_selection=axis_selection,
                )
            values_by_object[object_name] = tuple(
                IndexedObjectMeasurementLabelPlaneBinding(
                    measurement_tables=object_query.measurement_tables,
                    object_name=object_name,
                    feature_name=object_query.feature_name,
                    labels=label_plane,
                    dialect=object_query.dialect,
                    indexed_values=indexed_values,
                ).values()
                for label_plane, indexed_values in zip(
                    label_planes,
                    indexed_values_by_plane,
                    strict=True,
                )
            )
        return MappingProxyType(
            {object_name: values_by_object[object_name] for object_name in object_names}
        )

    def object_feature_query(
        self, object_name: str
    ) -> MeasurementLabelSliceFeatureQuery:
        """Return the single-object query that owns one batch member's semantics."""
        return MeasurementLabelSliceFeatureQuery(
            measurement_tables=self.measurement_tables,
            feature_name=self.feature_name,
            object_name=object_name,
            dialect=self.dialect,
            row_axis=self.row_axis,
            plane_projector=self.plane_projector,
        )


def _merge_measurement_value_index(
    target: MeasurementValueIndexResult,
    source: MeasurementValueIndexResult,
) -> None:
    target[0].update(source[0])
    target[1].extend(source[1])


@dataclass(slots=True)
class AxisFilteredMeasurementColumnarRows(MeasurementColumnarRowsView):
    """Columnar measurement rows filtered to one runtime/CellProfiler axis value."""

    rows: ColumnarRows
    projection: MeasurementAxisValueProjection
    axis_mask: Any | None = None

    def __post_init__(self) -> None:
        self.object_row_identity = self.rows.object_row_identity
        self._fields = self.rows.fields
        columns = {
            str(column): np.asarray(columnar_row_values(self.rows, str(column)))
            for column in self.rows.columns
        }
        if self.axis_mask is None:
            axis_values = columns.get(self.projection.field_name)
            if axis_values is None:
                self._columns = columns
            else:
                axis_mask = self.projection.mask(axis_values)
        else:
            axis_mask = self.axis_mask
        if self.projection.field_name not in columns:
            self._columns = columns
        elif bool(np.all(axis_mask)):
            self._columns = columns
        else:
            self._columns = {
                column_name: column_values[axis_mask]
                for column_name, column_values in columns.items()
            }
        self.validate_fields()


def _label_planes_are_empty(label_planes: tuple[Any, ...]) -> bool:
    import numpy as np

    return all(not np.any(label_plane > 0) for label_plane in label_planes)
