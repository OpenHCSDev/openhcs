"""CellProfiler image numbering over typed OpenHCS source identities."""

from __future__ import annotations

from collections import OrderedDict
from collections.abc import Sequence
from pathlib import Path
from types import MappingProxyType
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from openhcs.core.context.processing_context import ProcessingContext
from dataclasses import dataclass, field

from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.measurement_row_materialization import (
    MeasurementRowsAxisProjection,
    ColumnarRowColumnOverlay,
    MeasurementProjectedColumnarRows,
    is_structural_missing_measurement_cell,
)
from openhcs.core.runtime_measurements import (
    MeasurementScope,
    MeasurementRowValueField,
    aggregate_image_number_reference_measurement_field,
    image_number_reference_measurement_field,
    measurement_axis_integer_value,
)
from openhcs.core.runtime_measurements import MeasurementTable
from openhcs.core.runtime_measurements import MeasurementRowAxisField
from openhcs.core.runtime_tabular_values import ColumnarRows
from openhcs.core.source_image_provenance import SourceImageProvenance
from openhcs.core.source_matching import (
    SourceImageSetIdentity,
    SourceImageSetIdentityPolicy,
)


@dataclass(slots=True)
class CellProfilerImageSetNumbering:
    """Assign stable one-based image numbers to exact source image sets."""

    identity_policy: SourceImageSetIdentityPolicy
    _numbers: OrderedDict[tuple[str, SourceImageSetIdentity], int] = field(
        default_factory=OrderedDict,
        init=False,
    )

    def observe_export_paths(
        self,
        context: "ProcessingContext",
        paths: Sequence[str],
    ) -> None:
        """Bind actual exporter numbering to its relative bundle paths."""
        from openhcs.core.steps.abstract import StepExecutionObservation

        # Direct rendering has no active execution observer. Actual FunctionSteps
        # retain their derived export ownership until materialization completes.
        if context.runtime_step_outputs is None:
            return
        numbers: dict[str, list[int]] = {}
        for (axis_id, _source_identity), number in self._numbers.items():
            numbers.setdefault(axis_id, []).append(number)
        by_axis = MappingProxyType(
            {axis_id: tuple(values) for axis_id, values in numbers.items()}
        )
        context.record_runtime_step_outputs(
            StepExecutionObservation(
                MappingProxyType({}),
                image_numbers_by_export_path=MappingProxyType(
                    {Path(path): by_axis for path in paths}
                ),
            )
        )

    def for_source_slices(
        self,
        *,
        scope: RuntimeExecutionAxisScope,
        provenance: SourceImageProvenance,
        slice_indices: Sequence[int],
        owner: str,
    ) -> dict[int, int]:
        """Map one producer's local slices to CellProfiler image numbers."""

        return {
            slice_index: self._numbers.setdefault(
                self._source_key(scope, provenance, slice_index, owner=owner),
                len(self._numbers) + 1,
            )
            for slice_index in slice_indices
        }

    def existing_number_for_source_slice(
        self,
        *,
        scope: RuntimeExecutionAxisScope,
        provenance: SourceImageProvenance,
        slice_index: int,
        owner: str,
    ) -> int | None:
        """Find an executed image set without admitting an unused source occurrence."""

        return self._numbers.get(
            self._source_key(scope, provenance, slice_index, owner=owner)
        )

    def _source_key(
        self,
        scope: RuntimeExecutionAxisScope,
        provenance: SourceImageProvenance,
        slice_index: int,
        *,
        owner: str,
    ) -> tuple[str, SourceImageSetIdentity]:
        return (
            scope.axis_id,
            self._source_identity(provenance, slice_index, owner=owner),
        )

    def for_source_slice(
        self,
        *,
        scope: RuntimeExecutionAxisScope,
        provenance: SourceImageProvenance,
        slice_index: int,
        owner: str,
    ) -> int:
        """Return one producer slice's CellProfiler image number."""

        return self.for_source_slices(
            scope=scope,
            provenance=provenance,
            slice_indices=(slice_index,),
            owner=owner,
        )[slice_index]

    def project_measurement_rows(
        self,
        *,
        scope: RuntimeExecutionAxisScope,
        table: MeasurementTable,
        projection: MeasurementRowsAxisProjection | None = None,
    ) -> Sequence[object] | ColumnarRows:
        """Project OpenHCS row axes into exact CellProfiler image numbers."""
        if projection is None:
            projection = MeasurementRowsAxisProjection.from_rows(table.rows)
        image_numbers_by_slice, axisless_image_number = self._measurement_image_numbers(
            scope=scope,
            table=table,
            projection=projection,
        )
        projected = projection.remap_runtime_slice_indices(
            image_numbers_by_slice,
            axisless_value=axisless_image_number,
        )
        replacements = self._project_reference_columns(scope=scope, table=table)
        if not replacements:
            return projected
        return MeasurementProjectedColumnarRows(
            ColumnarRowColumnOverlay(projected.columns, MappingProxyType(replacements)),
            fields=projected.fields,
            declared_object_measurement_domain_covered=(
                projected.covers_declared_object_measurement_domain
            ),
            object_row_identity=projected.object_row_identity,
        )

    def admit_measurement_references(
        self,
        *,
        scope: RuntimeExecutionAxisScope,
        table: MeasurementTable,
        projection: MeasurementRowsAxisProjection | None = None,
    ) -> None:
        """Retain exact image admission without materializing unused row axes.

        References may introduce source planes absent from the physical row
        domain. Preserve their first-encounter numbering and validation even
        when subject demand defers the producer's measurement rows.
        """
        if projection is None:
            projection = MeasurementRowsAxisProjection.from_rows(table.rows)
        self._measurement_image_numbers(scope=scope, table=table, projection=projection)
        self._project_reference_columns(scope=scope, table=table)

    def _measurement_image_numbers(
        self,
        *,
        scope: RuntimeExecutionAxisScope,
        table: MeasurementTable,
        projection: MeasurementRowsAxisProjection,
    ) -> tuple[dict[int, int], int | None]:
        slice_axis = MeasurementRowAxisField.SLICE_INDEX
        image_numbers_by_slice = self.for_source_slices(
            scope=scope,
            provenance=table.source_provenance,
            slice_indices=self.source_slices_for_measurement_table(
                table, projection=projection
            ),
            owner=table.name,
        )
        axisless_image_number = None
        if projection.has_axisless_rows(slice_axis):
            source_plane_indices = tuple(
                range(table.source_provenance.source_plane_count)
            ) or (0,)
            source_image_numbers = tuple(
                dict.fromkeys(
                    image_numbers_by_slice[index] for index in source_plane_indices
                )
            )
            if (
                len(source_image_numbers) != 1
                and table.subject.scope is not MeasurementScope.ARTIFACT
            ):
                raise ValueError(
                    f"CellProfiler export cannot bind axisless rows in "
                    f"{table.name!r} to one source image set; producer provenance "
                    f"resolves to image numbers {source_image_numbers!r}."
                )
            # Artifact-scoped rows summarize the complete produced stack rather
            # than any individual source plane. CellProfiler nevertheless
            # requires every exported row to carry one ImageNumber, so anchor
            # the artifact summary to the stack's first stable image-set number.
            # Image- and object-scoped axisless rows remain ambiguous and fail
            # above when their provenance spans multiple image sets.
            axisless_image_number = source_image_numbers[0]
        return image_numbers_by_slice, axisless_image_number

    def _project_reference_columns(
        self,
        *,
        scope: RuntimeExecutionAxisScope,
        table: MeasurementTable,
    ) -> dict[str, list[object]]:
        # References describe the producer's original image domain, just like
        # slice_index. Project their correlated values before the wide join;
        # precomputed reference means are derived from these object values by
        # the spreadsheet aggregate owner instead of offsetting a mean.
        replacements = {}
        feature_field = next(
            (
                name
                for name in MeasurementRowAxisField.feature_name_field_names_ordered()
                if name in table.rows.columns
            ),
            None,
        )
        reference_indices = []
        value_fields = MeasurementRowValueField.field_names()
        if feature_field is not None and value_fields.intersection(table.rows.columns):
            reference_features: dict[str, bool] = {}
            for offset, features in table.rows.column_value_segments(feature_field):
                for index, feature in enumerate(features, start=offset):
                    if is_structural_missing_measurement_cell(feature):
                        continue
                    feature = str(feature)
                    is_reference = reference_features.get(feature)
                    if is_reference is None:
                        is_reference = image_number_reference_measurement_field(
                            feature
                        ) and not aggregate_image_number_reference_measurement_field(
                            feature
                        )
                        reference_features[feature] = is_reference
                    if is_reference:
                        reference_indices.append(index)
        reference_numbers: dict[int, int] = {}
        for name in table.rows.columns:
            wide_reference = image_number_reference_measurement_field(name)
            if aggregate_image_number_reference_measurement_field(name):
                continue
            if not wide_reference and (
                name not in value_fields or not reference_indices
            ):
                continue
            values = table.rows.column_values(name)
            updated = None
            indices = range(len(values)) if wide_reference else reference_indices
            for index in indices:
                value = values[index]
                if is_structural_missing_measurement_cell(value):
                    continue
                number = measurement_axis_integer_value(
                    value, MeasurementRowAxisField.SLICE_INDEX
                )
                if number is None or number <= 0:
                    continue
                global_number = reference_numbers.get(number)
                if global_number is None:
                    global_number = self.for_source_slice(
                        scope=scope,
                        provenance=table.source_provenance,
                        slice_index=number - 1,
                        owner=table.name,
                    )
                    reference_numbers[number] = global_number
                if updated is None:
                    updated = list(values)
                updated[index] = global_number
            if updated is not None:
                replacements[name] = updated
        return replacements

    @staticmethod
    def source_slices_for_measurement_table(
        table: MeasurementTable,
        *,
        projection: MeasurementRowsAxisProjection | None = None,
    ) -> tuple[int, ...]:
        """Return exactly the slices represented by this producer's row scope.

        Axisless rows consume their declared source stack, not a guessed plate
        grid. Preserve explicit row order before additional source planes.
        """
        if projection is None:
            projection = MeasurementRowsAxisProjection.from_rows(table.rows)
        indices = projection.present_axis_values(
            MeasurementRowAxisField.SLICE_INDEX.value
        )
        if not projection.has_axisless_rows(MeasurementRowAxisField.SLICE_INDEX):
            return indices
        source_indices = (
            tuple(range(table.source_provenance.source_plane_count)) or (0,)
        )
        return tuple(dict.fromkeys((*indices, *source_indices)))

    def _source_identity(
        self,
        provenance: SourceImageProvenance,
        slice_index: int,
        *,
        owner: str,
    ) -> SourceImageSetIdentity:
        source_identity = provenance.for_source_plane(slice_index)
        image_set_identity = SourceImageSetIdentity.from_metadata(
            source_identity.source_component_metadata or {},
            fallback_source_path=source_identity.source_path or "",
            policy=self.identity_policy,
        )
        if image_set_identity.components == (("source_path", ""),):
            raise ValueError(
                f"CellProfiler export requires {owner!r} to carry producer-declared "
                f"source identity for slice_index={slice_index}; producer provenance "
                f"is {provenance.equality_identity!r}."
            )
        return image_set_identity
