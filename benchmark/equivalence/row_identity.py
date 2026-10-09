"""Object measurement row identity used when projecting snapshots for native CellProfiler comparison."""

from __future__ import annotations

from dataclasses import dataclass

from openhcs.core.component_group_scope import ComponentGroupScope
from openhcs.core.equivalence.cells import (
    RuntimeCellSignature,
    RuntimeMeasurementCellSignatureProjection,
)
from openhcs.core.equivalence.keys import (
    RuntimeMeasurementSubjectKey,
)
from openhcs.core.equivalence.measurement_rows import (
    IMAGE_IDENTITY_FIELDS,
    RUNTIME_AXIS_ROW_IDENTITY_FIELD,
    RuntimeMeasurementRowIdentity,
    RuntimeMeasurementRowMapping,
)
from openhcs.core.equivalence.policy import (
    RuntimeEquivalencePolicy,
    RuntimeMeasurementDialect,
)
from openhcs.core.runtime_measurements import (
    MeasurementScope,
)
from openhcs.core.runtime_relationships import (
    ObjectInstanceKey,
)

OBJECT_LABEL_ROW_IDENTITY_FIELD = "object_label"


RUNTIME_SLICE_ROW_IDENTITY_FIELD = "_runtime_slice"


@dataclass(frozen=True, slots=True)
class RuntimeObjectMeasurementRowIdentity:
    """Nominal identity for one object measurement row within a runtime axis."""

    row_identity: RuntimeMeasurementRowIdentity
    occurrence_scope: ComponentGroupScope | None = None

    def without_occurrence_scope(self) -> "RuntimeObjectMeasurementRowIdentity":
        """Return this row identity independent of invocation grouping."""
        if self.occurrence_scope is None:
            return self
        return type(self)(self.row_identity)

    @classmethod
    def from_row(
        cls,
        row: RuntimeMeasurementRowMapping,
        axis_key: str | None,
        policy: RuntimeEquivalencePolicy,
    ) -> "RuntimeObjectMeasurementRowIdentity | None":
        selected_field = policy.measurement_dialect.row_identity_contract.selected_object_identity_field(
            row.normalized_field_names
        )
        object_label = row.object_label(
            object_id_field=(
                None
                if selected_field is None
                else row.normalized_fields[selected_field]
            )
        )
        if object_label is None:
            return None
        return cls(
            (
                *row.axis_scoped_identity(
                    axis_key,
                    policy.measurement_dialect,
                ),
                (
                    OBJECT_LABEL_ROW_IDENTITY_FIELD,
                    RuntimeMeasurementCellSignatureProjection(
                        object_label,
                        policy,
                    ).signature(),
                ),
            )
        )

    @classmethod
    def from_object_instance(
        cls,
        row: RuntimeMeasurementRowMapping,
        axis_key: str | None,
        policy: RuntimeEquivalencePolicy,
        object_instance_key: ObjectInstanceKey,
        *,
        occurrence_scope: ComponentGroupScope | None = None,
    ) -> "RuntimeObjectMeasurementRowIdentity":
        row_identity = row.axis_scoped_identity(
            axis_key,
            policy.measurement_dialect,
        )
        if object_instance_key.slice_index is not None:
            image_identity_fields = (
                policy.measurement_dialect.row_identity_contract.image_identity_fields
            )
            row_identity = (
                *(
                    field
                    for field in row_identity
                    if field[0] not in image_identity_fields
                ),
                (RUNTIME_SLICE_ROW_IDENTITY_FIELD, object_instance_key.slice_index),
            )
        return cls(
            (
                *row_identity,
                (
                    OBJECT_LABEL_ROW_IDENTITY_FIELD,
                    RuntimeMeasurementCellSignatureProjection(
                        object_instance_key.object_id,
                        policy,
                    ).signature(),
                ),
            ),
            occurrence_scope,
        )

    @property
    def image_identity(self) -> RuntimeMeasurementRowIdentity:
        return tuple(
            field
            for field in self.row_identity
            if field[0] != OBJECT_LABEL_ROW_IDENTITY_FIELD
        )

    @property
    def has_image_identity(self) -> bool:
        return any(
            field[0] in IMAGE_IDENTITY_FIELDS
            or field[0]
            in (
                RUNTIME_AXIS_ROW_IDENTITY_FIELD,
                RUNTIME_SLICE_ROW_IDENTITY_FIELD,
            )
            for field in self.row_identity
        )

    @property
    def object_label_signature(self) -> RuntimeCellSignature | None:
        return object_label_signature_from_row_identity(self.row_identity)


@dataclass(frozen=True, slots=True)
class RuntimeMeasurementRowSubjectProjection:
    """Resolve runtime-row source and subject from nominal row identity."""

    table_subject: RuntimeMeasurementSubjectKey
    table_source_name: str | None
    row: RuntimeMeasurementRowMapping
    dialect: RuntimeMeasurementDialect

    def source_name(self) -> str | None:
        row_source_name = self.row.source_name()
        if row_source_name is not None:
            return row_source_name
        return self.table_source_name

    def subject(self) -> RuntimeMeasurementSubjectKey:
        object_identity = self.row.object_identity_value(self.dialect)
        object_name = self.row.object_name()
        if object_name is not None and object_identity is not None:
            return RuntimeMeasurementSubjectKey(MeasurementScope.OBJECT, object_name)
        if self.row.source_name() is not None and object_identity is None:
            return RuntimeMeasurementSubjectKey(
                MeasurementScope.IMAGE,
                MeasurementScope.IMAGE.value,
            )
        return self.table_subject


def object_label_signature_from_row_identity(
    row_identity: RuntimeMeasurementRowIdentity,
) -> RuntimeCellSignature | None:
    """Return the object-label signature embedded in a runtime row identity."""
    return next(
        (
            field_value
            for field_name, field_value in row_identity
            if (
                field_name == OBJECT_LABEL_ROW_IDENTITY_FIELD
                and isinstance(field_value, RuntimeCellSignature)
            )
        ),
        None,
    )
