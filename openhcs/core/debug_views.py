"""Renderer-independent debug inspector view models."""

from __future__ import annotations

from dataclasses import asdict, dataclass, fields, is_dataclass
from enum import Enum
import json
from typing import ClassVar, Mapping, cast

from metaclass_registry import AutoRegisterMeta

from openhcs.core.debug_view_models import (
    AvailableEmptySection,
    AvailableEmptyTable,
    ReportedEmptySection,
    DebugViewSection,
    DebugViewSectionDeclarationBase,
    DebugViewSectionKind,
    DebugViewTable,
    DebugViewTableProjection,
    DebugViewTableProjectionDeclarationBase,
    DebugViewModel,
    dataclass_record_cells as _dataclass_record_cells_imported,
    dataclass_record_columns as _dataclass_record_columns_imported,
    debug_view_cell_text as _debug_table_cell_text,
    debug_view_jsonable as _debug_table_jsonable,
)
from openhcs.core.artifacts import ArtifactType
from openhcs.core.debug import DebugArtifactRef, DebugInvocationParameter, DebugSnapshot
from openhcs.core.runtime_stores import (
    RuntimeArtifactAddress,
    RuntimeValueStore,
    StoredRuntimeValue,
)


def dataclass_record_columns(record_type: type) -> tuple[str, ...]:
    return _dataclass_record_columns_imported(record_type)


def dataclass_record_cells(record: object, columns: tuple[str, ...]) -> tuple[str, ...]:
    return _dataclass_record_cells_imported(record, columns)


class SummaryDebugViewSection(AvailableEmptySection, DebugViewSectionDeclarationBase):
    kind = DebugViewSectionKind.SUMMARY
    title_words = ("Summary",)
    empty_subject = "summary values"

    @classmethod
    def text_for_snapshot(cls, snapshot: DebugSnapshot) -> str:
        values = (
            ("step", snapshot.step_name),
            ("callable", snapshot.callable_name or ""),
            ("axis", snapshot.axis_id or ""),
            ("cursor", snapshot.cursor.invocation_key or ""),
            (
                "timing_seconds",
                (
                    ""
                    if snapshot.timing_seconds is None
                    else f"{snapshot.timing_seconds:.6f}"
                ),
            ),
        )
        return "\n".join(f"{name}: {value}" for name, value in values)

    @classmethod
    def show_empty_snapshot_section(cls) -> bool:
        return True


class SourcesDebugViewSection(AvailableEmptySection, DebugViewSectionDeclarationBase):
    kind = DebugViewSectionKind.SOURCES
    title_words = ("Sources",)
    empty_subject = "source paths"

    @classmethod
    def text_for_snapshot(cls, snapshot: DebugSnapshot) -> str | None:
        if not snapshot.source_paths:
            return None
        return "\n".join(snapshot.source_paths)


class InputArtifactsDebugViewSection(
    AvailableEmptySection,
    DebugViewSectionDeclarationBase,
):
    kind = DebugViewSectionKind.INPUT_ARTIFACTS
    title_words = ("Input", "Artifacts")
    empty_subject = "input artifacts"

    @classmethod
    def table_for_snapshot(cls, snapshot: DebugSnapshot) -> "DebugViewTable | None":
        return artifact_refs_snapshot_table(snapshot.input_artifact_refs)


class OutputArtifactsDebugViewSection(
    AvailableEmptySection,
    DebugViewSectionDeclarationBase,
):
    kind = DebugViewSectionKind.OUTPUT_ARTIFACTS
    title_words = ("Output", "Artifacts")
    empty_subject = "output artifacts"

    @classmethod
    def table_for_snapshot(cls, snapshot: DebugSnapshot) -> "DebugViewTable | None":
        return artifact_refs_snapshot_table(snapshot.output_artifact_refs)


class PreviewArtifactsDebugViewSection(
    AvailableEmptySection,
    DebugViewSectionDeclarationBase,
):
    kind = DebugViewSectionKind.PREVIEW_ARTIFACTS
    title_words = ("Preview", "Artifacts")
    empty_subject = "preview artifacts"

    @classmethod
    def table_for_snapshot(cls, snapshot: DebugSnapshot) -> "DebugViewTable | None":
        return artifact_refs_snapshot_table(snapshot.preview_refs)


class InvocationParametersDebugViewSection(
    AvailableEmptySection,
    DebugViewSectionDeclarationBase,
):
    kind = DebugViewSectionKind.INVOCATION_PARAMETERS
    title_words = ("Invocation", "Parameters")
    empty_subject = "invocation parameters"

    @classmethod
    def table_for_snapshot(cls, snapshot: DebugSnapshot) -> "DebugViewTable | None":
        if not snapshot.invocation_parameters:
            return None
        return DebugViewTable.from_projection(
            DebugViewTableProjection.INVOCATION_PARAMETERS,
            snapshot.invocation_parameters,
        )


class RuntimeValuesDebugViewSection(
    AvailableEmptySection,
    DebugViewSectionDeclarationBase,
):
    kind = DebugViewSectionKind.RUNTIME_VALUES
    title_words = ("Runtime", "Values")
    empty_subject = "runtime values"


class MeasurementsDebugViewSection(
    AvailableEmptySection,
    DebugViewSectionDeclarationBase,
):
    kind = DebugViewSectionKind.MEASUREMENTS
    title_words = ("Measurements",)
    empty_subject = "measurements"

    @classmethod
    def table_for_snapshot(cls, snapshot: DebugSnapshot) -> "DebugViewTable | None":
        return artifact_refs_snapshot_table(snapshot.measurement_refs)


class RelationshipsDebugViewSection(
    AvailableEmptySection,
    DebugViewSectionDeclarationBase,
):
    kind = DebugViewSectionKind.RELATIONSHIPS
    title_words = ("Relationships",)
    empty_subject = "relationships"

    @classmethod
    def table_for_snapshot(cls, snapshot: DebugSnapshot) -> "DebugViewTable | None":
        return artifact_refs_snapshot_table(snapshot.relationship_refs)


class TimingDebugViewSection(AvailableEmptySection, DebugViewSectionDeclarationBase):
    kind = DebugViewSectionKind.TIMING
    title_words = ("Timing",)
    empty_subject = "timing value"
    empty_verb = "is"

    @classmethod
    def text_for_snapshot(cls, snapshot: DebugSnapshot) -> str | None:
        if snapshot.timing_seconds is None:
            return None
        return f"{snapshot.timing_seconds:.6f}s"


class ErrorDebugViewSection(ReportedEmptySection, DebugViewSectionDeclarationBase):
    kind = DebugViewSectionKind.ERROR
    title_words = ("Error",)
    empty_subject = "error"

    @classmethod
    def text_for_snapshot(cls, snapshot: DebugSnapshot) -> str | None:
        return snapshot.exception


class ArtifactActionDebugTable:
    """Trait for debug tables whose rows identify viewable/exportable artifacts."""

    supports_artifact_actions: ClassVar[bool] = True


class ArtifactRefsDebugViewTable(
    ArtifactActionDebugTable,
    AvailableEmptyTable,
    DebugViewTableProjectionDeclarationBase,
):
    projection = DebugViewTableProjection.ARTIFACT_REFS
    value_type = DebugArtifactRef
    empty_subject = "artifact references"


class InvocationParametersDebugViewTable(
    AvailableEmptyTable,
    DebugViewTableProjectionDeclarationBase,
):
    projection = DebugViewTableProjection.INVOCATION_PARAMETERS
    value_type = DebugInvocationParameter
    empty_subject = "invocation parameters"


class RuntimeValueRecordsDebugViewTable(
    AvailableEmptyTable,
    DebugViewTableProjectionDeclarationBase,
):
    projection = DebugViewTableProjection.RUNTIME_VALUE_RECORDS
    value_type = StoredRuntimeValue
    record_type = RuntimeArtifactAddress
    empty_subject = "runtime values"

    @classmethod
    def table_record(cls, value: object) -> RuntimeArtifactAddress:
        runtime_value = cast(StoredRuntimeValue, cls.require_value(value))
        return RuntimeArtifactAddress.from_record(runtime_value)


def _debug_table_cell_text(value: object) -> str:
    if value is None:
        return ""
    if isinstance(value, Enum):
        return str(value.value)
    if isinstance(value, type) and issubclass(value, ArtifactType):
        return value.require_value()
    if isinstance(value, (str, int, float, bool)):
        return str(value)
    if isinstance(value, tuple):
        return ", ".join(_debug_table_cell_text(item) for item in value)
    if is_dataclass(value):
        return json.dumps(_debug_table_jsonable(value), sort_keys=True)
    if isinstance(value, Mapping):
        return json.dumps(_debug_table_jsonable(value), sort_keys=True)
    return str(value)


def _debug_table_jsonable(value: object) -> object:
    if value is None or isinstance(value, (str, int, float, bool)):
        return value
    if isinstance(value, Enum):
        return value.value
    if isinstance(value, type) and issubclass(value, ArtifactType):
        return value.require_value()
    if isinstance(value, tuple):
        return [_debug_table_jsonable(item) for item in value]
    if isinstance(value, list):
        return [_debug_table_jsonable(item) for item in value]
    if isinstance(value, Mapping):
        return {str(key): _debug_table_jsonable(item) for key, item in value.items()}
    if is_dataclass(value):
        return {
            field.name: _debug_table_jsonable(getattr(value, field.name))
            for field in fields(value)
        }
    return str(value)


def artifact_refs_snapshot_table(
    refs: tuple[DebugArtifactRef, ...],
) -> DebugViewTable | None:
    if not refs:
        return None
    return DebugViewTable.from_projection(DebugViewTableProjection.ARTIFACT_REFS, refs)


def is_debug_view_export(name: str, value: object) -> bool:
    return (
        isinstance(value, type)
        and value.__module__ == __name__
        and not name.startswith("_")
    )


__all__ = tuple(
    name for name, value in globals().items() if is_debug_view_export(name, value)
)
