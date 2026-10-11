"""Debug inspector section and table declarations over debug snapshots."""

from __future__ import annotations

from typing import ClassVar, cast

from openhcs.core.debug import DebugArtifactRef, DebugInvocationParameter, DebugSnapshot
from openhcs.core.debug_view_models import (
    AvailableEmptySection,
    AvailableEmptyTable,
    DebugViewModel,
    DebugViewSectionDeclarationBase,
    DebugViewTable,
    DebugViewTableProjectionDeclarationBase,
    ReportedEmptySection,
)
from openhcs.core.runtime_stores import (
    RuntimeArtifactAddress,
    RuntimeValueStore,
    StoredRuntimeValue,
)


class SummaryDebugViewSection(AvailableEmptySection, DebugViewSectionDeclarationBase):
    name = "summary"
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
    name = "sources"
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
    name = "input_artifacts"
    title_words = ("Input", "Artifacts")
    empty_subject = "input artifacts"

    @classmethod
    def table_for_snapshot(cls, snapshot: DebugSnapshot) -> "DebugViewTable | None":
        return artifact_refs_snapshot_table(snapshot.input_artifact_refs)


class OutputArtifactsDebugViewSection(
    AvailableEmptySection,
    DebugViewSectionDeclarationBase,
):
    name = "output_artifacts"
    title_words = ("Output", "Artifacts")
    empty_subject = "output artifacts"

    @classmethod
    def table_for_snapshot(cls, snapshot: DebugSnapshot) -> "DebugViewTable | None":
        return artifact_refs_snapshot_table(snapshot.output_artifact_refs)


class PreviewArtifactsDebugViewSection(
    AvailableEmptySection,
    DebugViewSectionDeclarationBase,
):
    name = "preview_artifacts"
    title_words = ("Preview", "Artifacts")
    empty_subject = "preview artifacts"

    @classmethod
    def table_for_snapshot(cls, snapshot: DebugSnapshot) -> "DebugViewTable | None":
        return artifact_refs_snapshot_table(snapshot.preview_refs)


class InvocationParametersDebugViewSection(
    AvailableEmptySection,
    DebugViewSectionDeclarationBase,
):
    name = "invocation_parameters"
    title_words = ("Invocation", "Parameters")
    empty_subject = "invocation parameters"

    @classmethod
    def table_for_snapshot(cls, snapshot: DebugSnapshot) -> "DebugViewTable | None":
        if not snapshot.invocation_parameters:
            return None
        return InvocationParametersDebugViewTable.table_for(
            snapshot.invocation_parameters
        )


class RuntimeValuesDebugViewSection(
    AvailableEmptySection,
    DebugViewSectionDeclarationBase,
):
    name = "runtime_values"
    title_words = ("Runtime", "Values")
    empty_subject = "runtime values"

    @classmethod
    def view_model_for_store(
        cls,
        store: RuntimeValueStore,
        *,
        title: str = "Runtime Values",
    ) -> DebugViewModel:
        return DebugViewModel(
            title=title,
            sections=(
                cls.section(
                    table=RuntimeValueRecordsDebugViewTable.table_for(store.values())
                ),
            ),
        )


class MeasurementsDebugViewSection(
    AvailableEmptySection,
    DebugViewSectionDeclarationBase,
):
    name = "measurements"
    title_words = ("Measurements",)
    empty_subject = "measurements"

    @classmethod
    def table_for_snapshot(cls, snapshot: DebugSnapshot) -> "DebugViewTable | None":
        return artifact_refs_snapshot_table(snapshot.measurement_refs)


class RelationshipsDebugViewSection(
    AvailableEmptySection,
    DebugViewSectionDeclarationBase,
):
    name = "relationships"
    title_words = ("Relationships",)
    empty_subject = "relationships"

    @classmethod
    def table_for_snapshot(cls, snapshot: DebugSnapshot) -> "DebugViewTable | None":
        return artifact_refs_snapshot_table(snapshot.relationship_refs)


class TimingDebugViewSection(AvailableEmptySection, DebugViewSectionDeclarationBase):
    name = "timing"
    title_words = ("Timing",)
    empty_subject = "timing value"
    empty_verb = "is"

    @classmethod
    def text_for_snapshot(cls, snapshot: DebugSnapshot) -> str | None:
        if snapshot.timing_seconds is None:
            return None
        return f"{snapshot.timing_seconds:.6f}s"


class ErrorDebugViewSection(ReportedEmptySection, DebugViewSectionDeclarationBase):
    name = "error"
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
    name = "artifact_refs"
    value_type = DebugArtifactRef
    empty_subject = "artifact references"


class InvocationParametersDebugViewTable(
    AvailableEmptyTable,
    DebugViewTableProjectionDeclarationBase,
):
    name = "invocation_parameters"
    value_type = DebugInvocationParameter
    empty_subject = "invocation parameters"


class RuntimeValueRecordsDebugViewTable(
    AvailableEmptyTable,
    DebugViewTableProjectionDeclarationBase,
):
    name = "runtime_value_records"
    value_type = StoredRuntimeValue
    record_type = RuntimeArtifactAddress
    empty_subject = "runtime values"

    @classmethod
    def table_record(cls, value: object) -> RuntimeArtifactAddress:
        runtime_value = cast(StoredRuntimeValue, cls.require_value(value))
        return RuntimeArtifactAddress.from_record(runtime_value)


def snapshot_view_model(
    snapshot: DebugSnapshot,
    *,
    title: str | None = None,
) -> DebugViewModel:
    """The inspector view of one snapshot: every declared section that has content."""

    return DebugViewModel(
        title=title or snapshot.callable_name or snapshot.step_name,
        sections=tuple(
            section
            for declaration in DebugViewSectionDeclarationBase.__registry__.values()
            for section in (declaration.section_for_snapshot(snapshot),)
            if section is not None
        ),
    )


def artifact_refs_snapshot_table(
    refs: tuple[DebugArtifactRef, ...],
) -> DebugViewTable | None:
    if not refs:
        return None
    return ArtifactRefsDebugViewTable.table_for(refs)


__all__ = tuple(
    name
    for name, value in tuple(globals().items())
    if isinstance(value, type) and value.__module__ == __name__
)
