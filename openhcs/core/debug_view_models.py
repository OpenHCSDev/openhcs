"""Lightweight debug view model payloads.

Pure renderer-independent wire payloads (enums, declarations, table, section,
model) with no imports from the runtime, artifact, or debug-snapshot
authorities. The concrete section and table-projection declarations, which
require those authorities, live in ``openhcs.core.debug_views`` and register
into the declaration registries defined here, so wire-projection consumers
(agent DTOs, MCP clients) do not pay the runtime import cost of building the
inspector registry.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import asdict, dataclass, fields, is_dataclass
from enum import Enum
import json
from typing import ClassVar, Mapping

from metaclass_registry import AutoRegisterMeta


class DebugViewTableProjection(Enum):
    """Closed table projection family used by debug inspectors."""

    ARTIFACT_REFS = "artifact_refs"
    INVOCATION_PARAMETERS = "invocation_parameters"
    RUNTIME_VALUE_RECORDS = "runtime_value_records"


class DebugViewSectionKind(str, Enum):
    """Closed renderer-independent debug inspector section family."""

    SUMMARY = "summary"
    SOURCES = "sources"
    INPUT_ARTIFACTS = "input_artifacts"
    OUTPUT_ARTIFACTS = "output_artifacts"
    PREVIEW_ARTIFACTS = "preview_artifacts"
    INVOCATION_PARAMETERS = "invocation_parameters"
    RUNTIME_VALUES = "runtime_values"
    MEASUREMENTS = "measurements"
    RELATIONSHIPS = "relationships"
    TIMING = "timing"
    ERROR = "error"


class DebugViewSectionDeclarationBase(ABC, metaclass=AutoRegisterMeta):
    """Nominal declaration for one debug inspector section kind."""

    __registry_key__ = "kind"
    __skip_if_no_key__ = True
    __registry__: ClassVar[
        dict[DebugViewSectionKind, type["DebugViewSectionDeclarationBase"]]
    ] = {}

    kind: ClassVar[DebugViewSectionKind | None] = None
    title_words: ClassVar[tuple[str, ...]]

    @classmethod
    def require_kind(cls) -> DebugViewSectionKind:
        if cls.kind is None:
            raise TypeError(f"{cls.__name__} does not declare a section kind.")
        return cls.kind

    @classmethod
    def for_kind(
        cls,
        kind: DebugViewSectionKind,
    ) -> type["DebugViewSectionDeclarationBase"]:
        return cls.__registry__[kind]

    @classmethod
    def default_title(cls) -> str:
        return " ".join(cls.title_words)

    @classmethod
    def registered_sections(cls) -> tuple[type["DebugViewSectionDeclarationBase"], ...]:
        return tuple(
            cls.__registry__[kind]
            for kind in DebugViewSectionKind
            if kind in cls.__registry__
        )

    @classmethod
    def section_for_snapshot(cls, snapshot: DebugSnapshot) -> "DebugViewSection | None":
        table = cls.table_for_snapshot(snapshot)
        text = cls.text_for_snapshot(snapshot)
        if table is None and text is None:
            return None
        section = DebugViewSection(
            kind=cls.require_kind(),
            title=cls.default_title(),
            table=table,
            text=text,
        )
        if section.is_empty and not cls.show_empty_snapshot_section():
            return None
        return section

    @classmethod
    def table_for_snapshot(cls, snapshot: DebugSnapshot) -> "DebugViewTable | None":
        del snapshot
        return None

    @classmethod
    def text_for_snapshot(cls, snapshot: DebugSnapshot) -> str | None:
        del snapshot
        return None

    @classmethod
    def show_empty_snapshot_section(cls) -> bool:
        return False

    @classmethod
    @abstractmethod
    def empty_message(cls) -> str:
        """Return section-level empty text."""


class AvailableEmptySection:
    """Section empty-message strategy for absent available values."""

    empty_subject: ClassVar[str]
    empty_verb: ClassVar[str] = "are"

    @classmethod
    def empty_message(cls) -> str:
        return f"No {cls.empty_subject} {cls.empty_verb} available."


class ReportedEmptySection:
    """Section empty-message strategy for absent reported values."""

    empty_subject: ClassVar[str]

    @classmethod
    def empty_message(cls) -> str:
        return f"No {cls.empty_subject} was reported."


class DebugViewTableProjectionDeclarationBase(ABC, metaclass=AutoRegisterMeta):
    """Nominal declaration for one debug table projection."""

    __registry_key__ = "projection"
    __skip_if_no_key__ = True
    __registry__: ClassVar[
        dict[
            DebugViewTableProjection,
            type["DebugViewTableProjectionDeclarationBase"],
        ]
    ] = {}

    projection: ClassVar[DebugViewTableProjection | None] = None
    value_type: ClassVar[type]
    record_type: ClassVar[type | None] = None
    empty_message: ClassVar[str]
    supports_artifact_actions: ClassVar[bool] = False

    @classmethod
    def require_projection(cls) -> DebugViewTableProjection:
        if cls.projection is None:
            raise TypeError(f"{cls.__name__} does not declare a table projection.")
        return cls.projection

    @classmethod
    def for_projection(
        cls,
        projection: DebugViewTableProjection,
    ) -> type["DebugViewTableProjectionDeclarationBase"]:
        return cls.__registry__[projection]

    @classmethod
    def table_for(cls, values: tuple[object, ...]) -> "DebugViewTable":
        records = tuple(cls.table_record(value) for value in values)
        columns = cls.table_columns()
        return DebugViewTable(
            columns=columns,
            rows=tuple(cls.table_row(record, columns) for record in records),
            projection=cls.require_projection(),
            empty_message=cls.empty_message(),
        )

    @classmethod
    def table_columns(cls) -> tuple[str, ...]:
        record_type = cls.require_record_type()
        return dataclass_record_columns(record_type)

    @classmethod
    def require_record_type(cls) -> type:
        return cls.value_type if cls.record_type is None else cls.record_type

    @classmethod
    def table_record(cls, value: object) -> object:
        return cls.require_value(value)

    @classmethod
    def table_row(cls, record: object, columns: tuple[str, ...]) -> tuple[str, ...]:
        return dataclass_record_cells(record, columns)

    @classmethod
    def require_value(cls, value: object) -> object:
        if not isinstance(value, cls.value_type):
            raise TypeError(
                f"{cls.__name__} requires {cls.value_type.__name__}, "
                f"got {type(value).__name__}."
            )
        return value

    @classmethod
    def empty_message(cls) -> str:
        return "No rows are available."


class AvailableEmptyTable:
    """Table empty-message strategy for absent available rows."""

    empty_subject: ClassVar[str]

    @classmethod
    def empty_message(cls) -> str:
        return f"No {cls.empty_subject} are available."


@dataclass(frozen=True, slots=True)
class DebugViewTable:
    """Small table-like payload for debug inspectors."""

    columns: tuple[str, ...]
    rows: tuple[tuple[str, ...], ...]
    projection: DebugViewTableProjection | None = None
    empty_message: str | None = None

    @classmethod
    def from_projection(
        cls,
        projection: DebugViewTableProjection,
        values: tuple[object, ...],
    ) -> "DebugViewTable":
        return DebugViewTableProjectionDeclarationBase.for_projection(
            projection
        ).table_for(values)

    @classmethod
    def from_dataclass_records(
        cls,
        *,
        record_type: type,
        records: tuple[object, ...],
        empty_message: str | None = None,
        projection: DebugViewTableProjection | None = None,
    ) -> "DebugViewTable":
        columns = dataclass_record_columns(record_type)
        return cls(
            columns=columns,
            rows=tuple(dataclass_record_cells(record, columns) for record in records),
            projection=projection,
            empty_message=empty_message,
        )

    def to_json_dict(self) -> dict[str, object]:
        return {
            "columns": list(self.columns),
            "rows": [list(row) for row in self.rows],
            "projection": None if self.projection is None else self.projection.value,
            "empty_message": self.empty_message,
        }

    @classmethod
    def from_json_dict(cls, data: Mapping[str, object]) -> "DebugViewTable":
        projection_value = data["projection"]
        return cls(
            columns=tuple(str(column) for column in data["columns"]),
            rows=tuple(tuple(str(value) for value in row) for row in data["rows"]),
            projection=(
                None
                if projection_value is None
                else DebugViewTableProjection(str(projection_value))
            ),
            empty_message=(
                None if data["empty_message"] is None else str(data["empty_message"])
            ),
        )


def dataclass_record_columns(record_type: type) -> tuple[str, ...]:
    if not is_dataclass(record_type):
        raise TypeError(
            "dataclass_record_columns requires a dataclass record type, "
            f"got {record_type!r}."
        )
    return tuple(field.name for field in fields(record_type))


def dataclass_record_cells(record: object, columns: tuple[str, ...]) -> tuple[str, ...]:
    if not is_dataclass(record):
        raise TypeError(
            "dataclass_record_cells requires dataclass table records, "
            f"got {type(record).__name__}."
        )
    mapping = asdict(record)
    return tuple(debug_view_cell_text(mapping[column]) for column in columns)


@dataclass(frozen=True, slots=True)
class DebugViewSection:
    """One named debug view section."""

    kind: DebugViewSectionKind
    title: str
    table: DebugViewTable | None = None
    text: str | None = None

    @property
    def is_empty(self) -> bool:
        return (self.table is None or not self.table.rows) and not self.text

    def to_json_dict(self) -> dict[str, object]:
        return {
            "kind": self.kind.value,
            "title": self.title,
            "table": None if self.table is None else self.table.to_json_dict(),
            "text": self.text,
        }

    @classmethod
    def from_json_dict(cls, data: Mapping[str, object]) -> "DebugViewSection":
        table = data["table"]
        if table is not None and not isinstance(table, Mapping):
            raise TypeError("DebugViewSection.table must be a mapping or None.")
        return cls(
            kind=DebugViewSectionKind(str(data["kind"])),
            title=str(data["title"]),
            table=(None if table is None else DebugViewTable.from_json_dict(table)),
            text=None if data["text"] is None else str(data["text"]),
        )


@dataclass(frozen=True, slots=True)
class DebugViewModel:
    """Renderer-independent debug inspector model."""

    title: str
    sections: tuple[DebugViewSection, ...]

    @classmethod
    def from_debug_snapshot(
        cls,
        snapshot: DebugSnapshot,
        *,
        title: str | None = None,
    ) -> "DebugViewModel":
        return cls(
            title=title or snapshot.callable_name or snapshot.step_name,
            sections=tuple(
                section
                for declaration in DebugViewSectionDeclarationBase.registered_sections()
                for section in (declaration.section_for_snapshot(snapshot),)
                if section is not None
            ),
        )

    @classmethod
    def from_runtime_value_store(
        cls,
        store: RuntimeValueStore,
        *,
        title: str = "Runtime Values",
    ) -> "DebugViewModel":
        from openhcs.core.runtime_stores import RuntimeValueStore

        if not isinstance(store, RuntimeValueStore):
            raise TypeError(
                "DebugViewModel.from_runtime_value_store requires RuntimeValueStore, "
                f"got {type(store).__name__}."
            )
        section_declaration = DebugViewSectionDeclarationBase.for_kind(
            DebugViewSectionKind.RUNTIME_VALUES
        )
        return cls(
            title=title,
            sections=(
                DebugViewSection(
                    kind=DebugViewSectionKind.RUNTIME_VALUES,
                    title=section_declaration.default_title(),
                    table=DebugViewTable.from_projection(
                        DebugViewTableProjection.RUNTIME_VALUE_RECORDS,
                        store.values(),
                    ),
                ),
            ),
        )

    def to_json_dict(self) -> dict[str, object]:
        return {
            "title": self.title,
            "sections": [section.to_json_dict() for section in self.sections],
        }

    @classmethod
    def from_json_dict(cls, data: Mapping[str, object]) -> "DebugViewModel":
        return cls(
            title=str(data["title"]),
            sections=tuple(
                DebugViewSection.from_json_dict(section) for section in data["sections"]
            ),
        )


def debug_view_cell_text(value: object) -> str:
    if value is None:
        return ""
    if isinstance(value, Enum):
        return str(value.value)
    if isinstance(value, (str, int, float, bool)):
        return str(value)
    if isinstance(value, tuple):
        return ", ".join(debug_view_cell_text(item) for item in value)
    from openhcs.core.artifacts import ArtifactType

    if isinstance(value, type) and issubclass(value, ArtifactType):
        return value.require_value()
    if is_dataclass(value):
        return json.dumps(debug_view_jsonable(value), sort_keys=True)
    if isinstance(value, Mapping):
        return json.dumps(debug_view_jsonable(value), sort_keys=True)
    return str(value)


def debug_view_jsonable(value: object) -> object:
    if value is None or isinstance(value, (str, int, float, bool)):
        return value
    if isinstance(value, Enum):
        return value.value
    if isinstance(value, tuple):
        return [debug_view_jsonable(item) for item in value]
    if isinstance(value, list):
        return [debug_view_jsonable(item) for item in value]
    if isinstance(value, Mapping):
        return {str(key): debug_view_jsonable(item) for key, item in value.items()}
    from openhcs.core.artifacts import ArtifactType

    if isinstance(value, type) and issubclass(value, ArtifactType):
        return value.require_value()
    if is_dataclass(value):
        return {
            field.name: debug_view_jsonable(getattr(value, field.name))
            for field in fields(value)
        }
    return str(value)


def is_debug_view_model_export(name: str, value: object) -> bool:
    return (
        isinstance(value, type)
        and value.__module__ == __name__
        and not name.startswith("_")
    )


__all__ = tuple(
    name
    for name, value in globals().items()
    if is_debug_view_model_export(name, value)
    and name != "is_debug_view_model_export"
    and name != "AutoRegisterMeta"
    and name != "ABC"
    and name != "abstractmethod"
    and name != "dataclass"
    and name != "fields"
    and name != "is_dataclass"
    and name != "asdict"
    and name != "Enum"
    and name != "json"
    and name != "ClassVar"
    and name != "Mapping"
    and name != "annotations"
)
