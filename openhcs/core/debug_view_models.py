"""Lightweight debug view model payloads.

Renderer-independent wire payloads (table, section, model) and the section
and table declaration families, with no imports from the runtime, artifact or
debug-snapshot modules. The concrete declarations, which need those modules,
live in ``openhcs.core.debug_views`` and register into these families, so wire
consumers (agent DTOs, MCP clients) do not pay the runtime import cost. On the
wire a section and a table name their declaration by its registry key.
"""

from __future__ import annotations

import json
from abc import ABC, abstractmethod
from dataclasses import dataclass, fields
from typing import TYPE_CHECKING, ClassVar

from metaclass_registry import AutoRegisterMeta
from python_introspect import JsonValue, to_jsonable

if TYPE_CHECKING:
    from openhcs.core.debug import DebugSnapshot


class DebugViewSectionDeclarationBase(ABC, metaclass=AutoRegisterMeta):
    """One debug inspector section kind; ``name`` is its wire spelling.

    Sections render in registration order.
    """

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type["DebugViewSectionDeclarationBase"]]] = {}

    name: ClassVar[str | None] = None
    title_words: ClassVar[tuple[str, ...]]

    @classmethod
    def default_title(cls) -> str:
        return " ".join(cls.title_words)

    @classmethod
    def section_for_snapshot(cls, snapshot: DebugSnapshot) -> "DebugViewSection | None":
        table = cls.table_for_snapshot(snapshot)
        text = cls.text_for_snapshot(snapshot)
        if table is None and text is None:
            return None
        section = cls.section(table=table, text=text)
        if section.is_empty and not cls.show_empty_snapshot_section():
            return None
        return section

    @classmethod
    def section(
        cls,
        *,
        table: "DebugViewTable | None" = None,
        text: str | None = None,
    ) -> "DebugViewSection":
        return DebugViewSection(
            kind=cls.name, title=cls.default_title(), table=table, text=text
        )

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
    """One debug table over a record type; ``name`` is its wire spelling."""

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[
        dict[str, type["DebugViewTableProjectionDeclarationBase"]]
    ] = {}

    name: ClassVar[str | None] = None
    value_type: ClassVar[type]
    record_type: ClassVar[type | None] = None
    supports_artifact_actions: ClassVar[bool] = False

    @classmethod
    def table_for(cls, values: tuple[object, ...]) -> "DebugViewTable":
        record_type = cls.value_type if cls.record_type is None else cls.record_type
        columns = tuple(declared.name for declared in fields(record_type))
        return DebugViewTable(
            columns=columns,
            rows=tuple(
                tuple(
                    debug_view_cell_text(getattr(cls.table_record(value), column))
                    for column in columns
                )
                for value in values
            ),
            projection=cls.name,
            empty_message=cls.empty_message(),
        )

    @classmethod
    def table_record(cls, value: object) -> object:
        return cls.require_value(value)

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
    projection: str | None = None
    empty_message: str | None = None


@dataclass(frozen=True, slots=True)
class DebugViewSection:
    """One named debug view section."""

    kind: str
    title: str
    table: DebugViewTable | None = None
    text: str | None = None

    @property
    def is_empty(self) -> bool:
        return (self.table is None or not self.table.rows) and not self.text


@dataclass(frozen=True, slots=True)
class DebugViewModel:
    """Renderer-independent debug inspector model."""

    title: str
    sections: tuple[DebugViewSection, ...]


def debug_view_cell_text(value: object) -> str:
    """One table cell: the value's JSON form, rendered as text."""

    return _json_cell_text(to_jsonable(value))


def _json_cell_text(value: JsonValue) -> str:
    if value is None:
        return ""
    if isinstance(value, list):
        return ", ".join(_json_cell_text(item) for item in value)
    if isinstance(value, dict):
        return json.dumps(value, sort_keys=True)
    return str(value)


__all__ = tuple(
    name
    for name, value in tuple(globals().items())
    if isinstance(value, type) and value.__module__ == __name__
)
