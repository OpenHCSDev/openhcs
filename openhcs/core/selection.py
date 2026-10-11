"""Shared selection carriers for UI and agent-facing projections."""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Iterable
from dataclasses import dataclass
from typing import ClassVar

from metaclass_registry import AutoRegisterMeta


class SelectionScope(ABC, metaclass=AutoRegisterMeta):
    """Whether a view or document covers the selected items or all of them.

    ``name`` is the scope's spelling on the wire and in CLI choices.
    """

    __registry_key__ = "name"
    __skip_if_no_key__ = True

    name: ClassVar[str | None] = None

    @staticmethod
    def named(name: str) -> type["SelectionScope"]:
        scope = SelectionScope.__registry__.get(name)
        if scope is None:
            raise ValueError(
                f"Unknown selection mode {name!r}; expected one of "
                f"{tuple(SelectionScope.__registry__)!r}."
            )
        return scope

    @staticmethod
    @abstractmethod
    def keeps(selected: bool) -> bool:
        """Whether an item with this selection state is in scope."""

    @staticmethod
    @abstractmethod
    def pick(selected: tuple[str, ...], every: tuple[str, ...]) -> tuple[str, ...]:
        """The ids in scope, given the selected ids (in selection order) and all ids."""


class SelectedItems(SelectionScope):
    name = "selected"

    @staticmethod
    def keeps(selected: bool) -> bool:
        return selected

    @staticmethod
    def pick(selected: tuple[str, ...], every: tuple[str, ...]) -> tuple[str, ...]:
        return selected


class AllItems(SelectionScope):
    name = "all"

    @staticmethod
    def keeps(selected: bool) -> bool:
        return True

    @staticmethod
    def pick(selected: tuple[str, ...], every: tuple[str, ...]) -> tuple[str, ...]:
        return every


@dataclass(frozen=True, kw_only=True, slots=True)
class SelectionModeCarrier:
    selection_mode: str | None = None

    def resolved_selection_mode(self, default: type[SelectionScope]) -> str:
        """The requested mode's wire spelling, or ``default``'s."""
        if self.selection_mode is None:
            return default.name
        return SelectionScope.named(self.selection_mode).name

    def selection_scope(self, default: type[SelectionScope]) -> type[SelectionScope]:
        return SelectionScope.named(self.resolved_selection_mode(default))


@dataclass(frozen=True, kw_only=True, slots=True)
class SelectedScopeIdsCarrier(SelectionModeCarrier):
    selected_scope_ids: tuple[str, ...] = ()


@dataclass(frozen=True, slots=True)
class SelectedScopeIdsArgument(SelectedScopeIdsCarrier):
    """Nominal adapter for optional external selected-scope collections."""

    @classmethod
    def from_optional_iterable(
        cls,
        value: Iterable[str] | None,
    ) -> "SelectedScopeIdsArgument":
        if value is None:
            return cls(selected_scope_ids=())
        return cls(selected_scope_ids=tuple(value))
