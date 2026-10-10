"""Kinds of dataset scope: what one dataset row stands for.

A plain dataset scope is its root directory. A domain may register other
kinds, for example one row per pipeline file found in the root; each kind
spells its scope id, names its rows, offers rows for a newly added root and
prepares the input workspace that initialization reads.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, ClassVar
from urllib.parse import quote, unquote

from metaclass_registry import AutoRegisterMeta

from openhcs.core.dataset_sources.discovery import domain_registry_config

if TYPE_CHECKING:
    from openhcs.core.input_workspace import InputWorkspacePreparationResult


@dataclass(frozen=True, slots=True)
class DatasetScope:
    """One parsed dataset scope id."""

    scope_id: str
    root: Path
    kind: type["DatasetScopeKind"]
    pipeline_path: Path | None = None
    execution_root: Path | None = None
    """A separately prepared root the dataset executes on (none: its root)."""

    @property
    def plate_id(self) -> str:
        """The identity an execution submission names for this dataset."""

        return self.kind.plate_id(self)

    @property
    def initialized_root(self) -> Path:
        """The root initialization writes metadata into."""

        return self.root if self.execution_root is None else self.execution_root

    @property
    def display_name(self) -> str:
        return self.kind.display_name(self)

    def code_value(self) -> Path | str:
        """The value a code document spells for this scope."""

        return self.kind.code_value(self)

    def owns_object_state_scope(self, scope_id: str) -> bool:
        """Whether an ObjectState scope belongs to this dataset."""

        return scope_id == self.scope_id or scope_id.startswith(
            f"{self.scope_id}{SCOPE_SEGMENT_SEPARATOR}"
        )

    def prepare_input_workspace(self) -> "InputWorkspacePreparationResult | None":
        return self.kind.prepare_input_workspace(self)

    @classmethod
    def parse(cls, scope_id: str) -> "DatasetScope":
        """Parse a scope id through the kind whose marker it carries."""

        for kind in DatasetScopeKind.__registry__.values():
            if kind.marker in scope_id:
                return kind.parse(scope_id)
        return PlainDatasetScope.parse(scope_id)

    @classmethod
    def of_root(cls, root: Path | str) -> "DatasetScope":
        return PlainDatasetScope.parse(str(Path(root)))


@dataclass(frozen=True, slots=True)
class DatasetScopeOffer:
    """One row a kind offers for a newly added root."""

    scope: DatasetScope
    select_by_default: bool = False


class DatasetScopeKind(ABC, metaclass=AutoRegisterMeta):
    """How one kind of dataset row is identified, named and prepared."""

    __registry_config__ = domain_registry_config(
        key_attribute="marker",
        registry_name="dataset scope kind",
    )
    marker: ClassVar[str | None] = None
    """Text separating the root from the kind's own part of a scope id."""

    @classmethod
    @abstractmethod
    def parse(cls, scope_id: str) -> DatasetScope: ...

    @classmethod
    def display_name(cls, scope: DatasetScope) -> str:
        return scope.root.name

    @classmethod
    def plate_id(cls, scope: DatasetScope) -> str:
        return scope.scope_id

    @classmethod
    def code_value(cls, scope: DatasetScope) -> Path | str:
        return scope.scope_id

    @classmethod
    def offers(cls, root: Path) -> tuple[DatasetScopeOffer, ...]:
        """Rows this kind offers for ``root`` (none when it does not apply)."""

        del root
        return ()

    @classmethod
    def prepare_input_workspace(
        cls,
        scope: DatasetScope,
    ) -> "InputWorkspacePreparationResult | None":
        """The input workspace initialization binds (none for a plain root)."""

        del scope
        return None

    @staticmethod
    def offers_for_root(root: Path | str) -> tuple[DatasetScopeOffer, ...]:
        """Rows for a newly added root: a registered kind's offer, else the root."""

        root_path = Path(root)
        for kind in DatasetScopeKind.__registry__.values():
            offers = kind.offers(root_path)
            if offers:
                return offers
        return (DatasetScopeOffer(DatasetScope.of_root(root_path), True),)


class PlainDatasetScope(DatasetScopeKind):
    """A dataset row that is its root directory."""

    @classmethod
    def parse(cls, scope_id: str) -> DatasetScope:
        root = Path(scope_id)
        return DatasetScope(scope_id=str(root), root=root, kind=cls)

    @classmethod
    def code_value(cls, scope: DatasetScope) -> Path | str:
        return scope.root


class PreparedWorkspaceScope(DatasetScopeKind):
    """A source root executed on a workspace prepared separately.

    The row's identity, and the plate id its executions name, stays the source
    root; initialization binds the prepared root as the execution root.
    """

    marker = "#openhcs-execution-root="

    @classmethod
    def scope_for(cls, root: Path | str, execution_root: Path | str) -> DatasetScope:
        root_path = Path(root)
        execution_path = Path(execution_root)
        return DatasetScope(
            scope_id=f"{root_path}{cls.marker}{quote(str(execution_path), safe='/')}",
            root=root_path,
            kind=cls,
            execution_root=execution_path,
        )

    @classmethod
    def parse(cls, scope_id: str) -> DatasetScope:
        root_text, encoded = scope_id.rsplit(cls.marker, maxsplit=1)
        return cls.scope_for(root_text, unquote(encoded))

    @classmethod
    def plate_id(cls, scope: DatasetScope) -> str:
        return str(scope.root)

    @classmethod
    def prepare_input_workspace(
        cls,
        scope: DatasetScope,
    ) -> "InputWorkspacePreparationResult":
        from openhcs.core.input_workspace import InputWorkspacePreparationResult

        return InputWorkspacePreparationResult(
            original_source_root=scope.root,
            execution_plate_path=scope.execution_root,
        )


SCOPE_SEGMENT_SEPARATOR = "::"
