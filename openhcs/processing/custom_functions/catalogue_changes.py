"""The changes a session makes to its custom functions, as a server follows them.

Registering a custom function is making it usable, and usable includes
acquired on every server that will run it. Each operation of the manager
(create, edit, delete) is one member of this family. The member is the wire
request a connected server receives, and it carries its own effect there:
the server makes its store hold what the session's store holds and brings its
loaded functions up to date, which prepares a new source, prepares an edited
one again and withdraws what is gone.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, ClassVar

from openhcs.processing.custom_functions.source_namespace import CustomFunctionSource

if TYPE_CHECKING:
    from openhcs.processing.custom_functions.manager import CustomFunctionManager

WriteAdmission = Callable[[Path], Path]
"""Checks one path the server is about to write; raises when it may not."""


@dataclass(frozen=True)
class CustomFunctionChange(ABC):
    """One change of a session's custom functions that its servers follow."""

    wire_type: ClassVar[str] = "openhcs_custom_function_change"
    """Control message type of every member; the member itself is the payload."""

    change_key: ClassVar[str] = "change"

    @property
    @abstractmethod
    def function_names(self) -> tuple[str, ...]:
        """The functions whose state on a server this change decides."""

    @abstractmethod
    def change_store(
        self, manager: "CustomFunctionManager", admit_write: WriteAdmission
    ) -> None:
        """Make the server's store hold what the session's store holds."""

    def apply_on_server(
        self, manager: "CustomFunctionManager", admit_write: WriteAdmission
    ) -> None:
        """The whole effect in a server: its store, then its loaded functions.

        Loading in a serving process acquires what a source declares, so a new
        or edited source is acquired here, and a source that is gone is no
        longer published.
        """
        self.change_store(manager, admit_write)
        manager.load_all_custom_functions()


@dataclass(frozen=True)
class CustomFunctionCreated(CustomFunctionChange):
    """A new source was stored: the server prepares it."""

    name: str
    code: str

    @property
    def function_names(self) -> tuple[str, ...]:
        return (self.name,)

    def change_store(
        self, manager: "CustomFunctionManager", admit_write: WriteAdmission
    ) -> None:
        manager.hold_source(self.name, self.code, admit_write)


@dataclass(frozen=True)
class CustomFunctionEdited(CustomFunctionChange):
    """A source was replaced: the server prepares the new revision and withdraws the old."""

    old_name: str
    name: str
    code: str

    @property
    def function_names(self) -> tuple[str, ...]:
        return tuple(dict.fromkeys((self.old_name, self.name)))

    def change_store(
        self, manager: "CustomFunctionManager", admit_write: WriteAdmission
    ) -> None:
        manager.hold_source(self.name, self.code, admit_write)
        if self.old_name != self.name:
            manager.drop_source(self.old_name, admit_write)


@dataclass(frozen=True)
class CustomFunctionDeleted(CustomFunctionChange):
    """A source was deleted: the server withdraws the function."""

    name: str

    @property
    def function_names(self) -> tuple[str, ...]:
        return (self.name,)

    def change_store(
        self, manager: "CustomFunctionManager", admit_write: WriteAdmission
    ) -> None:
        manager.drop_source(self.name, admit_write)


@dataclass(frozen=True)
class CustomCatalogueStateRequest:
    """Ask a server what it holds of the custom functions, without changing it."""

    wire_type: ClassVar[str] = "openhcs_custom_function_state"


@dataclass(frozen=True)
class SourceFailedOnServer:
    """One source a server could not load or acquire."""

    name: str
    message: str
    line_number: int


@dataclass(frozen=True)
class ServerCatalogueState:
    """What one server reports of the custom functions.

    ``pending`` is the server's own catalogue-preparation state: while it is
    true the server is still loading or acquiring, and the other fields say
    nothing yet.
    """

    pending: bool
    loaded: tuple[CustomFunctionSource, ...] = ()
    failed: tuple[SourceFailedOnServer, ...] = ()

    state_key: ClassVar[str] = "custom_catalogue_state"
