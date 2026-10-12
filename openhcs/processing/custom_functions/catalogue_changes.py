"""The changes a session makes to its custom functions, as a server follows them.

Registering a custom function is making it usable, and usable includes
acquired on every server that will run it. Each operation of the manager
(create, edit, delete, retry) is one member of this family. The member is the
wire request a connected server receives, and it carries its own effect there:
the server makes its store hold what the session's store holds and brings its
loaded functions up to date, which prepares a new source, prepares an edited
one again, withdraws what is gone and tries a failed acquisition again.
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
    def before_loading(
        self, manager: "CustomFunctionManager", admit_write: WriteAdmission
    ) -> None:
        """What a server does so that loading its sources has this change's effect."""

    def apply_on_server(
        self, manager: "CustomFunctionManager", admit_write: WriteAdmission
    ) -> None:
        """The whole effect in a server: this member's step, then its loaded functions.

        Loading in a serving process acquires what a source declares, so a new
        or edited source is acquired here, a source that is gone is no longer
        published, and a source whose failure was forgotten is tried again.
        """
        self.before_loading(manager, admit_write)
        manager.load_all_custom_functions()


@dataclass(frozen=True)
class CustomFunctionCreated(CustomFunctionChange):
    """A new source was stored: the server prepares it."""

    name: str
    code: str

    @property
    def function_names(self) -> tuple[str, ...]:
        return (self.name,)

    def before_loading(
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

    def before_loading(
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

    def before_loading(
        self, manager: "CustomFunctionManager", admit_write: WriteAdmission
    ) -> None:
        manager.drop_source(self.name, admit_write)


@dataclass(frozen=True)
class CustomFunctionRetried(CustomFunctionChange):
    """A failed acquisition is tried again: the server forgets the failure and loads.

    The store is not changed. A source that failed to load is loaded and
    acquired again; a published function tries again the values it could not
    acquire.
    """

    name: str

    @property
    def function_names(self) -> tuple[str, ...]:
        return (self.name,)

    def before_loading(
        self, manager: "CustomFunctionManager", admit_write: WriteAdmission
    ) -> None:
        manager.acquire_again(self.name)


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
class ValuesUnacquiredOnServer:
    """A function a server publishes, and the declared values it could not acquire."""

    name: str
    values: tuple[str, ...]
    """Each value with the cause, as ``model='large' (ConnectionError: ...)``."""


@dataclass(frozen=True)
class ServerCatalogueState:
    """What one server reports of the custom functions.

    ``pending`` is the server's own catalogue-preparation state: while it is
    true the server is still loading or acquiring, and the other fields say
    nothing yet. ``failed`` are sources that did not load; ``unacquired`` are
    loaded functions with values the server could not acquire.
    """

    pending: bool
    loaded: tuple[CustomFunctionSource, ...] = ()
    failed: tuple[SourceFailedOnServer, ...] = ()
    unacquired: tuple[ValuesUnacquiredOnServer, ...] = ()
