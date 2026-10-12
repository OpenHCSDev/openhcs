"""The running servers this process is connected to follow its custom functions.

The manager tells this owner about each change it makes. Every connected
server is sent the change and then asked for its state until it stops
reporting pending; until then the manager lists the function as preparing, and
a source a server could not acquire is listed as failed to load with the
server's error.
"""

from __future__ import annotations

import logging
import threading
import time
import weakref
from abc import ABC, abstractmethod
from collections.abc import Callable, Hashable
from dataclasses import dataclass

from openhcs.processing.custom_functions.catalogue_changes import (
    CustomFunctionChange,
    ServerCatalogueState,
)
from openhcs.processing.custom_functions.events import custom_function_changed
from openhcs.processing.custom_functions.listing import (
    CustomFunctionInfo,
    CustomFunctionLoadFailure,
    CustomFunctionPreparing,
    PersistedCustomFunction,
)
from openhcs.processing.custom_functions.validation import ValidationError

logger = logging.getLogger(__name__)


class CustomFunctionServer(ABC):
    """A server that runs this process's custom functions."""

    @abstractmethod
    def is_connected(self) -> bool:
        """Whether this process holds a connection to the server now."""

    @abstractmethod
    def server_address(self) -> Hashable:
        """Where the server is; two connections to one address are one server."""

    @abstractmethod
    def follow_custom_function_change(
        self, change: CustomFunctionChange
    ) -> ServerCatalogueState:
        """Send one change; the server starts applying it and answers at once."""

    @abstractmethod
    def custom_catalogue_state(self) -> ServerCatalogueState:
        """Ask what the server holds of the custom functions."""


class ServerReport(ABC):
    """What the connected servers say about one function this process loaded."""

    @abstractmethod
    def listing(self, loaded_here: CustomFunctionInfo) -> PersistedCustomFunction:
        """The entry the manager lists for the function."""


class AcquiredOnServers(ServerReport):
    """Every connected server holds the function (or none is connected)."""

    def listing(self, loaded_here: CustomFunctionInfo) -> PersistedCustomFunction:
        return loaded_here


class PreparingOnServers(ServerReport):
    """A connected server was told and has not finished."""

    def listing(self, loaded_here: CustomFunctionInfo) -> PersistedCustomFunction:
        return CustomFunctionPreparing(
            name=loaded_here.name, file_path=loaded_here.file_path
        )


@dataclass(frozen=True)
class FailedOnServer(ServerReport):
    """A connected server could not load or acquire the source."""

    message: str
    line_number: int

    def listing(self, loaded_here: CustomFunctionInfo) -> PersistedCustomFunction:
        return CustomFunctionLoadFailure(
            name=loaded_here.name,
            file_path=loaded_here.file_path,
            error=ValidationError(
                f"On the execution server: {self.message}", self.line_number
            ),
        )


@dataclass(frozen=True)
class UnacquiredOnServer(ServerReport):
    """A connected server publishes the function without some declared values."""

    values: tuple[str, ...]

    def listing(self, loaded_here: CustomFunctionInfo) -> PersistedCustomFunction:
        return loaded_here.with_unacquired(
            tuple(f"on the execution server: {value}" for value in self.values)
        )


class ConnectedServers:
    """Tell every connected server about a change and keep what each reports."""

    poll_seconds = 0.1
    unanswered_seconds = 60.0
    """How long a server may leave state requests unanswered before it is reported."""

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._servers: weakref.WeakSet[CustomFunctionServer] = weakref.WeakSet()
        self._reports: dict[str, ServerReport] = {}
        self._followers: list[threading.Thread] = []

    def add(self, server: CustomFunctionServer) -> None:
        with self._lock:
            self._servers.add(server)

    def connected(self) -> tuple[CustomFunctionServer, ...]:
        """One connection per server this process is connected to."""
        with self._lock:
            servers = tuple(self._servers)
        by_process = {
            server.server_address(): server
            for server in servers
            if server.is_connected()
        }
        return tuple(by_process.values())

    def tell(self, change: CustomFunctionChange) -> None:
        """Send the change to every connected server; return without waiting."""
        servers = self.connected()
        if not servers:
            return
        follower = threading.Thread(
            target=self._follow,
            args=(servers, change),
            name="openhcs-custom-function-change",
            daemon=True,
        )
        with self._lock:
            for name in change.function_names:
                self._reports[name] = PreparingOnServers()
            self._followers.append(follower)
        follower.start()

    def listing(self, loaded_here: CustomFunctionInfo) -> PersistedCustomFunction:
        """The manager's entry for a function this process loaded."""
        with self._lock:
            report = self._reports.get(loaded_here.name, AcquiredOnServers())
        return report.listing(loaded_here)

    def wait_until_followed(self, timeout: float) -> bool:
        """Wait for every server to finish the changes told so far."""
        deadline = time.monotonic() + timeout
        with self._lock:
            followers = tuple(self._followers)
        for follower in followers:
            follower.join(max(0.0, deadline - time.monotonic()))
        return not any(follower.is_alive() for follower in followers)

    def _follow(
        self,
        servers: tuple[CustomFunctionServer, ...],
        change: CustomFunctionChange,
    ) -> None:
        failed: dict[str, ServerReport] = {}
        unacquired: dict[str, tuple[str, ...]] = {}
        for server in servers:
            try:
                state = self._state_after(server, change)
            except Exception as error:
                logger.warning(
                    "An execution server did not follow %s: %s", change, error
                )
                for name in change.function_names:
                    failed[name] = FailedOnServer(
                        f"the server did not report ({type(error).__name__}: {error})", 0
                    )
                continue
            for failure in state.failed:
                failed[failure.name] = FailedOnServer(
                    failure.message, failure.line_number
                )
            for missing in state.unacquired:
                unacquired[missing.name] = (
                    *unacquired.get(missing.name, ()),
                    *missing.values,
                )
        with self._lock:
            for name in change.function_names:
                self._reports.pop(name, None)
            self._reports.update(
                (name, UnacquiredOnServer(values))
                for name, values in unacquired.items()
            )
            self._reports.update(failed)
            self._followers.remove(threading.current_thread())
        custom_function_changed.emit()

    def _state_after(
        self, server: CustomFunctionServer, change: CustomFunctionChange
    ) -> ServerCatalogueState:
        """The server's state once it no longer reports pending."""
        state = self._answered(lambda: server.follow_custom_function_change(change))
        while state.pending:
            time.sleep(self.poll_seconds)
            state = self._answered(server.custom_catalogue_state)
        return state

    def _answered(
        self, ask: Callable[[], ServerCatalogueState]
    ) -> ServerCatalogueState:
        """Ask until answered; a server forking its workers is silent for a moment.

        Both requests can be repeated: a change the server already applied
        finds its store as the change leaves it.
        """
        give_up = time.monotonic() + self.unanswered_seconds
        while True:
            try:
                return ask()
            except TimeoutError:
                if time.monotonic() > give_up:
                    raise


connected_servers = ConnectedServers()
