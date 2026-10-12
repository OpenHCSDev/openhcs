"""What the manager lists for each persisted custom-function source."""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass
from pathlib import Path

from openhcs.core.callable_contract import CallableContract
from openhcs.processing.custom_functions.validation import ValidationError


@dataclass(frozen=True)
class PersistedCustomFunction(ABC):
    """
    One persisted custom-function source as the manager lists it.

    Attributes:
        name: Name the source file gives the function
        file_path: Path to source .py file
    """

    name: str
    file_path: Path

    @property
    @abstractmethod
    def list_label(self) -> str:
        """The text a list of custom functions shows for this source."""

    @property
    @abstractmethod
    def backend_label(self) -> str:
        """The memory type or scope, or why there is none."""

    @property
    @abstractmethod
    def status(self) -> str:
        """Whether the source is loaded, and the error when it is not."""

    @property
    def can_retry(self) -> bool:
        """Whether something this source needs failed and can be tried again."""
        return False


@dataclass(frozen=True)
class CustomFunctionLoadFailure(PersistedCustomFunction):
    """
    A persisted source that could not be loaded.

    Attributes:
        error: What preparing or publishing the source raised
    """

    error: Exception

    @property
    def message(self) -> str:
        if isinstance(self.error, ValidationError):
            return self.error.message
        return f"{type(self.error).__name__}: {self.error}"

    @property
    def line_number(self) -> int:
        """Source line of the error, 0 when the error has none."""
        if isinstance(self.error, ValidationError):
            return self.error.line_number
        return 0

    @property
    def list_label(self) -> str:
        return f"{self.name} (failed to load)"

    @property
    def backend_label(self) -> str:
        return "failed to load"

    @property
    def status(self) -> str:
        return f"Failed to load: {self.describe()}"

    @property
    def can_retry(self) -> bool:
        return True

    def describe(self) -> str:
        """File, line and error as one line of text."""
        location = self.file_path.name
        if self.line_number:
            location = f"{location}, line {self.line_number}"
        return f"{location}: {self.message}"


@dataclass(frozen=True)
class CustomFunctionInfo(PersistedCustomFunction):
    """
    A persisted source that loaded.

    Attributes:
        contract: Original callable contract, also owning scope and memory type
    """

    contract: CallableContract

    @property
    def list_label(self) -> str:
        return self.name

    @property
    def status(self) -> str:
        return "Loaded"

    @property
    def memory_type(self) -> str | None:
        return self.contract.input_memory_type

    @property
    def doc(self) -> str:
        return self.contract.func.__doc__ or ""

    @property
    def backend_label(self) -> str:
        return self.memory_type or self.contract.execution_scope.value

    def with_unacquired(self, values: tuple[str, ...]) -> CustomFunctionInfo:
        """This entry, also listing declared values that could not be acquired."""
        if not values:
            return self
        return CustomFunctionMissingValues(
            name=self.name,
            file_path=self.file_path,
            contract=self.contract,
            unacquired=values,
        )


@dataclass(frozen=True)
class CustomFunctionMissingValues(CustomFunctionInfo):
    """A source that loaded, with declared values that could not be acquired.

    A pipeline can use the values that were acquired. One that selects a
    missing value has it tried again when the pipeline is prepared.
    """

    unacquired: tuple[str, ...]
    """Each missing value with its cause, as ``model='large' (ConnectionError: ...)``."""

    def with_unacquired(self, values: tuple[str, ...]) -> CustomFunctionInfo:
        return CustomFunctionInfo.with_unacquired(self, (*self.unacquired, *values))

    @property
    def list_label(self) -> str:
        return f"{self.name} (values not acquired)"

    @property
    def status(self) -> str:
        return "Loaded; not acquired: " + "; ".join(self.unacquired)

    @property
    def can_retry(self) -> bool:
        return True


@dataclass(frozen=True)
class CustomFunctionPreparing(PersistedCustomFunction):
    """A source that loaded here and that a connected server is still preparing."""

    @property
    def list_label(self) -> str:
        return f"{self.name} (preparing)"

    @property
    def backend_label(self) -> str:
        return "preparing"

    @property
    def status(self) -> str:
        return "Preparing on the execution server"
