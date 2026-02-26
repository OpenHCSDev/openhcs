"""Progress-specific exceptions."""

from typing import Optional


class ProgressError(Exception):
    """Base exception for progress system."""

    pass


class ProgressValidationError(ProgressError):
    """Raised when ProgressEvent validation fails."""

    def __init__(self, message: str, event: dict):
        self.message = message
        self.event = event
        super().__init__(f"{message}: {event}")


class ProgressRegistrationError(ProgressError):
    """Raised when registry operation fails."""

    def __init__(self, message: str, execution_id: Optional[str] = None):
        self.execution_id = execution_id
        super().__init__(message)
