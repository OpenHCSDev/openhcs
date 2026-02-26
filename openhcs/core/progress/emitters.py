"""Progress emitter interface and implementations."""

import logging
from abc import ABC, abstractmethod
from typing import Callable
import json

from .types import ProgressEvent

logger = logging.getLogger(__name__)


# =============================================================================
# ProgressEmitter Interface (ABC)
# =============================================================================


class ProgressEmitter(ABC):
    """Abstract base class for progress emitters.

    Follows OpenHCS pattern: explicit ABC with single abstract method.
    Emitter implementations decide WHERE progress goes (callback, ZMQ, noop).

    Design:
    - ABC enforces implementation (no duck typing)
    - Single abstract method (minimal surface area)
    - Subclasses handle transport details
    """

    @abstractmethod
    def emit(self, event: ProgressEvent) -> None:
        """Emit a progress event.

        Args:
            event: ProgressEvent to emit

        Raises:
            ProgressError: If emission fails
        """
        pass


# =============================================================================
# NoopEmitter - For Testing/Disabled Progress
# =============================================================================


class NoopEmitter(ProgressEmitter):
    """No-op emitter for testing or disabled progress tracking.

    Does nothing on emit() - useful for:
    - Unit tests (no side effects)
    - Production runs with progress disabled
    - Dry-run modes
    """

    def emit(self, event: ProgressEvent) -> None:
        """Do nothing (intentionally no-op)."""
        pass


# =============================================================================
# CallbackEmitter - For In-Process Use
# =============================================================================


class CallbackEmitter(ProgressEmitter):
    """Callback-based emitter for in-process use.

    Useful when:
    - No ZMQ required (same process)
    - Direct UI updates needed
    - Testing with mock callbacks
    """

    def __init__(self, callback: Callable[[ProgressEvent], None]):
        """Initialize with callback.

        Args:
            callback: Function to call on each emit
        """
        self.callback = callback

    def emit(self, event: ProgressEvent) -> None:
        """Call callback with event.

        Wraps in try/except to prevent progress failures from
        crashing the pipeline (fail-safe).
        """
        try:
            self.callback(event)
        except Exception as e:
            logger.exception(f"Progress callback failed: {e}")
            # Don't re-raise - progress failure shouldn't stop pipeline


# =============================================================================
# ZMQProgressEmitter - For Cross-Process Communication
# =============================================================================


class ZMQProgressEmitter(ProgressEmitter):
    """ZMQ-based emitter for cross-process communication.

    Serializes ProgressEvent to JSON and sends via ZMQ socket.
    Used for worker processes to communicate progress to main process.
    """

    def __init__(self, socket):
        """Initialize with ZMQ socket.

        Args:
            socket: ZMQ socket (REQ/REP pair) or None
        """
        self.socket = socket

    def emit(self, event: ProgressEvent) -> None:
        """Emit event via ZMQ socket.

        Serializes to JSON dict for ZMQ transport.
        Handles closed socket gracefully (no crash).

        Args:
            event: ProgressEvent to emit
        """
        if self.socket is None:
            logger.debug(f"Progress emit (no socket): {event}")
            return

        try:
            # Serialize to dict (enums → strings for JSON)
            message = event.to_dict()
            json_str = json.dumps(message)
            self.socket.send_string(json_str)
        except Exception as e:
            logger.exception(f"ZMQ emit failed: {e}")
            # Don't re-raise - progress failure shouldn't stop pipeline


# =============================================================================
# LoggingEmitter - For Debugging
# =============================================================================


class LoggingEmitter(ProgressEmitter):
    """Logging emitter for debugging.

    Logs every progress event at INFO level.
    Useful for development and troubleshooting.
    """

    def __init__(self, prefix: str = "PROGRESS"):
        """Initialize with log prefix.

        Args:
            prefix: Prefix for log messages (e.g., "PROGRESS")
        """
        self.prefix = prefix

    def emit(self, event: ProgressEvent) -> None:
        """Log event at INFO level."""
        logger.info(
            f"[{self.prefix}] {event.execution_id} | "
            f"{event.phase.value} | {event.status.value} | "
            f"{event.step_name} | {event.axis_id} | "
            f"{event.percent:.1f}% ({event.completed}/{event.total})"
        )
