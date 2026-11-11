"""Runtime profiling event sink shared by execution adapters."""

from __future__ import annotations

from contextlib import contextmanager
from contextvars import ContextVar
from copy import deepcopy
from dataclasses import dataclass
import logging
import os
import time
from enum import Enum
from collections.abc import Iterator, Mapping
from typing import ClassVar

PROFILE_RUNTIME_ENV = "OPENHCS_PROFILE_FUNCTION_RUNTIME"
PROFILE_RUNTIME_PATH_ENV = "OPENHCS_PROFILE_FUNCTION_RUNTIME_PATH"
RuntimeProfileFieldValue = (
    str
    | int
    | float
    | bool
    | Enum
    | None
    | tuple["RuntimeProfileFieldValue", ...]
    | Mapping[str, "RuntimeProfileFieldValue"]
)


@dataclass(frozen=True, slots=True)
class RuntimeProfileTimer:
    """Runtime-profile timer that owns disabled-profile elapsed semantics."""

    enabled: bool
    started_at: float

    @classmethod
    def start(cls) -> "RuntimeProfileTimer":
        """Start a timer under the current profile sink state."""
        if RuntimeProfileLogger.enabled():
            return cls(enabled=True, started_at=time.perf_counter())
        return cls(enabled=False, started_at=0.0)

    def elapsed(self) -> float:
        """Return elapsed seconds, or the declared disabled-profile value."""
        if not self.enabled:
            return 0.0
        return time.perf_counter() - self.started_at


class RuntimeProfileLogger:
    """Own detached profile records for one worker run, then emit them once."""

    _active: ClassVar[ContextVar[RuntimeProfileLogger | None]] = ContextVar(
        "openhcs_runtime_profile", default=None
    )

    def __init__(self, **fields: RuntimeProfileFieldValue) -> None:
        self.output_path = os.environ.get(PROFILE_RUNTIME_PATH_ENV)
        self._fields = tuple(deepcopy(fields).items())
        self._records: list[
            tuple[
                logging.Logger,
                str,
                float,
                tuple[tuple[str, RuntimeProfileFieldValue], ...],
            ]
        ] = []

    @staticmethod
    def enabled() -> bool:
        return os.environ.get(PROFILE_RUNTIME_ENV, "").lower() in {"1", "true", "yes"}

    @classmethod
    @contextmanager
    def run(cls, **fields: RuntimeProfileFieldValue) -> Iterator[None]:
        """Bind fresh worker-local ownership, including after fork or cancellation."""
        profile = cls(**fields) if cls.enabled() else None
        token = cls._active.set(profile)
        failure: BaseException | None = None
        try:
            yield
        except BaseException as error:
            failure = error
            raise
        finally:
            cls._active.reset(token)
            if profile is not None:
                try:
                    profile.flush()
                except Exception as error:
                    if failure is None:
                        raise
                    failure.add_note(f"Runtime profile flush failed: {error}")

    def flush(self) -> None:
        """Format after execution and append the completed run in one write."""
        records, self._records = self._records, []
        if not records:
            return
        started_at = time.perf_counter()
        lines = []
        for logger, label, seconds, fields in records:
            field_text = " ".join(f"{key}={value}" for key, value in fields)
            line = f"RUNTIME_PROFILE {label} {seconds:.6f}s {field_text}"
            logger.info("%s", line)
            lines.append(line)
        if self.output_path is not None:
            with open(self.output_path, "a", encoding="utf-8") as handle:
                handle.write("\n".join(lines) + "\n")
        logging.getLogger(__name__).info(
            "RUNTIME_PROFILE_FLUSH %.6fs records=%d",
            time.perf_counter() - started_at,
            len(records),
        )

    @classmethod
    def log(
        cls,
        logger: logging.Logger,
        label: str,
        seconds: float,
        **fields: RuntimeProfileFieldValue,
    ) -> None:
        profile = cls._active.get()
        if profile is None:
            return
        profile._records.append(
            (logger, label, seconds, profile._fields + tuple(deepcopy(fields).items()))
        )


@dataclass(frozen=True, slots=True)
class RuntimeProfiler:
    """Runtime-profile emitter bound to a module logger."""

    logger: logging.Logger

    def enabled(self) -> bool:
        return RuntimeProfileLogger.enabled()

    def log(self, label: str, seconds: float, **fields: RuntimeProfileFieldValue) -> None:
        RuntimeProfileLogger.log(self.logger, label, seconds, **fields)
