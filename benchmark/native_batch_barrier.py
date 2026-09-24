"""Synchronize prepared native batch starts without timing the wait itself."""

from __future__ import annotations

import time
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class NativeBatchStartBarrier:
    """One job's membership in a file-backed, per-repetition start barrier."""

    root: Path
    job_count: int
    job_index: int

    def __post_init__(self) -> None:
        if self.job_count < 2 or not 0 <= self.job_index < self.job_count:
            raise ValueError("Native batch barrier requires a valid multi-job index.")

    def wait(self, repetition: int, *, timeout_seconds: float = 120.0) -> None:
        """Release together after every declared job is ready for this repeat."""

        if repetition < 0 or timeout_seconds <= 0:
            raise ValueError(
                "Native batch barrier requires a timed repetition and timeout."
            )
        self.root.mkdir(parents=True, exist_ok=True)
        ready_paths = tuple(
            self.root / f"repetition_{repetition}_job_{index}.ready"
            for index in range(self.job_count)
        )
        ready_paths[self.job_index].touch(exist_ok=False)
        deadline = time.monotonic() + timeout_seconds
        while not all(path.is_file() for path in ready_paths):
            if time.monotonic() >= deadline:
                missing = tuple(
                    index
                    for index, path in enumerate(ready_paths)
                    if not path.is_file()
                )
                raise TimeoutError(
                    "Native batch start barrier timed out waiting for jobs "
                    f"{missing} in repetition {repetition}."
                )
            time.sleep(0.01)
