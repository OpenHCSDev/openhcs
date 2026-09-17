"""Append-only preservation for diagnostic attempts."""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from benchmark.agent_validation.contracts import AttemptRecord
from openhcs.serialization.json import to_jsonable


@dataclass(frozen=True, slots=True)
class AttemptJournal:
    """Write each attempt once beneath a run-owned root."""

    root: Path

    def preserve(self, record: AttemptRecord) -> Path:
        """Write one typed receipt without replacing an earlier attempt."""

        task_root = self.root / record.task_id
        attempt_root = task_root / record.attempt_id
        attempt_root.mkdir(parents=True, exist_ok=True)
        receipt_path = attempt_root / "attempt.json"
        with receipt_path.open("x", encoding="utf-8") as handle:
            json.dump(to_jsonable(record), handle, indent=2, sort_keys=True)
            handle.write("\n")
        return receipt_path
