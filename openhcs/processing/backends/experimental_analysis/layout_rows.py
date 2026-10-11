"""Nominal helpers for experimental-analysis workbook formats."""

from __future__ import annotations



class ExperimentalLayoutRowRole:
    """Classify layout row labels used by Metaxpress/CX5 analysis workbooks."""

    def __init__(self, row_name: object) -> None:
        self.normalized = str(row_name).lower().replace("_", "").replace(" ", "")

    @property
    def is_replicate_count(self) -> bool:
        return self.normalized in {"n", "ns", "replicate", "replicates"}

    @property
    def is_well_all_replicates(self) -> bool:
        return self.normalized in {"well", "wells"}

    @property
    def is_well_specific_replicate(self) -> bool:
        return self.specific_replicate is not None

    @property
    def specific_replicate(self) -> int | None:
        for prefix in ("wells", "well"):
            if not self.normalized.startswith(prefix):
                continue
            suffix = self.normalized[len(prefix) :]
            if suffix.isdigit():
                return int(suffix)
        return None


