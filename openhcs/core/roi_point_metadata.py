"""Exact fractional Z retained beside ImageJ's integer-plane point ROI."""

from __future__ import annotations

from dataclasses import dataclass, replace
from math import isfinite
from typing import ClassVar, Mapping

from polystore.roi import ROI


@dataclass(frozen=True, slots=True)
class ROIFractionalZ:
    """The Z coordinate ImageJ's 2D point shape cannot represent."""

    value: float
    FIELD: ClassVar[str] = "openhcs_fractional_z"

    def __post_init__(self) -> None:
        if isinstance(self.value, bool) or not isfinite(self.value):
            raise ValueError("ROI fractional Z must be a finite real coordinate.")

    def bind(self, roi: ROI) -> ROI:
        return replace(roi, metadata={**roi.metadata, self.FIELD: float(self.value)})

    @classmethod
    def decode(cls, metadata: Mapping[str, object]) -> ROIFractionalZ | None:
        value = metadata.get(cls.FIELD)
        if value is None:
            return None
        if isinstance(value, bool) or not isinstance(value, (int, float)):
            raise ValueError("ROI fractional Z must be numeric.")
        return cls(float(value))
