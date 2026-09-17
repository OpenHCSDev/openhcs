"""Nominal image-tile blending contract shared by assembly backends."""

from collections.abc import Callable
from dataclasses import dataclass
from enum import Enum
from math import floor, isfinite

from arraybridge import MemoryType, detect_memory_type


class TileBlendMethod(Enum):
    """Weighting strategy used where assembled image tiles overlap."""

    NONE = "none"
    FIXED = "fixed"
    DYNAMIC = "dynamic"


@dataclass(frozen=True, slots=True)
class SubpixelTilePlacement:
    """One positive fractional translation on an acquisition-relative canvas.

    Pixels and their blending coverage are resampled together. The extra row or
    column retains the fractional boundary instead of cropping shifted pixels.
    The framework's affine sampler is the only backend-specific behavior hook.
    """

    target_xy: tuple[float, float]
    source_shape_yx: tuple[int, int]

    def __post_init__(self) -> None:
        if any(not isfinite(value) for value in self.target_xy):
            raise ValueError("Tile target coordinates must be finite.")

    @property
    def origin_yx(self) -> tuple[int, int]:
        x, y = self.target_xy
        return floor(y), floor(x)

    @property
    def fractional_yx(self) -> tuple[float, float]:
        x, y = self.target_xy
        iy, ix = self.origin_yx
        return y - iy, x - ix

    @property
    def output_shape_yx(self) -> tuple[int, int]:
        fy, fx = self.fractional_yx
        height, width = self.source_shape_yx
        return height + int(fy > 0), width + int(fx > 0)

    def weighted_samples(self, tile, mask, affine_sampler: Callable) -> tuple:
        """Translate preweighted pixels and coverage using identical coordinates."""
        fy, fx = self.fractional_yx
        if fy == 0 and fx == 0:
            return tile * mask, mask
        array_module = MemoryType(detect_memory_type(tile)).import_module()
        identity_matrix = array_module.ones(2, dtype=array_module.float64)
        kwargs = {
            "offset": (-fy, -fx),
            "output_shape": self.output_shape_yx,
            "order": 1,
            "mode": "grid-constant",
            "cval": 0.0,
            "prefilter": False,
        }
        return affine_sampler(tile * mask, identity_matrix, **kwargs), affine_sampler(
            mask, identity_matrix, **kwargs
        )
