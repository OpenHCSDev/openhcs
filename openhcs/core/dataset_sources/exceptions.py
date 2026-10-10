"""Typed dataset metadata exceptions."""

from __future__ import annotations

from pathlib import Path


class SourceMetadataError(ValueError):
    """Base class for dataset metadata contract failures."""


class PixelSizeUnavailableError(SourceMetadataError):
    """Raised when a dataset source cannot determine physical pixel size."""

    def __init__(self, image_path: str | Path) -> None:
        self.image_path = Path(image_path)
        super().__init__(f"Pixel size not found in TIFF metadata for {self.image_path}")
