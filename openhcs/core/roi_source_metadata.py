"""Persist the existing image-source declaration in native ROI metadata."""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import replace
from typing import ClassVar

from polystore.roi import ROI

from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.serialization.json import to_jsonable


class ROIArchiveSourceMetadata:
    """Native ROI sidecar projection, not a second source-metadata schema."""

    FIELD: ClassVar[str] = "openhcs_image_payload_metadata"

    @classmethod
    def bind(cls, rois: Sequence[ROI], metadata: ImagePayloadMetadata) -> list[ROI]:
        encoded = to_jsonable(metadata)
        return [
            replace(roi, metadata={**roi.metadata, cls.FIELD: encoded}) for roi in rois
        ]

    @classmethod
    def decode(cls, rois: Sequence[ROI]) -> ImagePayloadMetadata | None:
        """Decode once; external ROI archives may have no OpenHCS source binding."""
        encoded = [roi.metadata.get(cls.FIELD) for roi in rois]
        if not any(value is not None for value in encoded):
            return None
        if any(value is None or value != encoded[0] for value in encoded):
            raise ValueError(
                "ROI archive contains missing or conflicting source metadata."
            )
        return ImagePayloadMetadata.from_mapping(encoded[0])

    @classmethod
    def geometry(cls, rois: Sequence[ROI]) -> list[ROI]:
        """Keep transport-only source declarations out of the ROI feature table."""
        return [
            replace(
                roi,
                metadata={
                    key: value
                    for key, value in roi.metadata.items()
                    if key != cls.FIELD
                },
            )
            for roi in rois
        ]
