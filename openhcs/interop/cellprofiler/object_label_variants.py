"""Object-label variants CellProfiler's IdentifyPrimaryObjects produces beside its final labels."""

from __future__ import annotations

from openhcs.core.runtime_object_labels import ObjectLabelVariant


class UneditedLabels(ObjectLabelVariant):
    """Labels before size filtering and border removal (CellProfiler's unedited segmentation)."""

    name = "unedited"


class SmallRemovedLabels(ObjectLabelVariant):
    """Labels with only too-small objects removed (CellProfiler's small-removed segmentation)."""

    name = "small_removed"
