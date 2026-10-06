"""Fragmented diagnostic labels retain parent identity across real materialization."""

import json
from collections import Counter
from pathlib import Path
from zipfile import ZipFile

import numpy as np
import pytest
import tifffile
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
from polystore.roi import ROI_ZIP_METADATA_MEMBER, load_rois_from_zip

from openhcs.core.runtime_object_labels import (
    ObjectLabelPayload,
    ObjectLabelVariantData,
)
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.processing.materialization import (
    ImageFileOptions,
    MaterializationSpec,
    ROIOptions,
    materialization_outputs,
)


def fragmented_labels():
    labels = np.zeros((128, 128), dtype=np.int32)
    labels[4:124:4, 4:124:4] = 188
    labels[1:3, 1:3] = 7
    labels[125:127, 125:127] = 42
    return labels


def _payload(labels=None):
    return ObjectLabelPayload(
        variant_data=ObjectLabelVariantData(
            labels=fragmented_labels() if labels is None else labels
        ),
        source_path="/synthetic/raw.tif",
        source_component_metadata={"well": "A01", "channel": 1},
        source_spatial_domain=SourceSpatialDomain(
            origin_yx=(10, 20),
            source_shape_yx=(256, 256),
        ),
    )


def test_archive_fragments_keep_parent_label_and_source_geometry(tmp_path):
    filemanager = FileManager({"disk": DiskStorageBackend()})
    outputs = materialization_outputs(
        MaterializationSpec(ROIOptions(min_area=1)),
        _payload(),
        str(tmp_path / "fragmented"),
        filemanager,
    )
    archive = next(output for output in outputs if output.path.endswith(".roi.zip"))
    summary = next(output for output in outputs if output.path.endswith(".txt"))
    assert "Segmentation ROIs: 3 parent labels\n" in summary.content
    parents = archive.content
    assert Counter(roi.metadata["label"] for roi in parents) == {7: 1, 42: 1, 188: 1}
    assert Counter({roi.metadata["label"]: len(roi.shapes) for roi in parents}) == {
        7: 1,
        42: 1,
        188: 900,
    }
    filemanager.save(parents, archive.path, "disk")
    with ZipFile(archive.path) as zipped:
        members = [name for name in zipped.namelist() if name.endswith(".roi")]
        assert len(members) == 902
        metadata = json.loads(zipped.read(ROI_ZIP_METADATA_MEMBER))
        assert Counter(value["label"] for value in metadata.values()) == {
            7: 1,
            42: 1,
            188: 900,
        }
    # Native reopen flattens shapes, but every member still owns its parent label.
    restored = load_rois_from_zip(Path(archive.path))
    assert Counter(roi.metadata["label"] for roi in restored) == {7: 1, 42: 1, 188: 900}
    fragmented = next(roi for roi in restored if roi.metadata["label"] == 188)
    assert fragmented.metadata["area"] == 900
    assert fragmented.metadata["centroid"] == (72.0, 82.0)
    coordinates = np.concatenate(
        [roi.shapes[0].coordinates for roi in restored if roi.metadata["label"] == 188]
    )
    assert coordinates[:, 0].min() == pytest.approx(13.5)
    assert coordinates[:, 0].max() == pytest.approx(130.5)
    assert coordinates[:, 1].min() == pytest.approx(23.5)
    assert coordinates[:, 1].max() == pytest.approx(140.5)


@pytest.mark.parametrize("with_holes_and_borders", (False, True))
def test_declared_raster_selection_preserves_parent_labels_without_roi_extraction(
    tmp_path, monkeypatch, with_holes_and_borders
):
    monkeypatch.setattr(
        "polystore.roi.extract_rois_from_labeled_mask",
        lambda *args, **kwargs: pytest.fail("Unselected ROI extraction ran"),
    )
    labels = fragmented_labels()
    if with_holes_and_borders:
        labels[:32, :32] = 7
        labels[8:24, 8:24] = 0
        labels[12:16, 12:16] = 42
        labels[-1, -1] = 188
    filemanager = FileManager({"disk": DiskStorageBackend()})
    outputs = materialization_outputs(
        MaterializationSpec(
            ROIOptions(min_area=1), ImageFileOptions(filename_suffix=".tif")
        ),
        _payload(labels),
        str(tmp_path / "fragmented"),
        filemanager,
        output_path_filter=lambda path: path.suffix == ".tif",
    )
    assert len(outputs) == 1
    filemanager.save(outputs[0].content, outputs[0].path, "disk")
    np.testing.assert_array_equal(tifffile.imread(outputs[0].path), labels)
