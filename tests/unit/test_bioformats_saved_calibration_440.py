"""Header-only BioFormats preparation through the original durable source owners."""

import json
from types import SimpleNamespace

import numpy as np
import pytest
from polystore.bioformats_java import BioFormatsJavaContext
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
from polystore.roi import load_rois_from_zip

from openhcs.constants.constants import Backend
from openhcs.core.roi_source_metadata import ROIArchiveSourceMetadata
from openhcs.core.runtime_image_loading import ImagePayloadSourceMetadataContext
from openhcs.core.runtime_object_labels import ObjectLabelPayload, ObjectLabelVariantData
from openhcs.core.source_bindings import (
    MetadataSelector, NamedSourceBinding, SourceBindingsConfig, SourceSelector,
)
from openhcs.core.source_image_provenance import SourceImageIdentity
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.microscopes.bioformats import BioFormatsHandler
from openhcs.microscopes.bioformats_adapter import SourcePlaneStoreAdapter
from openhcs.microscopes.openhcs import OpenHCSMetadataHandler
from openhcs.processing.materialization import MaterializationSpec, ROIOptions, materialize
from tests.unit.test_bioformats_java_adapter import (
    FakeBioFormatsContext, FakeBioFormatsMetadata,
)


class _Header(FakeBioFormatsMetadata):
    """New non-plate metadata declaration, with no image decoding capability."""

    def getPlateCount(self):
        return 0


def _prepare(tmp_path, monkeypatch, pixel_size):
    source = tmp_path / "engineering.czi"
    source.touch()
    context = FakeBioFormatsContext(
        {source.name: _Header(pixel_size=pixel_size)}, declared_suffixes=(".czi",)
    )
    # The only external provider is the existing controlled OME header fixture.
    monkeypatch.setattr(BioFormatsJavaContext, "instance", classmethod(lambda cls: context))
    filemanager = FileManager({Backend.DISK.value: DiskStorageBackend()})
    bindings = SourceBindingsConfig(bindings=(NamedSourceBinding(
        alias="engineering",
        selector=SourceSelector(metadata=(MetadataSelector("channel", "2"),)),
    ),))
    handler = BioFormatsHandler(filemanager, source_bindings_config=bindings)
    dataset = handler.source_metadata_handler.source_dataset(tmp_path)
    handler.initialize_workspace(tmp_path, filemanager)
    document = json.loads((tmp_path / "openhcs_metadata.json").read_text())
    return source, dataset, document["subdirectories"]["."], filemanager


@pytest.mark.parametrize("pixel_size", (0.65, 0.217))
def test_nonplate_calibration_survives_preparation_and_native_roi_roundtrip(
    tmp_path, monkeypatch, pixel_size
):
    source, dataset, persisted, filemanager = _prepare(tmp_path, monkeypatch, pixel_size)
    expected = SourceVoxelSpacing((pixel_size, pixel_size))
    assert dataset.pixel_size == pixel_size
    assert persisted["pixel_size"] == pixel_size
    (virtual_path,) = persisted["image_files"]
    source_metadata = persisted["source_metadata"][virtual_path]
    assert SourceVoxelSpacing.from_source_metadata(source_metadata) == expected
    assert source_metadata["channel"] == "2"
    reopened = OpenHCSMetadataHandler(filemanager)
    assert reopened.get_pixel_size(tmp_path) == pixel_size
    assert reopened.get_metadata_pixel_size(tmp_path) == pixel_size

    # Exercise normal runtime metadata and the real registered ROI writer; these
    # 8x8 arrays are engineering fixtures, not pixels from the .czi placeholder.
    metadata = ImagePayloadSourceMetadataContext(SourceImageIdentity(
        path=str(source), component_metadata=source_metadata,
    )).metadata(np.zeros((8, 8), dtype=np.uint8))
    assert metadata.source_voxel_spacing == expected
    labels = np.zeros((8, 8), dtype=np.int32)
    labels[2:6, 3:7] = 12
    payload = ObjectLabelPayload(
        variant_data=ObjectLabelVariantData(labels=labels),
        source_provenance=metadata.source_provenance,
        parent_image_source_voxel_spacing=metadata.source_voxel_spacing,
        source_spatial_domain=metadata.source_spatial_domain,
    )
    batch = materialize(payload, MaterializationSpec(roi=ROIOptions()))
    path = tmp_path / "engineering.roi.zip"
    batch.roi.write(path, filemanager=filemanager, backend=Backend.DISK.value, backend_kwargs={})
    decoded = ROIArchiveSourceMetadata.decode(load_rois_from_zip(path))
    assert decoded.source_voxel_spacing == expected
    assert decoded.source_voxel_spacing.native_coordinate_unit == "micrometer"
    assert decoded.source_provenance == metadata.source_provenance


def test_absent_ome_calibration_does_not_invent_micrometers(tmp_path, monkeypatch):
    _, dataset, persisted, _ = _prepare(tmp_path, monkeypatch, None)
    assert dataset.pixel_size == persisted["pixel_size"] == 1.0
    assert all(
        not SourceVoxelSpacing.from_source_metadata(candidate.metadata).has_values
        for candidate in dataset.candidates
    )
    assert all(
        SourceVoxelSpacing.from_source_metadata(metadata).native_coordinate_unit == "pixel"
        for metadata in persisted["source_metadata"].values()
    )
