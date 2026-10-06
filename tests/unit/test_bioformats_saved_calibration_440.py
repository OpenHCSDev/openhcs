"""Header-only BioFormats preparation through the original durable source owners."""

import json
from pathlib import Path

import numpy as np
import pytest
from polystore.bioformats_java import BioFormatsJavaContext
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
from polystore.roi import load_rois_from_zip

from openhcs.constants.constants import Backend
from openhcs.core.roi_source_metadata import ROIArchiveSourceMetadata
from openhcs.core.runtime_image_loading import ImagePayloadSourceMetadataContext
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_object_labels import (
    ObjectLabelPayload,
    ObjectLabelVariantData,
)
from openhcs.core.source_bindings import (
    MetadataSelector,
    NamedSourceBinding,
    SourceBindingsConfig,
    SourceSelector,
)
from openhcs.core.source_image_provenance import SourceImageIdentity
from openhcs.core.source_metadata import SourceVoxelSpacing, SourceVoxelSpacingUnit
from openhcs.core.viewer_streaming_service import ViewerStreamingSource
from openhcs.microscopes.bioformats import BioFormatsMetadataHandler
from types import SimpleNamespace
from openhcs.microscopes.bioformats import BioFormatsHandler
from openhcs.microscopes.bioformats_adapter import BioFormatsAdapterUnavailableError
from openhcs.microscopes.openhcs import OpenHCSMetadataHandler
from openhcs.processing.materialization import (
    MaterializationSpec,
    ROIOptions,
    materialize,
)
from tests.unit.test_bioformats_java_adapter import (
    FakeBioFormatsContext,
    FakeBioFormatsMetadata,
    PhysicalSize,
)
from tests.unit.bioformats_fixture import write_bioformats_manifest_fixture


class _Header(FakeBioFormatsMetadata):
    """New non-plate metadata declaration, with no image decoding capability."""

    def getPlateCount(self):
        return 0


class _NanometerHeader(_Header):
    def getPixelsPhysicalSizeX(self, image):
        return PhysicalSize(self.pixel_size * 1000, to_micrometers=0.001)


class _VolumeHeader(_Header):
    def getPixelsPhysicalSizeZ(self, image):
        return PhysicalSize(2.5)


class _AnisotropicHeader(_Header):
    def getPixelsPhysicalSizeY(self, image):
        return PhysicalSize(self.pixel_size * 2)


class _IncompleteHeader(_Header):
    def getPixelsPhysicalSizeY(self, image):
        return None


def _prepare(tmp_path, monkeypatch, pixel_size, header_type=_Header):
    source = tmp_path / "engineering.czi"
    source.touch()
    context = FakeBioFormatsContext(
        {source.name: header_type(pixel_size=pixel_size)}, declared_suffixes=(".czi",)
    )
    # The only external provider is the existing controlled OME header fixture.
    monkeypatch.setattr(
        BioFormatsJavaContext, "instance", classmethod(lambda cls: context)
    )
    filemanager = FileManager({Backend.DISK.value: DiskStorageBackend()})
    bindings = SourceBindingsConfig(
        bindings=(
            NamedSourceBinding(
                alias="engineering",
                selector=SourceSelector(metadata=(MetadataSelector("channel", "2"),)),
            ),
        )
    )
    handler = BioFormatsHandler(filemanager, source_bindings_config=bindings)
    dataset = handler.source_metadata_handler.source_dataset(tmp_path)
    handler.initialize_workspace(tmp_path, filemanager)
    document = json.loads((tmp_path / "openhcs_metadata.json").read_text())
    return source, dataset, document["subdirectories"]["."], filemanager


@pytest.mark.parametrize(
    "header_type,pixel_size,spacing",
    (
        (_Header, 0.65, (0.65, 0.65)),
        (_Header, 0.217, (0.217, 0.217)),
        (_NanometerHeader, 0.65, (0.65, 0.65)),
        (_VolumeHeader, 0.65, (2.5, 0.65, 0.65)),
    ),
)
def test_nonplate_calibration_survives_preparation_and_native_roi_roundtrip(
    tmp_path, monkeypatch, header_type, pixel_size, spacing
):
    source, dataset, persisted, filemanager = _prepare(
        tmp_path, monkeypatch, pixel_size, header_type
    )
    expected = SourceVoxelSpacing(spacing)
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
    metadata = ImagePayloadSourceMetadataContext(
        SourceImageIdentity(
            path=str(source),
            component_metadata=source_metadata,
        )
    ).metadata(np.zeros((8, 8), dtype=np.uint8))
    assert metadata.source_voxel_spacing == expected
    labels = np.zeros((8, 8), dtype=np.int32)
    labels[2:6, 3:7] = 12
    payload = ObjectLabelPayload(
        variant_data=ObjectLabelVariantData(labels=labels),
        source_provenance=metadata.source_provenance,
        parent_image_source_voxel_spacing=metadata.source_voxel_spacing,
        source_spatial_domain=metadata.source_spatial_domain,
    )
    path = tmp_path / "engineering.roi.zip"
    path = materialize(
        MaterializationSpec(ROIOptions(min_area=0)),
        data=payload,
        path=str(path),
        filemanager=filemanager,
        backends=[Backend.DISK.value],
        backend_kwargs={},
    )
    decoded = ROIArchiveSourceMetadata.decode(load_rois_from_zip(Path(path)))
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
        SourceVoxelSpacing.from_source_metadata(metadata).native_coordinate_unit
        == "pixel"
        for metadata in persisted["source_metadata"].values()
    )
    metadata_handler = OpenHCSMetadataHandler(FileManager({Backend.DISK.value: DiskStorageBackend()}))
    assert metadata_handler.get_metadata_pixel_size(tmp_path) == 1.0
    assert metadata_handler.source_voxel_spacing(tmp_path) == SourceVoxelSpacing()
    with pytest.raises(ValueError, match="micrometer calibration"):
        metadata_handler.get_pixel_size(tmp_path)
    source = ViewerStreamingSource(
        filemanager=metadata_handler.filemanager,
        microscope_handler=SimpleNamespace(metadata_handler=metadata_handler),
        plate_path=tmp_path,
    )
    reopened = source.calibrated_metadata(ImagePayloadMetadata())
    assert reopened.source_voxel_spacing == SourceVoxelSpacing()
    assert reopened.source_voxel_spacing.layer_coordinate_kwargs(("y", "x")) == {
        "scale": (1.0, 1.0), "units": ("pixel", "pixel"),
    }


@pytest.mark.parametrize("spacings,expected", (
    ((SourceVoxelSpacing(),), SourceVoxelSpacing()),
    ((SourceVoxelSpacing((0.65, 0.65)),), SourceVoxelSpacing((0.65, 0.65))),
    ((SourceVoxelSpacing((2.0, 0.65, 0.65)),), SourceVoxelSpacing((2.0, 0.65, 0.65))),
    ((SourceVoxelSpacing((1.0, 2.0), unit=SourceVoxelSpacingUnit.RELATIVE),),
     SourceVoxelSpacing((1.0, 2.0), unit=SourceVoxelSpacingUnit.RELATIVE)),
    ((SourceVoxelSpacing(), SourceVoxelSpacing((0.65, 0.65))), SourceVoxelSpacing()),
    ((SourceVoxelSpacing((0.65, 0.65)), SourceVoxelSpacing((0.5, 0.5))), SourceVoxelSpacing()),
))
def test_store_spacing_preserves_declared_units_not_numeric_defaults(monkeypatch, spacings, expected):
    handler = BioFormatsMetadataHandler()
    dataset = SimpleNamespace(
        pixel_size=1.0,
        candidates=tuple(SimpleNamespace(metadata={}) for _ in spacings),
    )
    candidates = []
    for spacing in spacings:
        metadata = {}
        spacing.merge_into(metadata, path="original")
        candidates.append(SimpleNamespace(metadata=metadata))
    dataset.candidates = tuple(candidates)
    monkeypatch.setattr(handler, "source_dataset", lambda _: dataset)
    assert handler.source_voxel_spacing(Path("original")) == expected
    assert handler.get_metadata_pixel_size(Path("original")) == 1.0
    if SourceVoxelSpacing.common_physical_pixel_size(spacings) is None:
        with pytest.raises(ValueError, match="micrometer calibration"):
            handler.get_pixel_size(Path("original"))
    else:
        assert handler.get_pixel_size(Path("original")) == 0.65


def test_anisotropic_coordinates_are_preserved_without_a_false_scalar(
    tmp_path, monkeypatch
):
    _, _, persisted, filemanager = _prepare(
        tmp_path, monkeypatch, 0.65, _AnisotropicHeader
    )
    (virtual_path,) = persisted["image_files"]
    assert SourceVoxelSpacing.from_source_metadata(
        persisted["source_metadata"][virtual_path]
    ) == (SourceVoxelSpacing((1.3, 0.65)))
    assert persisted["pixel_size"] == 1.0  # Numeric view does not certify calibration.
    with pytest.raises(ValueError, match="isotropic"):
        OpenHCSMetadataHandler(filemanager).get_pixel_size(tmp_path)


@pytest.mark.parametrize("pixel_size", (0.0, -0.65, float("nan"), float("inf")))
def test_invalid_ome_calibration_is_rejected_at_the_original_decoder(
    tmp_path, monkeypatch, pixel_size
):
    with pytest.raises(BioFormatsAdapterUnavailableError, match="finite and positive"):
        _prepare(tmp_path, monkeypatch, pixel_size)


def test_partial_ome_calibration_is_not_inferred(tmp_path, monkeypatch):
    with pytest.raises(
        BioFormatsAdapterUnavailableError, match="both PhysicalSizeX and PhysicalSizeY"
    ):
        _prepare(tmp_path, monkeypatch, 0.65, _IncompleteHeader)


def test_existing_manifest_decoder_uses_the_same_typed_spacing_owner(tmp_path):
    write_bioformats_manifest_fixture(tmp_path)
    filemanager = FileManager({Backend.DISK.value: DiskStorageBackend()})
    BioFormatsHandler(filemanager).initialize_workspace(tmp_path, filemanager)
    reopened = OpenHCSMetadataHandler(filemanager)
    assert reopened.get_pixel_size(tmp_path) == 0.5
    document = json.loads((tmp_path / "openhcs_metadata.json").read_text())
    persisted = document["subdirectories"]["."]
    assert persisted["pixel_size"] == 0.5
    assert len(persisted["source_metadata"]) == 2
    assert all(
        SourceVoxelSpacing.from_source_metadata(metadata) == SourceVoxelSpacing((0.5, 0.5))
        for metadata in persisted["source_metadata"].values()
    )
