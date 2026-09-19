"""Saved-pixel facts and complete, nominal metadata replay."""

import json
from concurrent.futures import ThreadPoolExecutor
from dataclasses import fields

import numpy as np
import pytest
from polystore.virtual_workspace import SourcePixelRef

from openhcs.core.image_file_serialization import (
    ImageFileFormat,
    ImageFileSourceMetadata,
)
from openhcs.core.runtime_image_loading import ImagePayloadSourceMetadataContext
from openhcs.core.runtime_image_values import (
    ImageMetadataPayload,
    ImagePayloadMetadata,
    ImageUnitIntervalIntensityMetadata,
)
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_image_provenance import (
    SourceImageIdentity,
    SourceImageProvenance,
    SourceImageProvenanceContributor,
    SourceImageProvenancePlaneRecord,
    SourceImageProvenancePlanes,
)
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_projection import (
    OpenHCSPlaneAddress,
    SourcePlaneProjection,
    SourceProjectionMetadataSerializer,
)
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.virtual_workspace_metadata import FIELDS, AtomicMetadataWriter
from openhcs.serialization.json import to_jsonable


def metadata_fixture():
    contributors = tuple(
        SourceImageProvenancePlaneRecord(
            path=f"/source/site{site}.tif",
            component_metadata={"site": site},
            identity_kind=SourceImageProvenanceContributor.identity_kind,
            source_image_name="neurite",
        )
        for site in range(1, 10)
    )
    return ImagePayloadMetadata(
        source_provenance=SourceImageProvenance(
            source_path="/produced/mosaic.tif",
            source_component_metadata={"well": "A01", "site": 1, "channel": 1},
            source_image_provenance_planes=SourceImageProvenancePlanes.from_records(
                contributors
            ),
            source_image_names=("neurite", "nucleus"),
        ),
        source_voxel_spacing=SourceVoxelSpacing((0.25, 0.5)),
        source_spatial_domain=SourceSpatialDomain((7, 11), (20, 30), 0, "Crop"),
        source_dtype="float32",
        intensity_scale=1.0,
        unit_interval_intensity=ImageUnitIntervalIntensityMetadata(255),
        physical_border_edges_yx=(True, False, False, True),
        mask_defines_border=True,
    )


def test_complete_metadata_codec_uses_declarations_and_preserves_contributors():
    metadata = metadata_fixture()
    wire = json.loads(json.dumps(to_jsonable(metadata)))
    assert set(wire) == {field.name for field in fields(ImagePayloadMetadata)}
    restored = ImagePayloadMetadata.from_mapping(wire)
    assert restored == metadata
    assert len(restored.source_provenance.represented_source_identities) == 9
    assert restored.plane_axis is None  # Contributors are not a runtime SITE axis.
    assert restored.source_image_names == ("neurite", "nucleus")


@pytest.mark.parametrize("extension", (".tif", ".npy", ".png", ".bmp"))
def test_saved_format_metadata_is_native_and_does_not_reencode(
    tmp_path, monkeypatch, extension
):
    metadata = metadata_fixture()
    payload = ImageMetadataPayload(
        np.linspace(0, 1, 20, dtype=np.float32).reshape(4, 5), metadata
    )
    path = tmp_path / f"mosaic{extension}"
    image_format = ImageFileFormat.require_path(path)
    image_format.write(path, payload)
    monkeypatch.setattr(
        image_format,
        "prepare",
        lambda *_: pytest.fail("metadata copied/encoded pixels"),
    )
    restored = ImagePayloadMetadata.from_mapping(
        to_jsonable(image_format.persisted_metadata(path, payload))
    )
    saved = image_format.read(path)
    assert restored.source_dtype == str(saved.dtype)
    assert restored.source_voxel_spacing == metadata.source_voxel_spacing
    assert restored.source_spatial_domain == metadata.source_spatial_domain
    assert restored.source_provenance == metadata.source_provenance
    assert restored.plane_axis is None
    if extension in (".png", ".bmp"):
        assert restored.unit_interval_intensity.scale is None
        assert restored.physical_border_edges_yx is None
        assert restored.mask_defines_border is None
    else:
        assert restored.intensity_scale == metadata.intensity_scale
        assert restored.unit_interval_intensity == metadata.unit_interval_intensity
        assert restored.physical_border_edges_yx == metadata.physical_border_edges_yx


@pytest.mark.parametrize("extension", (".tif", ".npy"))
def test_saved_two_channel_planes_keep_runtime_axis_not_contributor_axis(
    tmp_path, extension
):
    contributor_records = metadata_fixture().source_image_provenance_planes.records
    metadata = metadata_fixture().replace_fields(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_image_provenance_planes=SourceImageProvenancePlanes.from_records(
            tuple(
                SourceImageProvenancePlaneRecord(
                    path=f"/produced/channel{channel}.tif",
                    component_metadata={"channel": channel},
                    contributors=contributor_records,
                )
                for channel in (1, 2)
            )
        ),
    )
    payload = ImageMetadataPayload(np.zeros((2, 4, 5), dtype=np.float32), metadata)
    path = tmp_path / f"paired{extension}"
    image_format = ImageFileFormat.require_path(path)
    image_format.write(path, payload)
    restored = ImagePayloadMetadata.from_mapping(
        to_jsonable(image_format.persisted_metadata(path, payload))
    )
    assert image_format.read(path).shape == (2, 4, 5)
    assert restored.plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
    assert restored.source_channel_axis is None
    assert restored.source_provenance.source_plane_count == 2
    assert all(
        len(
            restored.for_source_plane(
                index
            ).source_provenance.represented_source_identities
        )
        == 9
        for index in (0, 1)
    )


def test_atomic_perwell_projection_merge_preserves_all_records(tmp_path):
    path = tmp_path / "openhcs_metadata.json"
    writer = AtomicMetadataWriter()
    writer.replace_subdirectory_metadata(path, ".", {"unrelated": 7})

    def merge(well):
        virtual_path = f"{well}.tif"
        projection = SourcePlaneProjection(
            OpenHCSPlaneAddress.from_values(well, 1, 1, 1, 1),
            SourcePixelRef("disk", virtual_path),
            image_metadata=metadata_fixture(),
        )
        writer.merge_source_projection_metadata(
            path,
            ".",
            {
                FIELDS.WORKSPACE_MAPPING: {
                    virtual_path: {"backend": "disk", "backend_address": virtual_path}
                },
                FIELDS.SOURCE_METADATA: {virtual_path: {"well": well}},
                FIELDS.SOURCE_PROJECTION: [
                    SourceProjectionMetadataSerializer(None)._source_projection_payload(
                        projection, virtual_path
                    )
                ],
            },
        )

    with ThreadPoolExecutor(max_workers=4) as pool:
        list(pool.map(merge, ("A01", "A02", "A03", "A04")))
    subdir = json.loads(path.read_text())[FIELDS.SUBDIRECTORIES]["."]
    assert subdir["unrelated"] == 7
    assert len(subdir[FIELDS.SOURCE_PROJECTION]) == 4
    assert len(subdir[FIELDS.WORKSPACE_MAPPING]) == 4
    assert len(subdir[FIELDS.SOURCE_METADATA]) == 4


def test_metadata_codec_rejects_unknown_declarations():
    with pytest.raises(ValueError, match="undeclared"):
        ImagePayloadMetadata.from_mapping({"imagined_tile_axis": 9})
    wire = to_jsonable(metadata_fixture())
    wire["source_provenance"]["invented_contributors"] = []
    with pytest.raises(ValueError, match="Unknown source provenance"):
        ImagePayloadMetadata.from_mapping(wire)


def test_absent_native_scale_retains_only_value_preserved_authored_facts():
    metadata = metadata_fixture().replace_fields(
        source_plane_intensity_scales=(1.0, 0.5)
    )
    header = ImageFileSourceMetadata(np.dtype("float32"))
    unchanged = header.project_image_metadata(metadata, values_preserved=True)
    assert unchanged.intensity_scale == 1.0
    assert unchanged.source_plane_intensity_scales == (1.0, 0.5)
    changed = header.project_image_metadata(metadata, values_preserved=False)
    assert changed.intensity_scale is None
    assert changed.source_plane_intensity_scales == (None, None)
    assert changed.unit_interval_intensity.scale is None


@pytest.mark.parametrize("origin", ((0, 0), (7, 11)))
def test_native_header_reload_preserves_declared_crop_and_alias(tmp_path, origin):
    metadata = metadata_fixture().replace_fields(
        source_spatial_domain=SourceSpatialDomain(origin, (20, 30), 0, "Crop")
    )
    path = tmp_path / "crop.tif"
    image_format = ImageFileFormat.require_path(path)
    payload = ImageMetadataPayload(np.zeros((4, 5), dtype=np.float32), metadata)
    image_format.write(path, payload)
    restored = image_format.persisted_metadata(path, payload)
    reloaded = ImageMetadataPayload(image_format.read(path), restored)
    context = ImagePayloadSourceMetadataContext(SourceImageIdentity(str(path), {}))
    from openhcs.core.runtime_image_values import image_payload_metadata
    from openhcs.core.source_bindings import NamedSourceBinding
    from openhcs.core.source_image_semantics import apply_source_binding_payload

    current = image_payload_metadata(
        apply_source_binding_payload(
            reloaded, NamedSourceBinding(alias="neurite"), context
        )
    )
    assert current.source_dtype == "float32"
    assert current.source_spatial_domain == metadata.source_spatial_domain
    assert current.source_image_names == ("neurite",)
    assert all(
        record.source_image_name == "neurite"
        for record in current.source_image_provenance_planes.records
    )
    assert len(current.source_provenance.represented_source_identities) == 9


def test_native_mosaic_replaces_incompatible_old_tile_domain_without_losing_source_facts(
    tmp_path,
):
    from openhcs.core.runtime_image_values import image_payload_metadata
    from openhcs.core.source_bindings import NamedSourceBinding
    from openhcs.core.source_image_semantics import apply_source_binding_payload

    metadata = metadata_fixture().replace_fields(
        source_spatial_domain=SourceSpatialDomain((0, 0), (4, 6))
    )
    path = tmp_path / "mosaic.tif"
    image_format = ImageFileFormat.require_path(path)
    payload = ImageMetadataPayload(np.zeros((10, 16), dtype=np.float32), metadata)
    image_format.write(path, payload)
    reloaded = ImageMetadataPayload(
        image_format.read(path), image_format.persisted_metadata(path, payload)
    )
    current = image_payload_metadata(
        apply_source_binding_payload(
            reloaded,
            NamedSourceBinding(alias="neurite"),
            ImagePayloadSourceMetadataContext(SourceImageIdentity(str(path), {})),
        )
    )
    assert current.source_spatial_domain.origin_yx == (0, 0)
    assert current.source_spatial_domain.source_shape_yx == (10, 16)
    assert current.source_image_names == ("neurite",)
    assert current.source_voxel_spacing == metadata.source_voxel_spacing
    assert len(current.source_provenance.represented_source_identities) == 9


@pytest.mark.parametrize(
    "authored_domain, expected_domain",
    (
        (
            SourceSpatialDomain((1, 2), (10, 12), 3, "authored crop"),
            SourceSpatialDomain((1, 2), (10, 12), 3, "authored crop"),
        ),
        (
            SourceSpatialDomain((1, 2), None, 3, "partial crop"),
            SourceSpatialDomain((1, 2), (10, 12), 3, "partial crop"),
        ),
        (
            SourceSpatialDomain((9, 11), (10, 12), 3, "conflicting crop"),
            SourceSpatialDomain((1, 2), (10, 12), 0, "native context"),
        ),
    ),
)
def test_persisted_projection_validates_loaded_window_not_full_source_extent(
    authored_domain, expected_domain
):
    from openhcs.core.runtime_image_values import image_payload_metadata
    from openhcs.core.source_workspace_projection import (
        VirtualWorkspaceSourceProjection,
    )

    current = metadata_fixture().replace_fields(
        source_spatial_domain=SourceSpatialDomain((1, 2), (10, 12), 0, "native context")
    )
    persisted = metadata_fixture().replace_fields(source_spatial_domain=authored_domain)
    payload = ImageMetadataPayload(np.zeros((2, 3), dtype=np.float32), current)
    restored = VirtualWorkspaceSourceProjection._project_payload_source_metadata(
        payload,
        source_metadata=None,
        source_alias="neurite",
        persisted_metadata=persisted,
    )
    metadata = image_payload_metadata(restored)
    assert metadata.source_spatial_domain == expected_domain
    assert metadata.source_image_names == ("neurite",)
    assert metadata.source_voxel_spacing == persisted.source_voxel_spacing
    assert len(metadata.source_provenance.represented_source_identities) == 9


def test_zarr_batch_header_uses_native_mapping_without_pixels(tmp_path, monkeypatch):
    import zarr
    from polystore.filemanager import FileManager
    from polystore.zarr import ZarrStorageBackend
    from polystore.zarr_batch import ZarrBatchAxis, ZarrBatchAxisRole, ZarrBatchLayout

    backend = ZarrStorageBackend()
    store = tmp_path / "images"
    paths = [store / f"A01_s001_w{channel}_z001_t001.tif" for channel in (1, 2)]
    pixels = [
        np.arange(20, dtype=np.uint16).reshape(4, 5) + channel for channel in (1, 2)
    ]
    layout = ZarrBatchLayout(
        axes=(ZarrBatchAxis("c", "channel", ("1", "2"), ZarrBatchAxisRole.ARRAY),),
        item_coordinates=((0,), (1,)),
    )
    backend.save_batch(
        pixels, paths, chunk_name="A01", batch_layout=layout, row="A", col="01"
    )
    loaded = backend.load_batch(paths)
    for actual, expected in zip(loaded, pixels, strict=True):
        np.testing.assert_array_equal(actual, expected)
    monkeypatch.setattr(
        zarr.Array, "__getitem__", lambda *_: pytest.fail("header loaded pixels")
    )
    manager = FileManager({"zarr": backend})
    for path in paths:
        relative = path.relative_to(tmp_path)
        assert (
            manager.physical_source_path(relative, "zarr", base_path=tmp_path) is None
        )
        assert manager.source_image_dtype(
            relative, "zarr", base_path=tmp_path
        ) == np.dtype("uint16")


@pytest.mark.parametrize("storage", ("npy", "zarr"))
def test_native_headerless_hwc_replay_retains_declared_channel_semantics(
    tmp_path, storage
):
    from polystore.filemanager import FileManager
    from polystore.zarr import ZarrStorageBackend

    from openhcs.core.runtime_image_values import image_payload_metadata
    from openhcs.core.source_bindings import NamedSourceBinding
    from openhcs.core.source_image_semantics import apply_source_binding_payload

    pixels = np.arange(60, dtype=np.uint8).reshape(4, 5, 3)
    metadata = metadata_fixture().replace_fields(
        source_dtype="uint8",
        source_channel_axis=-1,
        source_spatial_domain=SourceSpatialDomain((1, 2), (10, 12)),
    )
    payload = ImageMetadataPayload(pixels, metadata)
    if storage == "npy":
        path = tmp_path / "color.npy"
        image_format = ImageFileFormat.require_path(path)
        image_format.write(path, payload)
        restored = image_format.persisted_metadata(path, payload)
        loaded = image_format.read(path)
        context = ImagePayloadSourceMetadataContext(SourceImageIdentity(str(path)))
    else:
        path = tmp_path / "images" / "color.tif"
        backend = ZarrStorageBackend()
        backend.save(pixels, path)
        manager = FileManager({"zarr": backend})
        native_dtype = manager.source_image_dtype(path, "zarr", base_path=tmp_path)
        restored = ImageFileSourceMetadata(native_dtype, 255).project_image_metadata(
            metadata,
            values_preserved=manager.image_serialization_preserves_values(
                "zarr", pixels.dtype, native_dtype
            ),
        )
        loaded = backend.load(path)
        context = ImagePayloadSourceMetadataContext(
            SourceImageIdentity(str(path)), read_backend="zarr", filemanager=manager
        )
    restored = ImagePayloadMetadata.from_mapping(
        json.loads(json.dumps(to_jsonable(restored)))
    )
    assert restored.source_channel_axis == -1
    bound = apply_source_binding_payload(
        ImageMetadataPayload(loaded, restored),
        NamedSourceBinding(alias="neurite"),
        context,
    )
    current = image_payload_metadata(bound)
    assert current.source_channel_axis == -1
    assert current.spatial_shape_yx(loaded) == (4, 5)
    assert current.source_spatial_domain == metadata.source_spatial_domain
    assert current.source_voxel_spacing == metadata.source_voxel_spacing
    assert len(current.source_provenance.represented_source_identities) == 9
    np.testing.assert_array_equal(loaded, pixels)


def test_lossy_jpeg_clears_exact_value_proofs_even_for_uint8(tmp_path):
    pixels = ((np.indices((32, 32)).sum(axis=0) % 2) * 255).astype(np.uint8)
    metadata = metadata_fixture().replace_fields(source_dtype="uint8")
    payload = ImageMetadataPayload(pixels, metadata)
    path = tmp_path / "lossy.jpg"
    image_format = ImageFileFormat.require_path(path)
    image_format.write(path, payload)
    assert np.any(image_format.read(path) != pixels)
    restored = image_format.persisted_metadata(path, payload)
    assert restored.unit_interval_intensity.scale is None
    assert restored.physical_border_edges_yx is None
    assert restored.mask_defines_border is None
    assert restored.source_provenance == metadata.source_provenance


def test_mixed_zarr_batch_preserves_lineage_but_not_quantized_value_proofs(tmp_path):
    from polystore.filemanager import FileManager
    from polystore.zarr import ZarrStorageBackend
    from polystore.zarr_batch import ZarrBatchAxis, ZarrBatchLayout

    backend = ZarrStorageBackend()
    store = tmp_path / "images"
    paths = [store / f"A01_s001_w{channel}_z001_t001.tif" for channel in (1, 2)]
    pixels = [np.ones((4, 5), dtype=np.uint8), np.full((4, 5), 0.5, dtype=np.float32)]
    backend.save_batch(
        pixels,
        paths,
        chunk_name="A01",
        row="A",
        col="01",
        batch_layout=ZarrBatchLayout(
            axes=(ZarrBatchAxis("c", "channel", ("1", "2")),),
            item_coordinates=((0,), (1,)),
        ),
    )
    manager = FileManager({"zarr": backend})
    stored_dtype = manager.source_image_dtype(paths[1], "zarr", base_path=tmp_path)
    assert stored_dtype == np.dtype("uint8")
    saved = backend.load_batch(paths)[1]
    assert np.all(saved == 0)
    assert manager.image_serialization_preserves_values(
        "zarr", pixels[0].dtype, stored_dtype
    )
    assert not manager.image_serialization_preserves_values(
        "zarr", pixels[1].dtype, stored_dtype
    )
    metadata = metadata_fixture()
    restored = ImageFileSourceMetadata(stored_dtype, 255.0).project_image_metadata(
        metadata,
        values_preserved=manager.image_serialization_preserves_values(
            "zarr", pixels[1].dtype, stored_dtype
        ),
    )
    assert restored.source_dtype == "uint8"
    assert restored.unit_interval_intensity.scale is None
    assert restored.physical_border_edges_yx is None
    assert restored.mask_defines_border is None
    assert restored.source_provenance == metadata.source_provenance
    assert restored.source_spatial_domain == metadata.source_spatial_domain
    assert restored.source_voxel_spacing == metadata.source_voxel_spacing
