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
from openhcs.core.virtual_workspace_metadata import (
    FIELDS,
    AtomicMetadataWriter,
    MetadataWriteError,
    VirtualWorkspaceSourceProjectionEntries,
)
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser
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
        assert restored.unit_interval_intensity is None
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
            VirtualWorkspaceSourceProjectionEntries.from_projection_paths(
                ((projection, virtual_path),)
            ),
        )

    with ThreadPoolExecutor(max_workers=4) as pool:
        list(pool.map(merge, ("A01", "A02", "A03", "A04")))
    subdir = json.loads(path.read_text())[FIELDS.SUBDIRECTORIES]["."]
    assert subdir["unrelated"] == 7
    assert len(subdir[FIELDS.SOURCE_PROJECTION]) == 4
    assert len(subdir[FIELDS.WORKSPACE_MAPPING]) == 4
    assert len(subdir[FIELDS.SOURCE_METADATA]) == 4


def calibrated_projection(well, path, pixel_size):
    spacing = SourceVoxelSpacing((pixel_size, pixel_size))
    source_metadata = {}
    spacing.merge_into(source_metadata, path=path)
    return SourcePlaneProjection(
        OpenHCSPlaneAddress.from_values(well, 1, 1, 1, 1),
        SourcePixelRef("disk", path),
        source_metadata=source_metadata,
        image_metadata=metadata_fixture().replace_fields(source_voxel_spacing=spacing),
    )


def publish_projection_inventory(writer, path, projection_metadata, saved_paths):
    writer.publish_source_projection_metadata(
        path,
        "images",
        projection_metadata,
        serializer=SourceProjectionMetadataSerializer(SourceSchemaFilenameParser()),
        saved_image_paths=saved_paths,
        microscope_handler_name="VirtualWorkspaceMicroscopeHandler",
        source_filename_parser_name="SourceSchemaFilenameParser",
        component_labels={},
        backend="disk",
        is_main=True,
        results_dir=None,
    )


@pytest.mark.parametrize(
    "merge_method", ("merge_subdirectory_metadata", "merge_source_projection_metadata")
)
def test_atomic_projection_merge_refreshes_geometry_from_current_document(
    tmp_path, merge_method
):
    path = tmp_path / "openhcs_metadata.json"
    writer = AtomicMetadataWriter()
    serializer = SourceProjectionMetadataSerializer(SourceSchemaFilenameParser())
    first = calibrated_projection("A01", "images/first.tif", 0.5)
    second = calibrated_projection("A02", "images/second.tif", 2.0)
    first_fields = serializer.projection_fields(((first, "images/first.tif"),))
    writer.replace_subdirectory_metadata(path, "images", first_fields)
    second_fields = serializer.projection_fields(((second, "images/second.tif"),))
    if merge_method == "merge_subdirectory_metadata":
        # This API replaces the projection field with the authoritative new list.
        writer.merge_subdirectory_metadata(path, {"images": second_fields})
        expected_pixel_size = 2.0
    else:
        writer.merge_source_projection_metadata(
            path, "images",
            VirtualWorkspaceSourceProjectionEntries.from_projection_paths(
                ((second, "images/second.tif"),)
            ),
        )
        expected_pixel_size = 1.0  # Conflicting calibration has no physical scalar.
    subdir = json.loads(path.read_text())[FIELDS.SUBDIRECTORIES]["images"]
    assert subdir[FIELDS.PIXEL_SIZE] == expected_pixel_size


def test_final_publication_prunes_geometry_and_preserves_other_directories(tmp_path):
    path = tmp_path / "openhcs_metadata.json"
    writer = AtomicMetadataWriter()
    serializer = SourceProjectionMetadataSerializer(SourceSchemaFilenameParser())
    retained = calibrated_projection("A01", "images/retained.tif", 0.5)
    deleted = calibrated_projection("A02", "images/deleted.tif", 2.0)
    elsewhere = calibrated_projection("A03", "other/retained.tif", 0.5)
    projection_paths = (
        (retained, "images/retained.tif"),
        (deleted, "images/deleted.tif"),
        (elsewhere, "other/retained.tif"),
    )
    writer.merge_source_projection_metadata(
        path, "images",
        VirtualWorkspaceSourceProjectionEntries.from_projection_paths(projection_paths)
    )
    before = json.loads(path.read_text())[FIELDS.SUBDIRECTORIES]["images"]
    assert before[FIELDS.PIXEL_SIZE] == 1.0
    publish_projection_inventory(writer, path, None, ("images/retained.tif",))
    subdir = json.loads(path.read_text())[FIELDS.SUBDIRECTORIES]["images"]
    assert subdir[FIELDS.PIXEL_SIZE] == 0.5
    assert subdir[FIELDS.IMAGE_FILES] == ["images/retained.tif"]
    entries = VirtualWorkspaceSourceProjectionEntries.from_subdirectory(subdir).entries
    assert set(entries) == {"images/retained.tif", "other/retained.tif"}
    assert entries["images/retained.tif"].image_metadata == retained.image_metadata
    assert entries["other/retained.tif"].image_metadata == elsewhere.image_metadata
    # A failed final inventory cannot publish fields or prune existing records.
    before_bytes = path.read_bytes()
    with pytest.raises(MetadataWriteError, match="lack typed produced addresses"):
        publish_projection_inventory(writer, path, None, ("images/unowned.tif",))
    assert path.read_bytes() == before_bytes


def test_concurrent_step_publication_retains_records_outside_partial_inventory(
    tmp_path,
):
    path = tmp_path / "openhcs_metadata.json"
    writer = AtomicMetadataWriter()
    serializer = SourceProjectionMetadataSerializer(SourceSchemaFilenameParser())
    paths = tuple(f"images/{well}.tif" for well in ("A01", "A02", "A03", "A04"))

    def publish(item):
        index, image_path = item
        projection = calibrated_projection(f"A0{index + 1}", image_path, 0.5)
        publish_projection_inventory(
            writer,
            path,
            VirtualWorkspaceSourceProjectionEntries.from_projection_paths(
                ((projection, image_path),)
            ),
            (image_path,),
        )

    with ThreadPoolExecutor(max_workers=4) as pool:
        list(pool.map(publish, enumerate(paths)))
    subdir = json.loads(path.read_text())[FIELDS.SUBDIRECTORIES]["images"]
    assert set(subdir[FIELDS.WORKSPACE_MAPPING]) == set(paths)
    assert len(subdir[FIELDS.IMAGE_FILES]) == 1  # Most recent partial step inventory.
    assert subdir[FIELDS.PIXEL_SIZE] == 0.5
    publish_projection_inventory(writer, path, None, paths)
    subdir = json.loads(path.read_text())[FIELDS.SUBDIRECTORIES]["images"]
    assert subdir[FIELDS.IMAGE_FILES] == list(paths)
    assert len(subdir[FIELDS.SOURCE_PROJECTION]) == len(paths)
    assert subdir["wells"] == {f"A0{index + 1}": None for index in range(4)}


@pytest.mark.parametrize("publish", (False, True))
def test_typed_projection_update_admits_only_retained_wire_records(
    tmp_path, monkeypatch, publish
):
    path = tmp_path / "openhcs_metadata.json"
    writer = AtomicMetadataWriter()
    retained = calibrated_projection("A01", "images/retained.tif", 0.5)
    replacement = calibrated_projection("A02", "images/replaced.tif", 0.5)
    serializer = SourceProjectionMetadataSerializer(SourceSchemaFilenameParser())
    fields = serializer.projection_fields(((retained, "images/retained.tif"),))
    fields[FIELDS.SOURCE_PROJECTION].append(
        {"virtual_path": "images/replaced.tif", "projection_role": "broken"}
    )
    writer.replace_subdirectory_metadata(path, "images", fields)
    updates = VirtualWorkspaceSourceProjectionEntries.from_projection_paths(
        ((replacement, "images/replaced.tif"),)
    )
    admitted_paths = []
    serialized_paths = []
    decode = VirtualWorkspaceSourceProjectionEntries._projection_record
    encode = SourceProjectionMetadataSerializer._source_projection_payload

    def record(cls, wire):
        admitted_paths.append(wire["virtual_path"])
        return decode(wire)

    def payload(cls, projection, virtual_path):
        serialized_paths.append(virtual_path)
        return encode(projection, virtual_path)

    monkeypatch.setattr(
        VirtualWorkspaceSourceProjectionEntries,
        "_projection_record",
        classmethod(record),
    )
    monkeypatch.setattr(
        SourceProjectionMetadataSerializer,
        "_source_projection_payload",
        classmethod(payload),
    )
    merged = updates.merged_with_subdirectory(fields)
    assert merged.entries["images/replaced.tif"] is replacement
    assert tuple(merged.entries) == ("images/retained.tif", "images/replaced.tif")
    admitted_paths.clear()
    if publish:
        publish_projection_inventory(
            writer, path, updates, ("images/retained.tif", "images/replaced.tif")
        )
    else:
        writer.merge_source_projection_metadata(path, "images", updates)
    assert admitted_paths == ["images/retained.tif"]
    assert serialized_paths == ["images/replaced.tif"]
    subdir = json.loads(path.read_text())[FIELDS.SUBDIRECTORIES]["images"]
    restored = VirtualWorkspaceSourceProjectionEntries.from_subdirectory(subdir)
    assert (
        restored.entries["images/replaced.tif"].image_metadata
        == replacement.image_metadata
    )


@pytest.mark.parametrize("publish", (False, True))
def test_invalid_unreplaced_projection_aborts_typed_transaction(tmp_path, publish):
    path = tmp_path / "openhcs_metadata.json"
    writer = AtomicMetadataWriter()
    writer.replace_subdirectory_metadata(
        path, "images",
        {FIELDS.SOURCE_PROJECTION: [{"virtual_path": "images/broken.tif"}]},
    )
    replacement = calibrated_projection("A02", "images/new.tif", 0.5)
    updates = VirtualWorkspaceSourceProjectionEntries.from_projection_paths(
        ((replacement, "images/new.tif"),)
    )
    before = path.read_bytes()
    with pytest.raises(MetadataWriteError, match="projection_role"):
        if publish:
            publish_projection_inventory(writer, path, updates, ("images/new.tif",))
        else:
            writer.merge_source_projection_metadata(path, "images", updates)
    assert path.read_bytes() == before


@pytest.mark.parametrize("publish", (False, True))
def test_typed_transaction_retains_wire_fields_and_derives_workspace_views(
    tmp_path, publish
):
    path = tmp_path / "openhcs_metadata.json"
    writer = AtomicMetadataWriter()
    original = calibrated_projection("A01", "images/original.tif", 0.5)
    fields = SourceProjectionMetadataSerializer.projection_fields(
        ((original, "images/original.tif"),)
    )
    fields[FIELDS.SOURCE_PROJECTION][0]["external_annotation"] = {"version": 7}
    fields[FIELDS.SOURCE_METADATA]["images/original.tif"] = {
        "manual_override": "obsolete"
    }
    fields[FIELDS.WORKSPACE_MAPPING]["legacy.tif"] = {"opaque": "mapping"}
    fields[FIELDS.SOURCE_METADATA]["legacy.tif"] = {"opaque": "metadata"}
    writer.replace_subdirectory_metadata(path, "images", fields)
    new = calibrated_projection("A02", "images/new.tif", 0.5)
    updates = VirtualWorkspaceSourceProjectionEntries.from_projection_paths(
        ((new, "images/new.tif"),)
    )
    if publish:
        publish_projection_inventory(
            writer, path, updates, ("images/original.tif", "images/new.tif")
        )
    else:
        writer.merge_source_projection_metadata(path, "images", updates)
    subdir = json.loads(path.read_text())[FIELDS.SUBDIRECTORIES]["images"]
    assert subdir[FIELDS.SOURCE_PROJECTION][0]["external_annotation"] == {"version": 7}
    if publish:
        assert "legacy.tif" not in subdir[FIELDS.WORKSPACE_MAPPING]
        assert "legacy.tif" not in subdir[FIELDS.SOURCE_METADATA]
        assert subdir[FIELDS.SOURCE_METADATA]["images/original.tif"]["well"] == "A01"
        assert "manual_override" not in subdir[FIELDS.SOURCE_METADATA][
            "images/original.tif"
        ]
        assert "well" not in subdir[FIELDS.SOURCE_PROJECTION][0]["source_metadata"]
        publish_projection_inventory(
            writer, path, None, ("images/original.tif", "images/new.tif")
        )
        reconciled = json.loads(path.read_text())[FIELDS.SUBDIRECTORIES]["images"]
        assert reconciled[FIELDS.SOURCE_PROJECTION][0]["external_annotation"] == {
            "version": 7
        }
    else:
        assert subdir[FIELDS.WORKSPACE_MAPPING]["legacy.tif"] == {"opaque": "mapping"}
        assert subdir[FIELDS.SOURCE_METADATA]["legacy.tif"] == {"opaque": "metadata"}
        assert subdir[FIELDS.SOURCE_METADATA]["images/original.tif"] == {
            "manual_override": "obsolete"
        }


def test_typed_transaction_normalizes_legacy_paths_and_rejects_collisions():
    original = calibrated_projection("A01", "7", 0.5)
    fields = SourceProjectionMetadataSerializer.projection_fields(((original, "7"),))
    fields[FIELDS.SOURCE_PROJECTION][0]["virtual_path"] = 7
    updates = VirtualWorkspaceSourceProjectionEntries.from_projection_paths(
        ((calibrated_projection("A02", "new.tif", 0.5), "new.tif"),)
    )
    assert tuple(updates.merged_with_subdirectory(fields).entries) == ("7", "new.tif")
    colliding = VirtualWorkspaceSourceProjectionEntries.from_projection_paths(
        ((calibrated_projection("A02", "7", 0.5), "7"),)
    )
    with pytest.raises(RuntimeError, match="duplicate path '7'"):
        colliding.merged_with_subdirectory(fields)


@pytest.mark.parametrize("field", (FIELDS.WORKSPACE_MAPPING, FIELDS.SOURCE_METADATA))
def test_typed_transaction_preserves_durable_mapping_validation(field):
    projection = calibrated_projection("A01", "images/current.tif", 0.5)
    updates = VirtualWorkspaceSourceProjectionEntries.from_projection_paths(
        ((projection, "images/current.tif"),)
    )
    with pytest.raises(TypeError, match="must be a mapping"):
        updates.merged_with_subdirectory({field: None})


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
    assert changed.unit_interval_intensity is None


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

    current = image_payload_metadata(
        NamedSourceBinding(alias="neurite").apply_loaded_payload(
            reloaded,
            context,
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
        NamedSourceBinding(alias="neurite").apply_loaded_payload(
            reloaded,
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
        VirtualWorkspaceImagePayloadProjection,
    )

    current = metadata_fixture().replace_fields(
        source_spatial_domain=SourceSpatialDomain((1, 2), (10, 12), 0, "native context")
    )
    persisted = metadata_fixture().replace_fields(source_spatial_domain=authored_domain)
    payload = ImageMetadataPayload(np.zeros((2, 3), dtype=np.float32), current)
    restored = VirtualWorkspaceImagePayloadProjection(
        source_metadata=None,
        source_alias="neurite",
        persisted_metadata=persisted,
    ).apply(payload)
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
    bound = NamedSourceBinding(alias="neurite").apply_loaded_payload(
        ImageMetadataPayload(loaded, restored),
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
    assert restored.unit_interval_intensity is None
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
    assert restored.unit_interval_intensity is None
    assert restored.physical_border_edges_yx is None
    assert restored.mask_defines_border is None
    assert restored.source_provenance == metadata.source_provenance
    assert restored.source_spatial_domain == metadata.source_spatial_domain
    assert restored.source_voxel_spacing == metadata.source_voxel_spacing
