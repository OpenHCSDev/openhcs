"""Acquisition-path ownership through the real read-only inspection consumer."""

from pathlib import Path
import re

import pytest
from polystore.base import ensure_storage_registry, storage_registry
from polystore.filemanager import FileManager

from openhcs.agent.dto.plate import (
    PlateFileQueryRequest,
    PlateInspectionBounds,
    PlatePathInspectionRequest,
)
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.plate_inspection_service import (
    PlateInspectionFilenameParser,
    PlateInspectionService,
)
from openhcs.core.plate_image_inventory import PlateFileInventory
from openhcs.core.dataset_sources.choice import DatasetSourceChoice
from openhcs.microscopes.imagexpress import ImageXpressHandler
from openhcs.core.dataset_sources.source import DatasetSource
from openhcs.core.dataset_sources.interfaces import FilenameParserCapability
from openhcs.core.axes import AxisFamily
from openhcs.domains.microscopy.axes import Microscopy


def write_plate(root: Path) -> Path:
    plate = root / "plate"
    for z in (1, 2):
        folder = plate / "TimePoint_1" / f"ZStep_{z}"
        folder.mkdir(parents=True)
        for channel in (1, 2):
            (folder / f"plate_A01_s1_w{channel}.tif").write_bytes(b"source")
    (plate / "plate.HTD").write_text(
        "\n".join(
            (
                '"XSites", 1',
                '"YSites", 1',
                '"PixelSizeUM", 0.5',
                '"WaveName1", "DAPI"',
                '"WaveName2", "GFP"',
            )
        ),
        encoding="utf-8",
    )
    return plate


def service_for(plate: Path):
    return PlateInspectionService(
        AgentPathPolicy.with_roots(readable_roots=(plate.parent,), writable_roots=())
    )


def inspect_plate(plate: Path, source_format="imagexpress", **bounds):
    return service_for(plate).inspect(
        PlatePathInspectionRequest.from_fields(
            plate_path=str(plate),
            source_format=source_format,
            **bounds,
        )
    )


def inventory_for(plate: Path):
    ensure_storage_registry()
    filemanager = FileManager(dict(storage_registry))
    handler = DatasetSourceChoice.named("imagexpress").open(plate, filemanager=filemanager)
    return (
        handler,
        filemanager,
        PlateFileInventory.from_handler(
            plate_path=plate,
            handler=handler,
            filemanager=filemanager,
            backend=handler.get_primary_backend(plate, filemanager),
        ),
    )


def identity(record):
    return frozenset(
        (c, record.metadata[c.name]) for c in AxisFamily.active().axes
    ), record.source_path


def test_raw_inspection_retains_folder_z_and_never_initializes(tmp_path: Path):
    plate = write_plate(tmp_path)
    before = {
        p.relative_to(plate): p.read_bytes() for p in plate.rglob("*") if p.is_file()
    }
    result = inspect_plate(plate, max_sample_files=4, max_component_values=10)
    assert not result.errors
    assert result.image_files.count == result.parse_summary.parsed_file_count == 4
    assert result.pixel_size == 0.5
    z = next(
        item for item in result.components if item.component == Microscopy.ZIndex.name
    )
    assert z.count == 2
    assert {
        p.relative_to(plate): p.read_bytes() for p in plate.rglob("*") if p.is_file()
    } == before
    assert not (plate / "openhcs_metadata.json").exists()


def test_real_inventory_query_and_initialization_agree_on_physical_identity(tmp_path):
    plate = write_plate(tmp_path)
    handler, filemanager, raw = inventory_for(plate)
    expected = {
        (
            frozenset(
                (
                    (Microscopy.Well, "A01"),
                    (Microscopy.Site, 1),
                    (Microscopy.Channel, channel),
                    (Microscopy.ZIndex, z),
                    (Microscopy.Timepoint, 1),
                )
            ),
            str(plate / "TimePoint_1" / f"ZStep_{z}" / f"plate_A01_s1_w{channel}.tif"),
        )
        for z in (1, 2)
        for channel in (1, 2)
    }
    assert {identity(record) for record in raw.image_records} == expected
    query = service_for(plate).query_files(
        PlateFileQueryRequest.from_fields(
            plate_path=str(plate),
            source_format="imagexpress",
            component_filters={"well": ["A01"]},
            include_previews=False,
            limit=3,
        )
    )
    assert not query.errors
    assert (query.total_count, query.returned_count, query.truncated_count) == (4, 3, 1)
    assert {item.metadata["z_index"] for item in query.records} == {1, 2}
    assert not (plate / "openhcs_metadata.json").exists()
    original = {p: p.read_bytes() for p in plate.rglob("*") if p.is_file()}
    handler.initialize_workspace(plate, filemanager)
    prepared = PlateFileInventory.from_handler(
        plate_path=plate,
        handler=handler,
        filemanager=filemanager,
        backend=handler.get_primary_backend(plate, filemanager),
    )
    assert {identity(record) for record in prepared.image_records} == expected
    assert all(p.read_bytes() == data for p, data in original.items())
    inspection = inspect_plate(plate, max_component_values=10)
    assert not inspection.errors
    assert (
        inspection.image_files.count == inspection.parse_summary.parsed_file_count == 4
    )
    assert (
        next(
            c for c in inspection.components if c.component == Microscopy.ZIndex.name
        ).count
        == 2
    )


@pytest.mark.parametrize(
    "relative_path,z,time",
    [
        ("plate_A01_s1_w2.tif", 1, 1),
        ("TimePoint-3/plate_A01_s1_w2.tif", 1, 3),
        ("zstep2/plate_A01_s1_w2.tif", 2, 1),
        ("TimePoint_3/ZStep-2/plate_A01_s1_w2_z9_t8.tif", 2, 3),
    ],
)
def test_path_owner_preserves_flat_and_folder_precedence(relative_path, z, time):
    ensure_storage_registry()
    handler = ImageXpressHandler(FileManager(dict(storage_registry)))
    parsed = handler.parse_image_path(relative_path)
    assert parsed.value_for(Microscopy.ZIndex) == z
    assert parsed.value_for(Microscopy.Timepoint) == time
    assert parsed.value_for(Microscopy.Channel) == 2


def test_parse_bounds_errors_unparsed_and_absence_keep_original_receipts(tmp_path):
    plate = write_plate(tmp_path)
    inspection = inspect_plate(
        plate, max_files_to_parse=2, max_sample_files=1, max_component_values=1
    )
    assert (
        inspection.parse_summary.attempted_file_count,
        inspection.parse_summary.skipped_file_count,
    ) == (2, 2)
    assert inspection.image_files.truncated_file_count == 3
    channel = next(
        c for c in inspection.components if c.component == Microscopy.Channel.name
    )
    assert channel.count == 2 and len(channel.values) == 1
    handler, _, _ = inventory_for(plate)
    parser = PlateInspectionFilenameParser()
    paths = ("ZStep_1/ZStep_2/A01_w1.tif", "not-an-image", "other", "A01_w1.tif")
    parsed = parser.parse(
        parser=handler,
        image_files=paths,
        bounds=PlateInspectionBounds(
            max_parse_failure_samples=1,
            max_files_to_parse=4,
        ),
    )
    assert (parsed.summary.parsed_file_count, parsed.summary.failed_file_count) == (
        1,
        3,
    )
    assert parsed.summary.truncated_failure_count == 2
    assert parsed.summary.failure_samples[0].filename == paths[0]
    assert "replaced more than once" in parsed.summary.failure_samples[0].reason
    missing = parser.parse(
        parser=None, image_files=paths, bounds=PlateInspectionBounds()
    )
    assert missing.summary.skipped_file_count == 4
    assert (
        missing.summary.attempted_file_count == missing.summary.failed_file_count == 0
    )


@pytest.mark.parametrize("reverse", [False, True])
def test_new_declared_capability_through_unchanged_consumers_in_both_mro_orders(
    tmp_path, reverse
):
    events = []

    class PathTerminus(FilenameParserCapability):
        def image_path_components(self, path):
            events.append(("ancestor", str(path)))
            return super().image_path_components(path)

    class SiteFolders(PathTerminus):
        _site_pattern = re.compile(r"Site_(\d+)")

        def image_path_components(self, path):
            events.append(("site", str(path)))
            return (
                *super().image_path_components(path),
                *self.indexed_folder_components(
                    path,
                    Microscopy.Site,
                    self._site_pattern,
                ),
            )

    # One new subtype declaration: inherited registry, factory and consumers unchanged.
    parents = (
        (ImageXpressHandler, SiteFolders)
        if reverse
        else (SiteFolders, ImageXpressHandler)
    )
    key = f"imagexpress_site_folders_{reverse}"
    subtype = type("SiteAcquisitionHandler", parents, {"source_name": key})
    try:
        plate = write_plate(tmp_path)
        source = plate / "TimePoint_1"
        renamed = plate / "TimePoint_3"
        source.rename(renamed)
        site = renamed / "Site_7"
        site.mkdir()
        for folder in tuple(renamed.glob("ZStep*")):
            folder.rename(site / folder.name)
        result = inspect_plate(plate, source_format=key, max_component_values=10)
        assert not result.errors
        assert result.handler_class == subtype.__name__
        assert result.image_files.count == result.parse_summary.parsed_file_count == 4
        summaries = {item.component: item for item in result.components}
        assert tuple(v.key for v in summaries[Microscopy.Site.name].values) == ("7",)
        assert tuple(v.key for v in summaries[Microscopy.Timepoint.name].values) == ("3",)
        assert summaries[Microscopy.ZIndex.name].count == 2
        query = service_for(plate).query_files(
            PlateFileQueryRequest.from_fields(
                plate_path=str(plate),
                source_format=key,
                include_previews=False,
            )
        )
        assert not query.errors
        assert query.total_count == 4
        assert {item.metadata["site"] for item in query.records} == {7}
        # Inspector parses each path twice (inventory and bounded summary); query once.
        for path in {path for _, path in events}:
            assert events.count(("site", path)) == events.count(("ancestor", path)) == 3
        assert (
            subtype.__mro__.count(PathTerminus)
            == subtype.__mro__.count(FilenameParserCapability)
            == 1
        )
        assert DatasetSource.__registry__[key] is subtype
        assert not (plate / "openhcs_metadata.json").exists()
        filemanager = FileManager(dict(storage_registry))
        handler = DatasetSourceChoice.named(key).open(plate, filemanager=filemanager)
        handler.initialize_workspace(plate, filemanager)
        prepared = PlateFileInventory.from_handler(
            plate_path=plate,
            handler=handler,
            filemanager=filemanager,
            backend=handler.get_primary_backend(plate, filemanager),
        )
        assert len(prepared.image_records) == 4
        assert {record.metadata["site"] for record in prepared.image_records} == {7}
        assert {record.metadata["timepoint"] for record in prepared.image_records} == {
            3
        }
        assert {record.source_path for record in prepared.image_records} == {
            item.metadata["source_path"] for item in query.records
        }
        for path in {path for _, path in events}:
            assert events.count(("site", path)) == events.count(("ancestor", path))
    finally:
        del DatasetSource.__registry__[key]


def test_initializer_rejects_ambiguous_paths_instead_of_overwriting(tmp_path):
    plate = write_plate(tmp_path)
    handler, _, _ = inventory_for(plate)
    with pytest.raises(ValueError, match="collide"):
        handler.acquisition_workspace_mapping(
            ("TimePoint_1/A01_w1.tif", "TimePoint_1/A01_s1_w1.tif"),
            backend="disk",
        )
    assert not (plate / "openhcs_metadata.json").exists()
