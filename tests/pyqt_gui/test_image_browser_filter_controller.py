"""File inventory records and the browser rows they give."""

from pathlib import Path
from types import SimpleNamespace
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
from openhcs.core.result_file_formats import (
    RoiArchiveResultFile,
    TextResultFile,
    TiffResultFile,
)
from openhcs.core.component_filters import ComponentFilters
from openhcs.core.components.parser_metaprogramming import FilenameParseResult
from openhcs.core.config import GlobalPipelineConfig
from openhcs.core.pipeline.path_planner import PathPlannerPathAuthority
from openhcs.core.plate_image_inventory import (
    PlateImageInventory,
    PlateFileInventoryQuery,
    PlateFileKind,
    PlateFileInventory,
    PlateResultFileInventory,
    PlateResultFileRecord,
)
from openhcs.core.dataset_sources.interfaces import (
    AnalysisResultDirectory,
    FilenameParserCapability,
    MetadataHandler,
)
from openhcs.core.plate_image_inventory import PlateFileRecord
from openhcs.pyqt_gui.widgets.image_browser import (
    BrowsedFile,
    ImageFile,
    ResultFile,
    ViewerBatch,
)


def _rows(records) -> dict[str, BrowsedFile]:
    return {row.key: row for record in records for row in BrowsedFile.of(record)}


class _ResultOnlyOrchestrator:
    def __init__(self, plate_path: Path, config: GlobalPipelineConfig) -> None:
        self.dataset_root = plate_path
        self.microscope_handler = None
        self._config = config

    def get_effective_config(self) -> GlobalPipelineConfig:
        return self._config

    def initialize_microscope_handler(self) -> None:
        return None


class _InventoryParser:
    def parse_filename(self, filename: str):
        if "A01" not in filename:
            return None
        return FilenameParseResult.from_wire_mapping(
            {"well": "A01"},
            extension=".tif",
        )


class _InventoryMetadataHandler(MetadataHandler):
    """Inherits the handler defaults (workspace root, no virtual workspace)."""
    def __init__(self, handler_result_dir: Path) -> None:
        self._handler_result_dir = handler_result_dir

    def get_image_files(self, _plate_path: Path, *, all_subdirs: bool):
        assert all_subdirs is True
        return ("images/A01_w1.tif",)

    def find_metadata_file(self, _plate_path: Path) -> Path:
        raise AssertionError("Inventory does not read the metadata file.")

    def get_grid_dimensions(self, _plate_path: Path):
        raise AssertionError("Inventory does not read grid dimensions.")

    def get_pixel_size(self, _plate_path: Path):
        raise AssertionError("Inventory does not read pixel size.")

    def component_value_set(self, _plate_path: Path):
        raise AssertionError("Inventory does not read the component value set.")

    def source_workspace_root(self, plate_path: Path) -> Path:
        return plate_path

    def analysis_result_directories(self, _plate_path: Path):
        return (
            AnalysisResultDirectory(
                subdirectory_name="results",
                path=self._handler_result_dir,
            ),
        )


class _InventoryMicroscopeHandler(FilenameParserCapability):
    def __init__(self, handler_result_dir: Path) -> None:
        self.metadata_handler = _InventoryMetadataHandler(handler_result_dir)
        self.parser = _InventoryParser()

    def get_primary_backend(self, _plate_path: Path, _filemanager: FileManager) -> str:
        return "disk"


class _LazyInventoryOrchestrator:
    def __init__(self, plate_path: Path, handler_result_dir: Path) -> None:
        self.dataset_root = plate_path
        self.microscope_handler = None
        self._handler = _InventoryMicroscopeHandler(handler_result_dir)
        self._config = GlobalPipelineConfig()
        self.filemanager = FileManager({"disk": DiskStorageBackend()})
        self.initialized = False

    def initialize_microscope_handler(self) -> None:
        self.initialized = True
        self.microscope_handler = self._handler

    def get_effective_config(self) -> GlobalPipelineConfig:
        return self._config


def test_image_browser_projects_shared_result_inventory_records(tmp_path: Path):
    roi_path = tmp_path / "plate" / "results" / "A01.roi.zip"
    text_path = tmp_path / "plate" / "results" / "summary.txt"
    roi_path.parent.mkdir(parents=True)
    roi_path.write_bytes(b"roi")
    text_path.write_text("summary", encoding="utf-8")
    inventory = PlateResultFileInventory(
        plate_path=tmp_path / "plate",
        scanned_file_count=2,
        records=(
            PlateResultFileRecord(
                relative_path="results/A01.roi.zip",
                full_path=str(roi_path),
                file_format=RoiArchiveResultFile,
                metadata={
                    "filename": "results/A01.roi.zip",
                    "type": "ROI",
                    "well": "A01",
                },
            ),
            PlateResultFileRecord(
                relative_path="results/summary.txt",
                full_path=str(text_path),
                file_format=TextResultFile,
                metadata={
                    "filename": "results/summary.txt",
                    "type": "TEXT",
                    "well": "A01",
                },
            ),
        ),
    )

    rows = _rows(PlateFileRecord.from_result(record) for record in inventory.records)

    roi_row = rows["results/A01.roi.zip"]
    assert isinstance(roi_row, ResultFile)
    assert (roi_row.file_format, roi_row.path) == (RoiArchiveResultFile, roi_path)
    assert roi_row["type"] == "ROI"
    text_row = rows["results/summary.txt"]
    assert (text_row.file_format, text_row.path) == (TextResultFile, text_path)
    assert dict(text_row)["type"] == "TEXT"

    # Each format decides what a viewer batch receives: ROIs stream, text does not.
    batch = ViewerBatch()
    for row in rows.values():
        row.add_to(batch)
    assert (batch.image_paths, batch.roi_paths) == ([], [str(roi_path)])


def test_image_browser_projects_result_images_as_streamable_images(tmp_path: Path):
    image_path = tmp_path / "plate" / "results" / "A01_labels.tif"
    image_path.parent.mkdir(parents=True)
    image_path.write_bytes(b"result image")
    inventory = PlateResultFileInventory(
        plate_path=tmp_path / "plate",
        scanned_file_count=1,
        records=(
            PlateResultFileRecord(
                relative_path="results/A01_labels.tif",
                full_path=str(image_path),
                file_format=TiffResultFile,
                metadata={
                    "filename": "results/A01_labels.tif",
                    "type": "TIFF",
                    "well": "A01",
                },
            ),
        ),
    )

    rows = _rows(PlateFileRecord.from_result(record) for record in inventory.records)

    row = rows["results/A01_labels.tif"]
    assert isinstance(row, ImageFile)
    assert row.record.kind is PlateFileKind.RESULT
    assert row.image_path == str(image_path)
    batch = ViewerBatch()
    row.add_to(batch)
    assert (batch.image_paths, batch.roi_paths) == ([str(image_path)], [])


def test_plate_file_inventory_reads_path_planned_result_only_output(
    tmp_path: Path,
) -> None:
    plate_root = tmp_path / "source_plate_openhcs"
    config = GlobalPipelineConfig()
    result_dir = PathPlannerPathAuthority.analysis_results_dir_for(
        plate_root / config.path_planning_config.sub_dir,
    )
    result_dir.mkdir(parents=True)
    detail_csv = result_dir / "A01_w1_cell_counts_step0_details.csv"
    summary_text = result_dir / "A01_w1_segmentation_masks_step0_summary.txt"
    detail_csv.write_text("slice_index,cell_count\n0,11\n", encoding="utf-8")
    summary_text.write_text("Segmentation ROIs: 11 cells\n", encoding="utf-8")
    orchestrator = _ResultOnlyOrchestrator(plate_root, config)

    inventory = PlateFileInventory.from_orchestrator(orchestrator)

    assert inventory.image_records == ()
    assert inventory.scanned_result_file_count == 2
    assert [record.relative_path for record in inventory.result_records] == [
        "images_results/A01_w1_cell_counts_step0_details.csv",
        "images_results/A01_w1_segmentation_masks_step0_summary.txt",
    ]


def test_plate_file_inventory_from_lazy_orchestrator_uses_public_inventory_path(
    tmp_path: Path,
) -> None:
    plate_root = tmp_path / "plate"
    image_path = plate_root / "images" / "A01_w1.tif"
    handler_result_dir = plate_root / "results"
    image_path.parent.mkdir(parents=True)
    handler_result_dir.mkdir(parents=True)
    image_path.write_bytes(b"image")
    (handler_result_dir / "A01_summary.txt").write_text(
        "handler result\n",
        encoding="utf-8",
    )
    orchestrator = _LazyInventoryOrchestrator(plate_root, handler_result_dir)

    image_inventory = PlateImageInventory.from_orchestrator(orchestrator)
    file_inventory = PlateFileInventory.from_orchestrator(orchestrator)

    assert orchestrator.initialized is True
    assert [record.virtual_path for record in image_inventory.records] == [
        "images/A01_w1.tif"
    ]
    assert [record.virtual_path for record in file_inventory.image_records] == [
        "images/A01_w1.tif"
    ]
    assert [record.relative_path for record in file_inventory.result_records] == [
        "results/A01_summary.txt"
    ]


def test_plate_file_inventory_from_handler_matches_browser_file_shape(
    tmp_path: Path,
) -> None:
    plate_root = tmp_path / "plate"
    image_path = plate_root / "images" / "A01_w1.tif"
    handler_result_dir = plate_root / "results"
    config = GlobalPipelineConfig()
    output_dataset_root = PathPlannerPathAuthority.build_output_dataset_root(
        plate_root,
        config.path_planning_config,
    )
    output_result_dir = PathPlannerPathAuthority.analysis_results_dir_for(
        output_dataset_root / config.path_planning_config.sub_dir,
    )
    image_path.parent.mkdir(parents=True)
    handler_result_dir.mkdir(parents=True)
    output_result_dir.mkdir(parents=True)
    image_path.write_bytes(b"image")
    (handler_result_dir / "A01_handler_summary.txt").write_text(
        "handler result\n",
        encoding="utf-8",
    )
    (output_result_dir / "A01_output_counts.csv").write_text(
        "well,count\nA01,3\n",
        encoding="utf-8",
    )

    inventory = PlateFileInventory.from_handler(
        plate_path=plate_root,
        handler=_InventoryMicroscopeHandler(handler_result_dir),
        filemanager=FileManager({"disk": DiskStorageBackend()}),
        backend="disk",
        path_config=config.path_planning_config,
        all_subdirs=True,
    )

    assert [record.virtual_path for record in inventory.image_records] == [
        "images/A01_w1.tif"
    ]
    assert inventory.image_records[0].metadata["well"] == "A01"
    assert [record.relative_path for record in inventory.result_records] == [
        "images_results/A01_output_counts.csv",
        "results/A01_handler_summary.txt",
    ]
    assert inventory.result_records[0].full_path == str(
        output_result_dir / "A01_output_counts.csv"
    )
    assert inventory.scanned_result_file_count == 2
    assert inventory.result_inventory.records == inventory.result_records


def test_plate_file_inventory_query_returns_unified_browser_records(
    tmp_path: Path,
) -> None:
    plate_root = tmp_path / "plate"
    image_path = plate_root / "images" / "A01_w1.tif"
    handler_result_dir = plate_root / "results"
    image_path.parent.mkdir(parents=True)
    handler_result_dir.mkdir(parents=True)
    image_path.write_bytes(b"image")
    (handler_result_dir / "A01_summary.txt").write_text(
        "handler result\n",
        encoding="utf-8",
    )

    inventory = PlateFileInventory.from_handler(
        plate_path=plate_root,
        handler=_InventoryMicroscopeHandler(handler_result_dir),
        filemanager=FileManager({"disk": DiskStorageBackend()}),
        backend="disk",
        all_subdirs=True,
    )

    query_result = inventory.query_files(
        PlateFileInventoryQuery(
            kinds=(PlateFileKind.IMAGE,),
            component_filters=ComponentFilters.from_mapping({"well": "A01"}),
        )
    )
    rows = _rows(inventory.file_records())

    assert query_result.total_count == 1
    assert query_result.records[0].key == "images/A01_w1.tif"
    assert isinstance(rows["images/A01_w1.tif"], ImageFile)
    assert rows["images/A01_w1.tif"]["well"] == "A01"
    assert rows["results/A01_summary.txt"].file_format is TextResultFile
