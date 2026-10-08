"""Default selection belongs to the existing metadata transaction."""

import copy
import hashlib
import json
from pathlib import Path

import numpy as np
import pytest
import tifffile
from polystore.virtual_workspace import SourcePixelRef

from openhcs.constants.constants import AllComponents, Microscope
from openhcs.core.source_projection import (
    OpenHCSPlaneAddress, SourcePlaneProjection, SourceProjectionMetadataSerializer,
)
from openhcs.core.source_metadata import (
    SOURCE_VOXEL_SPACING_FIELD, SOURCE_VOXEL_SPACING_UNIT_FIELD,
)
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.source_image_provenance import SourceImageProvenance
from openhcs.core.virtual_workspace_metadata import (
    AtomicMetadataWriter, FIELDS, VirtualWorkspaceSourceProjectionEntries,
    MetadataWriteError,
)
from openhcs.microscopes.openhcs import OpenHCSMetadataHandler
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser


@pytest.mark.parametrize("method", ["merge", "replace"])
def test_explicit_promotion_preserves_other_projection_and_nonpromotion(tmp_path, method):
    path = tmp_path / "openhcs_metadata.json"
    writer = AtomicMetadataWriter()
    original = {"main": True, "image_files": ["images/one.tif"],
                "workspace_mapping": {}, "pixel_size": 0.65,
                "grid_dimensions": [3, 3], "source_metadata": {"origin": {"value": "retained"}}}
    writer.replace_subdirectory_metadata(path, "images", original)
    promoted = {"main": True, "image_files": ["selected.tif"]}
    if method == "merge":
        writer.merge_subdirectory_metadata(path, {".": promoted})
    else:
        writer.replace_subdirectory_metadata(path, ".", promoted)
    document = json.loads(path.read_text())[FIELDS.SUBDIRECTORIES]
    assert document["images"] == {**original, "main": False}
    assert document["."] == promoted
    if method == "merge":
        writer.merge_subdirectory_metadata(path, {"auxiliary": {"image_files": []}})
    else:
        writer.replace_subdirectory_metadata(path, "auxiliary", {"image_files": []})
    assert json.loads(path.read_text())[FIELDS.SUBDIRECTORIES]["."] == promoted


def test_conflicting_promotions_leave_original_document_unchanged(tmp_path):
    path = tmp_path / "openhcs_metadata.json"
    writer = AtomicMetadataWriter()
    writer.replace_subdirectory_metadata(path, "images", {"main": True})
    original = path.read_bytes()
    with pytest.raises(MetadataWriteError, match="Multiple.*explicitly promoted"):
        writer.merge_subdirectory_metadata(path, {"first": {"main": True}, "second": {"main": True}})
    assert path.read_bytes() == original


def test_reader_still_rejects_ambiguous_metadata():
    handler = OpenHCSMetadataHandler(None)
    with pytest.raises(ValueError, match="Multiple.*marked main"):
        handler._main_subdirectory_name({"images": {"main": True}, ".": {"main": True}}, Path("/synthetic"))


def test_publication_promotes_without_changing_retained_inventory(tmp_path):
    writer = AtomicMetadataWriter()
    path = tmp_path / "openhcs_metadata.json"
    original = {"main": True, "image_files": ["original.tif"], "pixel_size": 0.65}
    writer.replace_subdirectory_metadata(path, "original", original)
    publication = dict(
        serializer=SourceProjectionMetadataSerializer(SourceSchemaFilenameParser()),
        saved_image_paths=(), microscope_handler_name="openhcs",
        source_filename_parser_name="SourceSchemaFilenameParser", component_labels={},
        backend="disk", results_dir=None,
    )
    entries = VirtualWorkspaceSourceProjectionEntries.combine(())
    writer.publish_source_projection_metadata(path, "new", entries, is_main=True, **publication)
    document = json.loads(path.read_text())[FIELDS.SUBDIRECTORIES]
    assert document["original"] == {**original, "main": False}
    selected = copy.deepcopy(document["new"])
    writer.publish_source_projection_metadata(path, "auxiliary", entries, is_main=False, **publication)
    assert json.loads(path.read_text())[FIELDS.SUBDIRECTORIES]["new"] == selected


def test_completed_plate_rejects_conflicting_declared_targets_atomically(tmp_path):
    from polystore.base import ensure_storage_registry, storage_registry
    from polystore.filemanager import FileManager
    from openhcs.core.context.processing_context import ProcessingContext
    from openhcs.core.steps.function_outputs import PrimaryImageMetadataTarget

    ensure_storage_registry()
    context = ProcessingContext(axis_id="A01", filemanager=FileManager(dict(storage_registry)))
    targets = []
    for name in ("first", "second"):
        directory = tmp_path / name
        directory.mkdir()
        tifffile.imwrite(directory / "A01_s001_w1_z001_t001.tif", np.ones((8, 8), dtype=np.uint16))
        targets.append(PrimaryImageMetadataTarget(
            output_dir=directory, backend="disk", plate_root=str(tmp_path), sub_dir=name, results_dir=None,
        ))
    writer = AtomicMetadataWriter()
    path = tmp_path / "openhcs_metadata.json"
    writer.replace_subdirectory_metadata(path, "original", {"main": True})
    before = path.read_bytes()
    with pytest.raises(MetadataWriteError, match="Multiple.*explicitly promoted"):
        writer.reconcile_completed_plate(path, {target: context for target in targets})
    assert path.read_bytes() == before


def test_persist_eighteen_select_two_reopen_and_compile(tmp_path):
    from objectstate.lazy_factory import ensure_global_config_context
    from polystore.base import ensure_storage_registry, storage_registry
    from polystore.filemanager import FileManager
    from openhcs.core.config import GlobalPipelineConfig, PipelineConfig, LazySourceBindingsConfig
    from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
    from openhcs.core.source_bindings import (
        MetadataExtractionRule, MetadataSource,
        SourceFilterClause, SourceFilterMatchType, SourceFilterSubject,
    )
    from openhcs.core.steps.function_step import FunctionStep
    from openhcs.core.progress import set_progress_queue
    from queue import Queue
    from openhcs.processing.backends.processors.numpy_processor import stack_percentile_normalize

    root = tmp_path / "persisted"
    images = root / "images"
    images.mkdir(parents=True)
    paths = []
    projections = []
    for site in range(1, 10):
        for channel in (1, 2):
            relative = f"images/A01_s{site:03}_w{channel}_z001_t001.tif"
            path = root / relative
            tifffile.imwrite(path, np.arange(64, dtype=np.uint16).reshape(8, 8) + site * channel,
                             metadata={"axes": "YX"})
            paths.append(relative)
            projections.append((SourcePlaneProjection(
                address=OpenHCSPlaneAddress.from_values("A01", site, channel, 1, 1),
                ref=SourcePixelRef("disk", relative),
                source_metadata={SOURCE_VOXEL_SPACING_FIELD: "0.65,0.65",
                                 SOURCE_VOXEL_SPACING_UNIT_FIELD: "micrometers"},
                image_metadata=ImagePayloadMetadata(
                    source_dtype="uint16",
                    source_provenance=SourceImageProvenance(source_path=f"acquisition/site-{site}/channel-{channel}"),
                ),
            ), relative))
    hashes = {p: hashlib.sha256((root / p).read_bytes()).hexdigest() for p in paths}
    writer = AtomicMetadataWriter()
    metadata_path = root / "openhcs_metadata.json"
    serializer = SourceProjectionMetadataSerializer(SourceSchemaFilenameParser())
    publication = dict(
        serializer=serializer, saved_image_paths=paths,
        microscope_handler_name="source_bindings", source_filename_parser_name="SourceSchemaFilenameParser",
        component_labels={}, backend="disk", results_dir="images_results",
    )
    entries = VirtualWorkspaceSourceProjectionEntries.from_projection_paths(projections)
    writer.publish_source_projection_metadata(metadata_path, "images", entries, is_main=True, **publication)
    original_images = copy.deepcopy(json.loads(metadata_path.read_text())[FIELDS.SUBDIRECTORIES]["images"])
    # Non-primary publication cannot steal the existing default.
    writer.publish_source_projection_metadata(metadata_path, "auxiliary", entries, is_main=False, **publication)
    assert json.loads(metadata_path.read_text())[FIELDS.SUBDIRECTORIES]["images"] == original_images
    (root / "images_results").mkdir()

    ensure_storage_registry()
    manager = FileManager(dict(storage_registry))
    global_config = GlobalPipelineConfig(num_workers=1, use_threading=True, microscope=Microscope.SOURCE_BINDINGS)
    ensure_global_config_context(GlobalPipelineConfig, global_config)
    selection = LazySourceBindingsConfig(
        metadata_rules=(MetadataExtractionRule(
            source=MetadataSource.FILE_NAME,
            pattern=r"(?P<well>A\d+)_s(?P<site>\d+)_w(?P<channel>\d+)_z(?P<z_index>\d+)_t(?P<timepoint>\d+)",
        ),),
        source_filters=(SourceFilterClause(
            subject=SourceFilterSubject.FILE, match_type=SourceFilterMatchType.CONTAINS, value="_s009_",
        ),),
    )
    owner = PipelineOrchestrator(root, pipeline_config=PipelineConfig(source_bindings_config=selection)).initialize()
    document = json.loads(metadata_path.read_text())[FIELDS.SUBDIRECTORIES]
    assert document["images"] == {**original_images, "main": False}
    assert document["."]["main"] is True
    assert len(document["."][FIELDS.IMAGE_FILES]) == 2
    reopened = OpenHCSMetadataHandler(manager)
    assert reopened.determine_main_subdirectory(root) == "."
    assert set(reopened.component_value_set(root).values_for(AllComponents.SITE)) == {"9"}
    assert tuple(reopened.source_workspace_metadata_document(root)[FIELDS.SUBDIRECTORIES]) == (".",)
    assert len(reopened.source_workspace_metadata_document(images)[FIELDS.SUBDIRECTORIES]["images"][FIELDS.IMAGE_FILES]) == 18
    assert {d.subdirectory_name for d in reopened.analysis_result_directories(root)} == {"images", "auxiliary"}
    assert {d.subdirectory_name for d in reopened.analysis_result_directories(images)} == {"images"}
    set_progress_queue(Queue())
    try:
        bundle = owner.compile_pipelines([FunctionStep(name="Synthetic normalization", func=stack_percentile_normalize)])
    finally:
        set_progress_queue(None)
    assert bundle.axis_ids == ("A01",)
    assert len(owner.source_workspace_files()) == 2
    assert hashes == {p: hashlib.sha256((root / p).read_bytes()).hexdigest() for p in paths}
    invalid_root = tmp_path / "invalid"
    invalid_root.mkdir()
    invalid = copy.deepcopy(json.loads(metadata_path.read_text()))
    invalid[FIELDS.SUBDIRECTORIES]["images"]["main"] = True
    (invalid_root / "openhcs_metadata.json").write_text(json.dumps(invalid))
    invalid_reader = OpenHCSMetadataHandler(manager)
    with pytest.raises(ValueError, match="Multiple.*marked main"):
        invalid_reader.source_workspace_metadata_document(invalid_root)
    print("native compiler: persisted18 -> selected2 -> reopened '.'; original18 TIFF hashes and images metadata preserved")
