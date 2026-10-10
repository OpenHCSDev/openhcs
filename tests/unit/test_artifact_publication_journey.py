"""Issue315: tiny public compiler and saved-checkpoint source journeys."""

import json
from pathlib import Path
from queue import Queue

import numpy as np
import pytest
import tifffile
from polystore.virtual_workspace import SourcePixelRef

from openhcs.core.config import (
    LazyPathPlanningConfig,
    PipelineConfig,
    LazyProcessingConfig,
    LazyStepMaterializationConfig,
)
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.progress import set_progress_queue
from openhcs.core.artifacts import (
    ArtifactSpec, ObjectLabelsArtifactType, MeasurementsArtifactType,
    ArtifactMeasurementSubjectRelation,
)
from openhcs.core.function_patterns import compile_function_pattern
from openhcs.core.aligned_image_payload import AlignedImageSliceContext
from openhcs.core.measurement_row_materialization import MeasurementSparseColumnarRows
from openhcs.core.runtime_tabular_values import FieldSpec
from openhcs.core.pipeline.function_contracts import (artifact_inputs, artifact_outputs, object_label_input_execution_mode)
from openhcs.core.memory import numpy as numpy_decorator
from openhcs.core.runtime_object_label_building import SourceImageObjectLabelBuildRequest
from openhcs.core.runtime_object_labels import ObjectLabelValue
from openhcs.core.processing_contracts import (
    Pure2DContract,
    Pure3DContract,
)
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.source_workspace_projection import VirtualWorkspaceSourceProjection
from openhcs.core.source_projection import (
    OpenHCSPlaneAddress,
    SourcePlaneProjection,
    SourceProjectionMetadataSerializer,
    SourceProjectionSet,
)
from openhcs.core.steps.function_step import FunctionStep
from openhcs.core.steps.function_outputs import OpenHCSMetadataTarget
from openhcs.core.dataset_sources.source_schema import SourceSchemaFilenameParser
from openhcs.processing.backends.cellprofiler.object_images import (
    ImageMode,
    convert_objects_to_image,
)
from openhcs.domains.microscopy.axes import Microscopy
from openhcs.core.pipeline.function_contracts import (
    FullStackLabels,
)


@artifact_outputs(ArtifactSpec.output("objects", ObjectLabelsArtifactType))
@numpy_decorator(contract=Pure2DContract)
def tiny_objects(image: np.ndarray) -> ObjectLabelValue:
    return SourceImageObjectLabelBuildRequest(
        image=image, labels=(np.asarray(image) > 0).astype(np.int32),
        declared_object_count=1, declared_object_ids=(1,),
    ).payload()


@artifact_inputs(ArtifactSpec.input("objects", ObjectLabelsArtifactType, parameter_name="labels"))
@numpy_decorator(contract=Pure3DContract)
@object_label_input_execution_mode(FullStackLabels)
def render_labels(image: np.ndarray, labels: ObjectLabelValue) -> np.ndarray:
    return convert_objects_to_image(image, labels, image_mode=ImageMode.UINT16)


@artifact_outputs(ArtifactSpec.output(
    "counts", MeasurementsArtifactType,
    relations=(ArtifactMeasurementSubjectRelation(),),
))
@numpy_decorator(contract=Pure2DContract)
def tiny_counts(image: np.ndarray):
    return image, MeasurementSparseColumnarRows.from_rows(
        ({"nonzero": int(np.count_nonzero(image))},),
        fields=(FieldSpec("nonzero", int),),
    )


@pytest.fixture(autouse=True)
def progress_events():
    set_progress_queue(Queue())
    yield
    set_progress_queue(None)


def _plate(root: Path, site_count: int = 1) -> Path:
    root.mkdir()
    pixels = np.zeros((8, 8), dtype=np.uint16)
    pixels[2:5, 2:5] = 1
    projections = []
    projection_paths = []
    for site in range(1, site_count + 1):
        path = root / f"A01_s{site:03d}_w1_z001_t001.tif"
        tifffile.imwrite(path, pixels)
        address = OpenHCSPlaneAddress(((Microscopy.Well, "A01"), (Microscopy.Site, site), (Microscopy.Channel, 1), (Microscopy.ZIndex, 1), (Microscopy.Timepoint, 1)))
        metadata = ImagePayloadMetadata(
            source_path=str(path),
            source_component_metadata={**address.as_component_metadata(), "extension": ".tif"},
            source_voxel_spacing=SourceVoxelSpacing((0.65, 0.65)),
        )
        projection = SourcePlaneProjection(
            address=address,
            ref=SourcePixelRef("disk", str(path)),
            source_metadata=metadata.source_component_metadata,
            image_metadata=metadata,
        )
        projections.append(projection)
        projection_paths.append((projection, path.name))
    document = SourceProjectionMetadataSerializer(SourceSchemaFilenameParser()).metadata_dict(
        SourceProjectionSet(tuple(projections)),
        microscope_handler_name="openhcsdata",
        source_filename_parser_name="SourceSchemaFilenameParser",
        grid_dimensions=[1, 1],
        pixel_size=0.65,
        main=True,
        projection_paths=tuple(projection_paths),
    )
    (root / "openhcs_metadata.json").write_text(json.dumps({"subdirectories": {".": document}}))
    return root


def _compile(root: Path, results: Path, main_filter=0):
    plate = _plate(root / "source")
    config = PipelineConfig(
        materialization_results_path=results,
        path_planning_config=LazyPathPlanningConfig(output_dir_suffix="_out", well_filter=main_filter),
        processing_config=LazyProcessingConfig(
            group_by=Microscopy.Channel,
            variable_components=[Microscopy.Site],
        ),
        num_workers=1,
        use_threading=True,
    )
    orchestrator = PipelineOrchestrator(plate, pipeline_config=config).initialize()
    steps = [
        FunctionStep(func=tiny_objects, name="objects"),
        FunctionStep(
            func=render_labels,
            name="render",
            step_materialization_config=LazyStepMaterializationConfig(
                enabled=True, output_dir_suffix="_out", sub_dir="converted",
            ),
        ),
        FunctionStep(func=tiny_counts, name="counts"),
    ]
    return orchestrator, steps, orchestrator.compile_pipelines(steps)


def test_public_planning_rejects_external_results_root(tmp_path):
    with pytest.raises(ValueError, match="materialization_results_path.*output plate root"):
        _compile(tmp_path, tmp_path / "external-results")


@pytest.mark.parametrize("absolute", (False, True))
@pytest.mark.parametrize("main_filter", (0, 1))
def test_converted_checkpoint_has_typed_address_on_final_reconciliation(tmp_path, absolute, main_filter):
    results = tmp_path / "source_out" / "results" if absolute else Path("results")
    orchestrator, steps, bundle = _compile(tmp_path, results, main_filter)
    for context in bundle.runtime_contexts.values():
        for index, step in enumerate(steps):
            step.process(context, index)
    OpenHCSMetadataTarget.finalize_completed_plate(bundle.runtime_contexts)
    saved = tmp_path / "source_out" / "converted"
    files = tuple(saved.glob("*.tif"))
    assert len(files) == 1
    assert tifffile.imread(files[0]).sum() == 9
    metadata = json.loads((saved.parent / "openhcs_metadata.json").read_text())
    entry = metadata["subdirectories"]["converted"]
    assert len(entry["source_projection"]) == 1
    [projection] = entry["source_projection"]
    assert projection["address"]["well"] == "A01"
    projected_metadata = ImagePayloadMetadata.from_mapping(projection["image_metadata"])
    assert projected_metadata.source_voxel_spacing == SourceVoxelSpacing((0.65, 0.65))
    assert Path(projected_metadata.source_path).parent == tmp_path / "source"
    assert projected_metadata.source_spatial_domain.source_shape_yx == (8, 8)
    assert entry["image_files"] == [projection["virtual_path"]]
    # Reopen the durable typed projection. Zero automatic main-flow output must
    # not invent a default main when independently saved targets coexist.
    reopened_metadata = orchestrator.microscope_handler.metadata_handler.load_metadata_document(saved.parent)
    reopened = VirtualWorkspaceSourceProjection.from_openhcs_metadata(saved.parent, reopened_metadata)
    retained = reopened.source_projections_by_virtual_path[projection["virtual_path"]]
    assert retained.address == OpenHCSPlaneAddress(((Microscopy.Well, "A01"), (Microscopy.Site, 1), (Microscopy.Channel, 1), (Microscopy.ZIndex, 1), (Microscopy.Timepoint, 1)))
    assert retained.image_metadata.source_voxel_spacing == SourceVoxelSpacing((0.65, 0.65))
    assert retained.image_metadata.source_path == projected_metadata.source_path
    if main_filter:
        reopened_plate = PipelineOrchestrator(saved.parent).initialize()
        assert reopened_plate.microscope_handler.get_pixel_size(saved.parent) == 0.65
    # Native objects retain their independent artifact publication/control.
    [object_projection] = metadata["subdirectories"]["results"]["source_projection"]
    assert object_projection["artifact_kind"] == ObjectLabelsArtifactType.value
    assert tifffile.imread(saved.parent / object_projection["virtual_path"]).sum() == 9
    import csv

    [table_path] = (saved.parent / "results").glob("*.csv")
    with table_path.open(newline="") as handle:
        [row] = csv.DictReader(handle)
    assert row["nonzero"] == "9"


def test_planning_rejects_relative_results_escape(tmp_path):
    with pytest.raises(ValueError, match="materialization_results_path.*output plate root"):
        _compile(tmp_path, Path("../external-results"))


def test_planning_preserves_symlinked_plate_identity(tmp_path):
    actual = tmp_path / "actual"
    actual.mkdir()
    alias = tmp_path / "alias"
    alias.symlink_to(actual, target_is_directory=True)
    _orchestrator, _steps, bundle = _compile(alias, Path("results"))
    for context in bundle.runtime_contexts.values():
        for plan in context.step_plans.values():
            assert Path(plan.analysis_results_dir).is_relative_to(plan.output_plate_root)


def test_planning_rejects_symlinked_results_escape(tmp_path):
    outside = tmp_path / "outside"
    outside.mkdir()
    output = tmp_path / "source_out"
    output.mkdir()
    (output / "results").symlink_to(outside, target_is_directory=True)
    with pytest.raises(ValueError, match="materialization_results_path.*output plate root"):
        _compile(tmp_path, Path("results"))


def test_new_unnamed_replacement_and_table_passthrough_contracts():
    def another_image(image):
        return image + 1

    @artifact_outputs(ArtifactSpec.output(
        "counts", MeasurementsArtifactType,
        relations=(ArtifactMeasurementSubjectRelation(),),
    ))
    def table_only(image):
        return image

    replacement = compile_function_pattern(another_image, {}, {}).default_group
    assert replacement.unwrapped_main_flow_output_context({}) == (
        AlignedImageSliceContext.anonymous_main_flow()
    )
    retained = compile_function_pattern(table_only, {}, {}).default_group
    assert retained.unwrapped_main_flow_output_context({}) is None
