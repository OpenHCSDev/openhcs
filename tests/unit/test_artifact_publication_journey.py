"""Issue315: tiny public compiler and saved-checkpoint source journeys."""

import json
from pathlib import Path
from queue import Queue

import numpy as np
import pytest
import tifffile
from polystore.virtual_workspace import SourcePixelRef

from openhcs.constants.constants import GroupBy, VariableComponents, Microscope
from openhcs.core.config import (
    LazyPathPlanningConfig,
    PipelineConfig,
    LazyProcessingConfig,
    LazyStepMaterializationConfig,
)
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.progress import set_progress_queue
from openhcs.core.artifacts import ArtifactSpec, ObjectLabelsArtifactType
from openhcs.core.pipeline.function_contracts import (
    artifact_inputs, artifact_outputs, object_label_input_execution_mode,
    ObjectLabelInputExecutionMode,
)
from openhcs.core.memory import numpy as numpy_decorator
from openhcs.core.runtime_object_label_building import SourceImageObjectLabelBuildRequest
from openhcs.core.runtime_object_labels import ObjectLabelValue
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.source_projection import (
    OpenHCSPlaneAddress,
    SourcePlaneProjection,
    SourceProjectionMetadataSerializer,
    SourceProjectionSet,
)
from openhcs.core.steps.function_step import FunctionStep
from openhcs.core.steps.function_outputs import OpenHCSMetadataWriter
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser
from openhcs.processing.backends.cellprofiler.object_images import (
    ImageMode,
    convert_objects_to_image,
)


@artifact_outputs(ArtifactSpec.output("objects", ObjectLabelsArtifactType))
@numpy_decorator(contract=ProcessingContract.PURE_2D)
def tiny_objects(image: np.ndarray) -> ObjectLabelValue:
    return SourceImageObjectLabelBuildRequest(
        image=image, labels=(np.asarray(image) > 0).astype(np.int32),
        declared_object_count=1, declared_object_ids=(1,),
    ).payload()


@artifact_inputs(ArtifactSpec.input("objects", ObjectLabelsArtifactType, parameter_name="labels"))
@numpy_decorator(contract=ProcessingContract.PURE_3D)
@object_label_input_execution_mode(ObjectLabelInputExecutionMode.FULL_STACK)
def render_labels(image: np.ndarray, labels: ObjectLabelValue) -> np.ndarray:
    return convert_objects_to_image(image, labels, image_mode=ImageMode.UINT16)


@pytest.fixture(autouse=True)
def progress_events():
    set_progress_queue(Queue())
    yield
    set_progress_queue(None)


def _plate(root: Path) -> Path:
    root.mkdir()
    path = root / "A01_s001_w1_z001_t001.tif"
    pixels = np.zeros((8, 8), dtype=np.uint16)
    pixels[2:5, 2:5] = 1
    tifffile.imwrite(path, pixels)
    address = OpenHCSPlaneAddress.from_values("A01", 1, 1, 1, 1)
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
    document = SourceProjectionMetadataSerializer(SourceSchemaFilenameParser()).metadata_dict(
        SourceProjectionSet((projection,)),
        microscope_handler_name=Microscope.OPENHCS.value,
        source_filename_parser_name="SourceSchemaFilenameParser",
        grid_dimensions=[1, 1],
        pixel_size=0.65,
        main=True,
        projection_paths=((projection, path.name),),
    )
    (root / "openhcs_metadata.json").write_text(json.dumps({"subdirectories": {".": document}}))
    return root


def _compile(root: Path, results: Path):
    plate = _plate(root / "source")
    config = PipelineConfig(
        materialization_results_path=results,
        path_planning_config=LazyPathPlanningConfig(output_dir_suffix="_out", well_filter=0),
        processing_config=LazyProcessingConfig(
            group_by=GroupBy.CHANNEL,
            variable_components=[VariableComponents.SITE],
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
    ]
    return orchestrator, steps, orchestrator.compile_pipelines(steps)


def test_public_planning_rejects_external_results_root(tmp_path):
    with pytest.raises(ValueError, match="materialization_results_path.*output plate root"):
        _compile(tmp_path, tmp_path / "external-results")


def test_converted_checkpoint_has_typed_address_on_final_reconciliation(tmp_path):
    orchestrator, steps, bundle = _compile(tmp_path, Path("results"))
    for context in bundle.runtime_contexts.values():
        for index, step in enumerate(steps):
            step.process(context, index)
    OpenHCSMetadataWriter.finalize_completed_plate(bundle.runtime_contexts)
    saved = tmp_path / "source_out" / "converted"
    files = tuple(saved.glob("*.tif"))
    assert len(files) == 1
    assert tifffile.imread(files[0]).sum() == 9
    metadata = json.loads((saved.parent / "openhcs_metadata.json").read_text())
    entry = metadata["subdirectories"]["converted"]
    assert len(entry["source_projection"]) == 1
    assert entry["source_projection"][0]["address"]["well"] == "A01"
