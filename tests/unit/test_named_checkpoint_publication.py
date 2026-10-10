"""PR316: preserve both named and ordinary 24-SITE checkpoint publication.

The numerical outputs are synthetic, not a BaSiCPy fit. The actual public
compiler, runtime materialization, metadata reconciliation and reopen are used.
"""

from dataclasses import dataclass, replace
import json

import numpy as np
import pytest
import tifffile

from test_artifact_publication_journey import _plate, progress_events
from openhcs.core.artifacts import (
    QaCheckpoint, ImageArtifactType, MainFlowPlaneProjectionOutputSpec,
    MainFlowStackOutputSpec,
)
from openhcs.core.config import (
    LazyPathPlanningConfig, LazyProcessingConfig, LazyStepMaterializationConfig,
    PipelineConfig,
)
from openhcs.core.memory import numpy as numpy_decorator
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.orchestrator.execution_result import RuntimeContextObservation, RuntimeExecutionObservation
from openhcs.core.pipeline.function_contracts import (
    artifact_outputs, required_axis_roles,
)
from openhcs.core.projected_image_output import SourceProjectedImageOutput
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_projection import OpenHCSPlaneAddress, SourceArtifactProjection
from openhcs.core.source_workspace_projection import VirtualWorkspaceSourceProjection
from openhcs.core.steps.function_outputs import OpenHCSMetadataTarget
from openhcs.core.steps.function_step import FunctionStep
from openhcs.core.virtual_workspace_metadata import MetadataWriteError
from openhcs.core.processing_contracts import (
    Pure3DContract,
)
from openhcs.processing.materialization import (
    ImageFileOptions, MaterializationSpec, MaterializedFilenameIdentity,
)
from openhcs.core.axes import TileAxis
from openhcs.domains.microscopy.axes import Microscopy



@dataclass(frozen=True)
class SyntheticAggregateField(SourceProjectedImageOutput):
    data: np.ndarray

    def with_data(self, data):
        return replace(self, data=data)

    def resolve_source_context(self, source, projection):
        assert projection is not None and projection.plane_index is None
        assert projection.axis_size == 24
        return source.metadata.collapse_leading_plane_axis().payload_with(self.data, None)


def _field(name):
    return MainFlowPlaneProjectionOutputSpec.output(
        name, ImageArtifactType, sidecar_role=QaCheckpoint,
        materialization=MaterializationSpec(ImageFileOptions(
            filename_suffix=".tif", filename_identity=MaterializedFilenameIdentity.ARTIFACT_NAME,
        )),
    )


@numpy_decorator(contract=Pure3DContract)
@required_axis_roles(TileAxis)
@artifact_outputs(
    MainFlowStackOutputSpec.output("corrected", ImageArtifactType),
    _field("flat"), _field("dark"),
)
def synthetic_three_outputs(image):
    assert image.shape == (24, 8, 8)
    return (
        np.asarray(image, dtype=np.float32) + 0.5,
        SyntheticAggregateField(np.ones((8, 8), dtype=np.float32)),
        SyntheticAggregateField(np.zeros((8, 8), dtype=np.float32)),
    )


@pytest.mark.parametrize("main_filter", (0, 1))
def test_named_and_ordinary_checkpoint_inventory_owns_every_address(tmp_path, main_filter):
    plate = _plate(tmp_path / "source", site_count=24)
    config = PipelineConfig(
        path_planning_config=LazyPathPlanningConfig(output_dir_suffix="_out", well_filter=main_filter),
        num_workers=1, use_threading=True,
    )
    orchestrator = PipelineOrchestrator(plate, pipeline_config=config).initialize()
    step = FunctionStep(
        func=synthetic_three_outputs,
        processing_config=LazyProcessingConfig(
            group_by=Microscopy.Channel, variable_components=[Microscopy.Site],
        ),
        step_materialization_config=LazyStepMaterializationConfig(enabled=True),
    )
    bundle = orchestrator.compile_pipelines([step])
    observations = RuntimeExecutionObservation(contexts=tuple(
        RuntimeContextObservation(context_key=key, records=(), outputs=step.process(context, 0))
        for key, context in bundle.runtime_contexts.items()
    ))
    OpenHCSMetadataTarget.finalize_completed_plate(
        bundle.runtime_contexts, runtime_observations=(observations,)
    )
    root = tmp_path / "source_out"
    metadata = json.loads((root / "openhcs_metadata.json").read_text())
    reopened = VirtualWorkspaceSourceProjection.from_openhcs_metadata(root, metadata)
    for target, count in (("checkpoints", 48), ("checkpoints_results", 2)):
        entry = metadata["subdirectories"][target]
        inventory = {str(path.relative_to(root)) for path in (root / target).glob("*.tif")}
        assert len(inventory) == count
        assert set(entry["image_files"]) == inventory
        assert {item["virtual_path"] for item in entry["source_projection"]} == inventory
        for item in entry["source_projection"]:
            retained = ImagePayloadMetadata.from_mapping(item["image_metadata"])
            assert retained.source_voxel_spacing == SourceVoxelSpacing((0.65, 0.65))
            assert retained.source_spatial_domain.source_shape_yx == (8, 8)
    checkpoints = metadata["subdirectories"]["checkpoints"]["source_projection"]
    ordinary = [
        projection
        for item in checkpoints
        if isinstance(
            projection := reopened.source_projections_by_virtual_path[item["virtual_path"]],
            SourceArtifactProjection,
        )
    ]
    assert len(ordinary) == len(checkpoints) - len(ordinary) == 24
    assert {projection.address for projection in ordinary} == {
        OpenHCSPlaneAddress(((Microscopy.Well, "A01"), (Microscopy.Site, site), (Microscopy.Channel, 1), (Microscopy.ZIndex, 1), (Microscopy.Timepoint, 1)))
        for site in range(1, 25)
    }
    for item in checkpoints:
        pixels = tifffile.imread(root / item["virtual_path"])
        assert pixels.shape == (8, 8)
        assert pixels.sum() == 41
    for item in metadata["subdirectories"]["checkpoints_results"]["source_projection"]:
        retained = ImagePayloadMetadata.from_mapping(item["image_metadata"])
        assert retained.source_image_provenance_planes.contributor_count == 24
        assert retained.plane_axis is None
    # The workspace index exposes both relative and absolute lookup aliases.
    # Verify canonical storage inventory, not the number of lookup keys.
    all_inventory = {
        path
        for entry in metadata["subdirectories"].values()
        for path in entry["image_files"]
    }
    assert len(all_inventory) == 50 + 24 * main_filter
    assert all_inventory.issubset(reopened.source_projections_by_virtual_path)
    if main_filter:
        assert len(metadata["subdirectories"]["images"]["image_files"]) == 24
        assert PipelineOrchestrator(root).initialize().microscope_handler.get_pixel_size(root) == 0.65
    # Keep fail-closed reconciliation: an actually unowned image is still an
    # error. This is not a missing-address permissive fallback.
    tifffile.imwrite(root / "checkpoints" / "unaddressed.tif", np.zeros((8, 8), dtype=np.uint16))
    with pytest.raises(MetadataWriteError, match="Saved images lack typed produced addresses.*unaddressed"):
        OpenHCSMetadataTarget.finalize_completed_plate(bundle.runtime_contexts)
