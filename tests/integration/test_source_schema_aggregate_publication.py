"""Real scalar aggregation through the installed compiler/runtime/export owners.

Tiny synthetic input only; no native/viewer, altered geometry or prebuilt runtime
record. The original source-schema parser must admit genuinely collapsed Z while
the normal image writer preserves all four pass-through source planes.
"""

from csv import DictReader
from hashlib import sha256

import numpy as np
import tifffile

from openhcs.agent.services.execution_session_service import (
    AgentProgressQueue,
    CompileInspectionInput,
    InProcessCompileInspectionGateway,
)
from openhcs.constants import AllComponents, GroupBy, Microscope, VariableComponents
from openhcs.constants.input_source import InputSource
from openhcs.core.artifacts import ImageArtifactType, MainFlowStackOutputSpec, SpecialArtifactType
from openhcs.core.config import (
    GlobalPipelineConfig,
    LazyProcessingConfig,
    LazySourceBindingsConfig,
    PipelineConfig,
)
from openhcs.core.memory import numpy as numpy_function
from openhcs.core.orchestrator.execution_result import RuntimeObservationMode
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.pipeline.function_contracts import artifact_outputs
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.core.source_bindings import (
    ComponentSelector,
    MetadataExtractionRule,
    MetadataSource,
    NamedSourceBinding,
    SourceSelector,
)
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.processing.custom_functions.runtime_registry import (
    CustomFunctionRuntimeRegistry,
    register_custom_function,
)
from openhcs.processing.materialization import CsvOptions, MaterializationSpec


@numpy_function(contract=ProcessingContract.PURE_3D)
@artifact_outputs(
    MainFlowStackOutputSpec.output("PassThrough", ImageArtifactType),
    MainFlowStackOutputSpec.output(
        "VolumeScalar609", SpecialArtifactType,
        materialization=MaterializationSpec(CsvOptions()),
    ),
)
def volume_scalar_609(image: np.ndarray):
    """Return the actual whole-stack sum and voxel count, retaining main flow."""
    return image, ({"volume_sum": int(image.sum()), "voxel_count": int(image.size)},)


def test_real_z_aggregation_persists_scalar_and_unchanged_source_planes(tmp_path):
    source = tmp_path / "input"
    source.mkdir()
    pixels = np.arange(140, dtype=np.uint16).reshape(4, 5, 7)
    originals = []
    for index, plane in enumerate(pixels, 1):
        image = source / f"A01_s001_w1_z{index:03d}_t001.tif"
        tifffile.imwrite(image, plane)
        originals.append((image, sha256(image.read_bytes()).hexdigest()))

    registered = register_custom_function(volume_scalar_609)
    try:
        document = PipelineDocumentAuthority.from_values(
            pipeline_config=PipelineConfig(
                microscope=Microscope.SOURCE_BINDINGS,
                source_bindings_config=LazySourceBindingsConfig(
                    metadata_rules=(MetadataExtractionRule(
                        source=MetadataSource.FILE_NAME,
                        pattern=r"(?P<well>A[0-9]+)_s(?P<site>[0-9]+)_w(?P<channel>[0-9]+)_z(?P<z_index>[0-9]+)_t(?P<timepoint>[0-9]+)",
                    ),),
                    bindings=(NamedSourceBinding(
                        alias="Fixture", selector=SourceSelector(),
                        component_identity=(ComponentSelector(AllComponents.CHANNEL, "1"),),
                    ),),
                ),
            ),
            pipeline_steps=[FunctionStep(
                func=registered, name="Actual volume scalar",
                processing_config=LazyProcessingConfig(
                    variable_components=[VariableComponents.Z_INDEX],
                    group_by=GroupBy.CHANNEL,
                    input_source=InputSource.PIPELINE_START,
                ),
            )],
        )
        bundle = InProcessCompileInspectionGateway().compile(CompileInspectionInput(
            plate=source, pipeline_document=document, axis_filter=("A01",),
            global_pipeline_config=GlobalPipelineConfig(num_workers=1, use_threading=True),
            progress_queue=AgentProgressQueue(),
        )).execution_bundle
        context = bundle.runtime_contexts["A01"]
        assert tuple(context.step_plans[0].variable_components) == (VariableComponents.Z_INDEX,)
        orchestrator = PipelineOrchestrator(source, pipeline_config=document.pipeline_config).initialize()
        outcomes = orchestrator.execute_compiled_plate(
            execution_bundle=bundle, max_workers=1,
            runtime_observation_mode=RuntimeObservationMode.MERGE_INTO_PARENT,
            progress_queue=AgentProgressQueue(),
        )
        assert outcomes["A01"].is_success(), outcomes["A01"].error_message
        (csv_path,) = tuple(tmp_path.rglob("*VolumeScalar609*details.csv"))
        with csv_path.open(newline="") as stream:
            (row,) = tuple(DictReader(stream))
        assert int(row["volume_sum"]) == int(pixels.sum())
        assert int(row["voxel_count"]) == pixels.size
        assert "_z" not in csv_path.name
        saved = tuple(context.step_plans[0].materialized_output.output_dir.glob("*.tif"))
        assert len(saved) == 4
        for image in saved:
            z_index = int(image.name.split("_z", 1)[1].split("_", 1)[0])
            np.testing.assert_array_equal(tifffile.imread(image), pixels[z_index - 1])
        for image, checksum in originals:
            assert sha256(image.read_bytes()).hexdigest() == checksum
    finally:
        CustomFunctionRuntimeRegistry.remove(volume_scalar_609.__name__)
