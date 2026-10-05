"""Canonical callable twice through document, compiler, execution and publication."""

from csv import DictReader
from inspect import unwrap

import numpy as np
import pytest
import tifffile

from openhcs.agent.services.execution_session_service import (
    AgentProgressQueue,
    CompileInspectionInput,
    InProcessCompileInspectionGateway,
)
from openhcs.constants import AllComponents, Microscope
from openhcs.core.artifacts import ArtifactInputPlan, ImageArtifactType
from openhcs.core.config import (
    GlobalPipelineConfig,
    LazyPathPlanningConfig,
    LazySourceBindingsConfig,
    LazyStepMaterializationConfig,
    PipelineConfig,
)
from openhcs.core.function_patterns import MainFlowInputProjection
from openhcs.core.orchestrator.execution_result import RuntimeObservationMode
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.core.runtime_image_values import image_payload_data
from openhcs.core.runtime_object_labels import object_label_dense_array
from openhcs.core.runtime_stores import RuntimeArtifactQuery
from openhcs.core.source_bindings import (
    ComponentSelector,
    NamedSourceBinding,
    SourceFilterClause,
    SourceFilterMatchType,
    SourceFilterSubject,
    SourceSelector,
)
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.custom_functions.runtime_registry import (
    CustomFunctionRuntimeRegistry,
    register_custom_function,
)
from polystore.roi import load_rois_from_zip

# Reuse the public reference's authoritative code block, not a copied callable.
from tests.unit.agent.test_callable_artifact_reference import reference_namespace  # noqa: F401


@pytest.fixture
def registered_reference_callable(reference_namespace):
    """Give the executable public example its actual custom catalog lifetime."""
    function = reference_namespace["inspect_label_fixture"]
    registered = register_custom_function(function)
    try:
        assert unwrap(registered) is unwrap(function)
        yield function
    finally:
        CustomFunctionRuntimeRegistry.remove(function.__name__)


def test_chained_public_callable_uses_declared_main_flow_not_storage_argument(
    tmp_path, reference_namespace, registered_reference_callable,
):
    assert reference_namespace["inspect_label_fixture"] is registered_reference_callable
    plate = tmp_path / "plate"
    plate.mkdir()
    fixture = np.zeros((8, 8), dtype=np.uint16)
    fixture[2:6, 3:7] = 1
    tifffile.imwrite(plate / "A01_s001_label-fixture.tif", fixture)
    source = NamedSourceBinding(
        alias="label-fixture",
        selector=SourceSelector(filters=(
            SourceFilterClause(
                subject=SourceFilterSubject.FILE,
                match_type=SourceFilterMatchType.CONTAINS,
                value="label-fixture",
            ),
        )),
        component_identity=(ComponentSelector(AllComponents.CHANNEL, "1"),),
    )
    document = PipelineDocumentAuthority.from_values(
        pipeline_config=PipelineConfig(
            num_workers=1,
            use_threading=True,
            microscope=Microscope.SOURCE_BINDINGS,
            source_bindings_config=LazySourceBindingsConfig(bindings=(source,)),
            path_planning_config=LazyPathPlanningConfig(
                global_output_folder=tmp_path / "outputs",
            ),
        ),
        pipeline_steps=[
            FunctionStep(
                func=reference_namespace["inspect_label_fixture"],
                name=f"PublicLabelFixture{index}",
                step_materialization_config=LazyStepMaterializationConfig(enabled=True),
            )
            for index in range(2)
        ],
    )
    document = PipelineDocumentAuthority.from_source(
        PipelineDocumentAuthority.render(document)
    )
    bundle = InProcessCompileInspectionGateway().compile(
        CompileInspectionInput(
            plate=plate,
            pipeline_document=document,
            axis_filter=("A01",),
            global_pipeline_config=GlobalPipelineConfig(num_workers=1, use_threading=True),
            progress_queue=AgentProgressQueue(),
        )
    ).execution_bundle
    context = bundle.runtime_contexts["A01"]
    first, second = (context.step_plans[index] for index in range(2))
    first_invocation = next(first.compiled_function_pattern.iter_invocations())
    second_invocation = next(second.compiled_function_pattern.iter_invocations())
    [first_image] = (
        plan for plan in first_invocation.artifact_output_plans
        if plan.artifact_type is ImageArtifactType
    )
    incoming_ref = first_image.ref().for_plan_type(ArtifactInputPlan)
    # Storage provenance exists, but is not a second callable argument authority.
    assert second.artifact_inputs[incoming_ref].source_step_id == 0
    [edge] = second_invocation.artifact_input_edges
    assert edge.spec.ref() == incoming_ref
    assert edge.spec.parameter_name is None
    assert second_invocation.contract.group_scope_inputs.ref_set() == {incoming_ref}
    assert edge.main_flow_projection is not None
    assert edge.main_flow_projection is MainFlowInputProjection.COMPLETE_PAYLOAD
    assert edge.storage_plan is None
    assert edge.projection is None

    orchestrator = PipelineOrchestrator(
        plate, pipeline_config=document.pipeline_config,
    ).initialize()
    results = orchestrator.execute_compiled_plate(
        execution_bundle=bundle,
        max_workers=1,
        runtime_observation_mode=RuntimeObservationMode.MERGE_INTO_PARENT,
        progress_queue=AgentProgressQueue(),
        progress_context={
            "execution_id": "chained-public-callable-synthetic",
            "plate_id": str(plate),
            "axis_id": "",
        },
    )
    assert results["A01"].is_success(), results["A01"].error_message
    for step_plan in (first, second):
        invocation = next(step_plan.compiled_function_pattern.iter_invocations())
        image_plan, labels_plan, rows_plan = invocation.artifact_output_plans
        records = []
        for plan in (image_plan, labels_plan, rows_plan):
            [record] = context.runtime_value_store.find_matching(
                RuntimeArtifactQuery.from_output_plan(
                    plan, axis_id="A01", backend="memory",
                    group_key=plan.group_scope().select_runtime_key(
                        invocation.key.group_key
                    ),
                )
            )
            records.append(record)
        image, labels, rows = (record.data for record in records)
        np.testing.assert_array_equal(np.squeeze(image_payload_data(image)), fixture)
        np.testing.assert_array_equal(np.squeeze(object_label_dense_array(labels)), fixture)
        assert rows.subject.object_name == labels_plan.name
        assert rows.subject.id_field == "object_label"
        assert tuple(rows.rows.column_values("object_label")) == (1,)
        assert tuple(rows.rows.column_values("pixel_count")) == (16,)
        assert rows_plan.object_subject_binding().source == labels_plan.ref()
        analysis = step_plan.artifact_analysis_output_dir
        [csv_path] = analysis.glob(
            f"*_{rows_plan.name}_step{step_plan.step_index}_details.csv"
        )
        with csv_path.open(newline="") as stream:
            [persisted] = DictReader(stream)
        assert persisted["object_label"] == "1"
        assert persisted["pixel_count"] == "16"
        [roi_path] = analysis.glob(f"*_{labels_plan.name}_step{step_plan.step_index}*.zip")
        assert len(load_rois_from_zip(roi_path)) == 1
        saved_images = tuple(step_plan.materialized_output.output_dir.glob("*.tif"))
        assert saved_images
        for image_path in saved_images:
            np.testing.assert_array_equal(np.squeeze(tifffile.imread(image_path)), fixture)
