"""Real IPO/secondary authoring -> compile -> execute -> persisted artifacts.

Run only in the coordinator's serialized native-validation slot. There is no
private plate, segmentation replacement, mocked runtime or biological verdict.
"""

import numpy as np
import pytest


def _field(empty=False):
    yy, xx = np.mgrid[:32, :40]
    image = (
        0.8 * np.exp(-((yy - 14) ** 2 + (xx - 14) ** 2) / 14)
        + 0.7 * np.exp(-((yy - 14) ** 2 + (xx - 20) ** 2) / 14)
        + 0.25 * np.exp(-((yy - 24) ** 2 + (xx - 30) ** 2) / 8)
    ).astype(np.float32)
    return np.zeros_like(image) if empty else image


@pytest.mark.parametrize("mode", ["empty", "disabled", "intensity", "shape"])
def test_real_registered_ipo_returns_same_run_stage_pixels(mode):
    from openhcs.core.config import DtypeConfig
    from openhcs.core.runtime_image_values import image_payload_data
    from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
    from openhcs.processing.backends.cellprofiler.primary_object_diagnostics import PrimaryObjectDiagnosticPlanes
    from openhcs.processing.backends.cellprofiler.primary_objects import UnclumpMethod, WatershedMethod
    from openhcs.processing.backends.cellprofiler.morphology import FillHolesOption
    from openhcs.processing.backends.cellprofiler.thresholding import CellProfilerThresholdMethod

    image = _field(mode == "empty")
    method = UnclumpMethod.NONE if mode == "disabled" else (
        UnclumpMethod.SHAPE if mode == "shape" else UnclumpMethod.INTENSITY
    )
    func = CellProfilerModule.require_module("IdentifyPrimaryObjects").require_callable()
    original, measurements, objects, *planes = func(
        image, min_diameter=2, max_diameter=20,
        exclude_size=False, exclude_border_objects=False,
        unclump_method=method, watershed_method=WatershedMethod.INTENSITY,
        threshold_method=CellProfilerThresholdMethod.MANUAL, manual_threshold=0.2,
        threshold_smoothing_scale=0.0, fill_holes=FillHolesOption.NEVER,
        automatic_smoothing=False, smoothing_filter_size=1,
        automatic_suppression=False, maxima_suppression_size=2,
        low_res_maxima=False, dtype_config=DtypeConfig(),
    )
    diagnostics = PrimaryObjectDiagnosticPlanes(*planes)
    np.testing.assert_array_equal(image_payload_data(original), image)
    np.testing.assert_array_equal(diagnostics.threshold_support.data, image > 0.2)
    np.testing.assert_array_equal(diagnostics.unedited_objects.data, objects.unedited_labels)
    np.testing.assert_array_equal(diagnostics.small_removed_objects.data, objects.small_removed_labels)
    assert measurements.row_count > 0
    if mode in ("empty", "disabled"):
        assert not diagnostics.declump_response.mask.any()
        assert np.isnan(diagnostics.declump_response.data).all()
        assert not diagnostics.seed_markers.data.any()
    else:
        assert diagnostics.declump_response.mask.all()
        assert diagnostics.seed_markers.data.max() > 0
        np.testing.assert_array_equal(diagnostics.seed_markers.data > 0, diagnostics.seed_maxima.data)
    if mode == "empty":
        assert not objects.labels.any()


def test_normal_compiled_runtime_persists_diagnostics_and_preserves_secondary_binding(tmp_path):
    import tifffile
    from openhcs.agent.services.execution_session_service import (
        AgentProgressQueue, CompileInspectionInput, InProcessCompileInspectionGateway,
    )
    from openhcs.constants import AllComponents, GroupBy, Microscope, VariableComponents
    from openhcs.constants.input_source import InputSource
    from openhcs.core.artifacts import ArtifactInputPlan, ArtifactOutputPlan, ImageArtifactType, ObjectLabelsArtifactType
    from openhcs.core.config import GlobalPipelineConfig, LazyProcessingConfig, LazySourceBindingsConfig, PipelineConfig
    from openhcs.core.orchestrator.execution_result import RuntimeObservationMode
    from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
    from openhcs.core.pipeline_document import PipelineDocumentAuthority
    from openhcs.core.runtime_image_values import image_payload_data, image_payload_metadata
    from openhcs.core.runtime_object_labels import object_label_dense_array
    from openhcs.core.source_bindings import (
        ComponentSelector, NamedSourceBinding, SourceFilterClause, SourceFilterMatchType,
        SourceFilterSubject, SourceSelector, StepSourceBindingsConfig,
    )
    from openhcs.core.steps.function_step import FunctionStep
    from openhcs.processing.backends.cellprofiler.primary_objects import (
        IdentifyPrimaryObjectsModule, UnclumpMethod, WatershedMethod, identify_primary_objects,
    )
    from openhcs.processing.backends.cellprofiler.primary_object_diagnostics import PrimaryObjectDiagnosticPlanes
    from openhcs.processing.backends.cellprofiler.secondary import (
        IdentifySecondaryObjectsModule, SecondaryMethod, identify_secondary_objects,
    )
    from openhcs.processing.backends.cellprofiler.thresholding import CellProfilerThresholdMethod

    def binding(module, plan_type, artifact_type):
        (declared,) = module.declared_artifact_bindings(plan_type=plan_type, artifact_type=artifact_type)
        return declared.require_parameter_name()

    def step(func, name, kwargs):
        return FunctionStep(
            func=(func, kwargs), name=name,
            processing_config=LazyProcessingConfig(
                variable_components=[VariableComponents.SITE], group_by=GroupBy.NONE,
                input_source=InputSource.PIPELINE_START,
            ),
            source_bindings=StepSourceBindingsConfig(enabled=True),
        )

    image = _field()
    tifffile.imwrite(tmp_path / "A01_s001_DNA.tif", image)
    primary = step(identify_primary_objects, "Primary", {
        binding(IdentifyPrimaryObjectsModule, ArtifactInputPlan, ImageArtifactType): "DNA",
        binding(IdentifyPrimaryObjectsModule, ArtifactOutputPlan, ObjectLabelsArtifactType): "Nuclei",
        "exclude_size": False, "exclude_border_objects": False,
        "min_diameter": 2, "max_diameter": 20,
        "unclump_method": UnclumpMethod.INTENSITY,
        "watershed_method": WatershedMethod.INTENSITY,
        "threshold_method": CellProfilerThresholdMethod.MANUAL,
        "manual_threshold": 0.2, "threshold_smoothing_scale": 0.0,
    })
    secondary = step(identify_secondary_objects, "Secondary", {
        binding(IdentifySecondaryObjectsModule, ArtifactInputPlan, ImageArtifactType): "DNA",
        binding(IdentifySecondaryObjectsModule, ArtifactInputPlan, ObjectLabelsArtifactType): "Nuclei",
        IdentifySecondaryObjectsModule.secondary_output_binding.require_parameter_name(): "Cells",
        "method": SecondaryMethod.DISTANCE_N, "distance_to_dilate": 2,
    })
    document = PipelineDocumentAuthority.from_values(
        pipeline_config=PipelineConfig(
            microscope=Microscope.SOURCE_BINDINGS,
            source_bindings_config=LazySourceBindingsConfig(bindings=(NamedSourceBinding(
                alias="DNA", selector=SourceSelector(filters=(SourceFilterClause(
                    subject=SourceFilterSubject.FILE, match_type=SourceFilterMatchType.CONTAINS,
                    value="DNA",
                ),)), component_identity=(ComponentSelector(AllComponents.CHANNEL, "1"),),
            ),)),
        ), pipeline_steps=[primary, secondary],
    )
    document = PipelineDocumentAuthority.from_source(PipelineDocumentAuthority.render(document))
    bundle = InProcessCompileInspectionGateway().compile(CompileInspectionInput(
        plate=tmp_path, pipeline_document=document, axis_filter=("A01",),
        global_pipeline_config=GlobalPipelineConfig(num_workers=1, use_threading=True),
        progress_queue=AgentProgressQueue(),
    )).execution_bundle
    context = bundle.runtime_contexts["A01"]
    primary_invocation = next(context.step_plans[0].compiled_function_pattern.iter_invocations())
    secondary_invocation = next(context.step_plans[1].compiled_function_pattern.iter_invocations())
    (edge,) = (edge for edge in secondary_invocation.artifact_input_edges
               if edge.spec.artifact_type is ObjectLabelsArtifactType)
    assert edge.spec.name == "Nuclei"
    assert edge.storage_plan.source_step_id == 0
    assert len(primary_invocation.contract.artifact_outputs.of_artifact_type(ObjectLabelsArtifactType)) == 1

    orchestrator = PipelineOrchestrator(tmp_path, pipeline_config=document.pipeline_config).initialize()
    results = orchestrator.execute_compiled_plate(
        execution_bundle=bundle, max_workers=1,
        runtime_observation_mode=RuntimeObservationMode.MERGE_INTO_PARENT,
        progress_queue=AgentProgressQueue(), progress_context={
            "execution_id": "primary-diagnostics-synthetic", "plate_id": str(tmp_path), "axis_id": "",
        },
    )
    assert results["A01"].is_success(), results["A01"].error_message
    store = context.runtime_value_store
    (primary_record,) = store.find(name="Nuclei", axis_id="A01")
    (secondary_record,) = store.find(name="Cells", axis_id="A01")
    assert np.count_nonzero(object_label_dense_array(secondary_record.value.data)) >= np.count_nonzero(
        object_label_dense_array(primary_record.value.data)) > 0
    diagnostic_specs = tuple(spec for spec in primary_invocation.contract.artifact_outputs
                             if spec.sidecar_role is not None)
    assert len(diagnostic_specs) == len(PrimaryObjectDiagnosticPlanes._fields)
    persisted = []
    for spec in diagnostic_specs:
        (record,) = store.find(name=spec.name, artifact_type=ImageArtifactType, axis_id="A01")
        reloaded = orchestrator.filemanager.load(record.path, record.backend)
        np.testing.assert_array_equal(image_payload_data(reloaded), image_payload_data(record.value.data))
        assert image_payload_metadata(record.value.data).source_path.endswith("A01_s001_DNA.tif")
        persisted.append(record.value.data)
    diagnostics = PrimaryObjectDiagnosticPlanes(*persisted)
    np.testing.assert_array_equal(diagnostics.unedited_objects.data, primary_record.value.data.unedited_labels)
    np.testing.assert_array_equal(diagnostics.small_removed_objects.data, primary_record.value.data.small_removed_labels)
