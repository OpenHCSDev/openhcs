"""Real source-document, headless compiler, and runtime selector journey."""

from __future__ import annotations

from dataclasses import dataclass, replace
from csv import DictReader
from inspect import unwrap

import numpy as np
import pytest
import tifffile

from openhcs.agent.services.artifact_plan_inspection_service import (
    AgentProgressQueue,
    CompileInspectionInput,
    InProcessCompileInspectionGateway,
)
from openhcs.constants.input_source import InputSource
from openhcs.core.artifacts import (
    ArtifactInputPlan,
    ArtifactOutputPlan,
    ArtifactSpecCollection,
    ImageArtifactType,
    ImageMeasurementSubjectRelation,
    MainFlowStackOutputSpec,
    MeasurementsArtifactType,
    ObjectLabelsArtifactType,
)
from openhcs.core.config import (
    GlobalPipelineConfig,
    LazyProcessingConfig,
    LazySourceBindingsConfig,
    PipelineConfig,
)
from openhcs.core.function_patterns import normalize_function_pattern
from openhcs.core.invocation_artifacts import (
    ArtifactDeclarationStepContext,
    MainFlowArtifactContractProvider,
)
from openhcs.core.function_step_document import FunctionStepDocumentCodec
from openhcs.core.measurement_feature_queries import measurement_values_for_feature
from openhcs.core.measurement_row_materialization import DataclassMeasurementColumnarRows
from openhcs.core.memory import numpy
from openhcs.core.orchestrator.execution_result import RuntimeObservationMode
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.core.pipeline.function_contracts import artifact_outputs
from openhcs.core.runtime_object_labels import object_label_dense_array
from openhcs.core.runtime_measurements import (
    RuntimeMeasurementFeature,
    RuntimeMeasurementFeatureOwner,
)
from openhcs.core.source_bindings import (
    ComponentSelector,
    NamedSourceBinding,
    SourceFilterClause,
    SourceFilterMatchType,
    SourceFilterSubject,
    SourceSelector,
    SourceBindingMatchMethod,
    SourceBindingMatchPlan,
    StepSourceBindingsConfig,
)
from openhcs.core.steps.function_step import FunctionStep
from openhcs.interop.cellprofiler.measurement_dialect import (
    CELLPROFILER_MEASUREMENT_LOOKUP_DIALECT,
)
from openhcs.processing.backends.cellprofiler.intensity import (
    MeasureObjectIntensityModule,
    measure_object_intensity,
)
from openhcs.processing.backends.cellprofiler.primary_objects import (
    IdentifyPrimaryObjectsModule,
    UnclumpMethod,
    WatershedMethod,
    identify_primary_objects,
)
from openhcs.processing.backends.cellprofiler.secondary import (
    IdentifySecondaryObjectsModule,
    SecondaryMethod,
    identify_secondary_objects,
)
from openhcs.processing.backends.cellprofiler.thresholding import (
    CellProfilerThresholdMethod,
)
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.processing.custom_functions.runtime_registry import (
    CustomFunctionRuntimeRegistry,
    register_custom_function,
)
from openhcs.processing.materialization import CsvOptions, MaterializationSpec
from openhcs.core.axes import Ungrouped
from openhcs.domains.microscopy.axes import Microscopy
from openhcs.core.dataset_sources.source_bindings_source import SourceBindingsSource


@dataclass(frozen=True)
class CountRow:
    slice_index: int
    pixel_count: int


class CountFeature(RuntimeMeasurementFeature):
    PIXEL_COUNT = "pixel_count"


class CountFeatureOwner(RuntimeMeasurementFeatureOwner):
    feature_type = CountFeature

    @classmethod
    def owns_measurement_feature_name(cls, feature_name):
        return any(feature.value == feature_name for feature in cls.feature_type)

    @classmethod
    def owns_primary_measurement_feature_name(cls, feature_name):
        return cls.owns_measurement_feature_name(feature_name)


COUNT_IMAGE = MainFlowStackOutputSpec.output("CountedImage", ImageArtifactType)
MISSING_SUBJECT_ROWS = MainFlowStackOutputSpec.output(
    "PixelCounts", MeasurementsArtifactType,
    materialization=MaterializationSpec(CsvOptions()),
    measurement_feature_owner=CountFeatureOwner,
)
IMAGE_SUBJECT_ROWS = replace(
    MISSING_SUBJECT_ROWS,
    relations=(
        *MISSING_SUBJECT_ROWS.relations,
        ImageMeasurementSubjectRelation(COUNT_IMAGE.ref()),
    ),
)


@numpy(contract=ProcessingContract.PURE_3D)
@artifact_outputs(COUNT_IMAGE, MISSING_SUBJECT_ROWS)
def count_without_subject(image):
    raise AssertionError("A missing subject must fail before callable execution")


@numpy(contract=ProcessingContract.PURE_3D)
@artifact_outputs(COUNT_IMAGE, IMAGE_SUBJECT_ROWS)
def count_with_image_subject(image):
    return image, DataclassMeasurementColumnarRows(
        (CountRow(0, int(np.count_nonzero(image))),), row_type=CountRow
    )


@numpy(contract=ProcessingContract.PURE_3D)
def half_current_pixels(image):
    """Transform main flow without declaring a separately named image artifact."""
    return image / 2


@pytest.fixture(scope="module")
def registered_current_transform():
    registered = register_custom_function(half_current_pixels)
    try:
        yield registered
    finally:
        CustomFunctionRuntimeRegistry.remove(half_current_pixels.__name__)


@pytest.fixture
def registered_count_callable(valid):
    function = count_with_image_subject if valid else count_without_subject
    registered = register_custom_function(function)
    try:
        assert unwrap(registered) is unwrap(function)
        yield registered
    finally:
        CustomFunctionRuntimeRegistry.remove(function.__name__)


def _binding_name(module, plan_type, artifact_type):
    (binding,) = module.declared_artifact_bindings(
        plan_type=plan_type, artifact_type=artifact_type
    )
    return binding.require_parameter_name()


def _source(alias, channel):
    return NamedSourceBinding(
        alias=alias,
        selector=SourceSelector(
            filters=(
                SourceFilterClause(
                    subject=SourceFilterSubject.FILE,
                    match_type=SourceFilterMatchType.CONTAINS,
                    value=f"_w{channel}_",
                ),
            ),
        ),
        component_identity=(ComponentSelector(Microscopy.Channel, channel),),
    )


def _step(func, name, kwargs):
    return FunctionStep(
        func=(func, kwargs),
        name=name,
        processing_config=LazyProcessingConfig(
            variable_components=[Microscopy.Site],
            group_by=Ungrouped,
            input_source=InputSource.PIPELINE_START,
        ),
        source_bindings=StepSourceBindingsConfig(enabled=True),
    )


def _document(*, selected=True, two_producers=True, same_source=False):
    measurement_image = "DNA" if same_source else "Actin"
    primary = _step(
        identify_primary_objects,
        "Primary",
        {
            _binding_name(IdentifyPrimaryObjectsModule, ArtifactInputPlan, ImageArtifactType): "DNA",
            _binding_name(IdentifyPrimaryObjectsModule, ArtifactOutputPlan, ObjectLabelsArtifactType): "Nuclei",
            "exclude_size": False,
            "exclude_border_objects": False,
            "unclump_method": UnclumpMethod.NONE,
            "watershed_method": WatershedMethod.NONE,
            "threshold_method": CellProfilerThresholdMethod.MANUAL,
            "manual_threshold": 0.5,
            "threshold_smoothing_scale": 0.0,
        },
    )
    secondary = _step(
        identify_secondary_objects,
        "Secondary",
        {
            _binding_name(IdentifySecondaryObjectsModule, ArtifactInputPlan, ImageArtifactType): measurement_image,
            _binding_name(IdentifySecondaryObjectsModule, ArtifactInputPlan, ObjectLabelsArtifactType): "Nuclei",
            IdentifySecondaryObjectsModule.secondary_output_binding.require_parameter_name(): "Cells",
            "method": SecondaryMethod.DISTANCE_N,
            "distance_to_dilate": 2,
        },
    )
    kwargs = {
        MeasureObjectIntensityModule.image_measurement_binding.require_parameter_name(): (measurement_image,),
    }
    if selected:
        kwargs[
            MeasureObjectIntensityModule.object_measurement_binding.require_parameter_name()
        ] = ("Cells" if two_producers else "Nuclei",)
    measure = _step(measure_object_intensity, "Measure cells", kwargs)
    return PipelineDocumentCodec.from_values(
        pipeline_config=PipelineConfig(
            dataset_source=SourceBindingsSource,
            source_bindings_config=LazySourceBindingsConfig(
                bindings=(_source("DNA", "1"),) if same_source else (
                    _source("DNA", "1"), _source("Actin", "2"),
                ),
            ),
        ),
        pipeline_steps=[primary, secondary, measure] if two_producers else [primary, measure],
    )


def _write_plate(path, *, same_source=False):
    dna = np.full((16, 16), 0.25 if same_source else 0.0, dtype=np.float32)
    dna[6:8, 6:8] = 1.0
    actin = np.ones_like(dna)
    tifffile.imwrite(path / "A01_s001_w1_z001_t001.tif", dna)
    tifffile.imwrite(path / "A01_s001_w2_z001_t001.tif", actin)


def _compile(path, document, global_config):
    return InProcessCompileInspectionGateway().compile(
        CompileInspectionInput(
            plate=path,
            pipeline_document=document,
            axis_filter=("A01",),
            global_pipeline_config=global_config,
            progress_queue=AgentProgressQueue(),
        )
    ).execution_bundle


def _execute(path, document, bundle):
    orchestrator = PipelineOrchestrator(
        path, pipeline_config=document.pipeline_config
    ).initialize()
    return orchestrator.execute_compiled_plate(
        execution_bundle=bundle,
        max_workers=1,
        runtime_observation_mode=RuntimeObservationMode.MERGE_INTO_PARENT,
        progress_queue=AgentProgressQueue(),
        progress_context={
            "execution_id": "measurement-contract-synthetic",
            "plate_id": str(path),
            "axis_id": "",
        },
    )


@pytest.mark.parametrize("image_names,current_scale", [
    (("DNA",), 1), (("DNA", "Actin"), 1), (("Actin", "DNA"), 1),
    (("DNAHalf",), 1), (("DNA", "DNAHalf"), 1), (("DNAHalf", "DNA"), 1),
    (("DNA", "Actin"), 0.5),
])
def test_photometry_carrier_preserves_raw_aliases_and_produced_pixels(
    tmp_path, image_names, current_scale, registered_current_transform,
):
    """A stored label cohort must not substitute label IDs for measured images."""
    from openhcs.processing.backends.cellprofiler.intensity import rescale_intensity, RescaleMethod
    dna = np.zeros((16, 16), dtype=np.float32)
    dna[6:8, 6:8] = ((0.6, 0.7), (0.8, 0.9))
    actin = (0.1 + np.arange(256).reshape(16, 16) * 0.001).astype(np.float32)
    tifffile.imwrite(tmp_path / "A01_s001_w1_z001_t001.tif", dna)
    tifffile.imwrite(tmp_path / "A01_s001_w2_z001_t001.tif", actin)
    document = _document()
    if "DNAHalf" in image_names:
        document.pipeline_steps.insert(0, _step(rescale_intensity, "Produced half intensity", {
            "select_the_input_image": "DNA", "name_the_output_image": "DNAHalf",
            "rescale_method": RescaleMethod.DIVIDE_BY_VALUE, "divisor_value": 2.0,
        }))
    document.pipeline_steps[-1] = _step(measure_object_intensity, "Actual photometry", {
        "select_images_to_measure": image_names, "select_object_sets_to_measure": ("Cells",),
    })
    if current_scale != 1:
        document.pipeline_steps.insert(-1, _step(
            registered_current_transform, "Transform current image carrier", {},
        ))
        measurement = document.pipeline_steps[-1]
        measurement.processing_config = replace(
            measurement.processing_config, input_source=InputSource.PREVIOUS_STEP,
        )
    document = PipelineDocumentCodec.from_source(PipelineDocumentCodec.render(document))
    bundle = _compile(tmp_path, document, GlobalPipelineConfig(num_workers=1, use_threading=True))
    context = bundle.runtime_contexts["A01"]
    plan = context.step_plans[len(document.pipeline_steps)-1]
    group = plan.compiled_function_pattern.default_group
    selected = plan.stored_primary_input_edges_for_group(group, None)
    if any(name in ("DNA", "Actin") for name in image_names):
        assert selected is None  # Raw STEP_INPUT aliases need the current image carrier.
    results = _execute(tmp_path, document, bundle)
    assert results['A01'].is_success(), results['A01'].error_message
    (labels,) = context.runtime_value_store.find(name="Cells", axis_id="A01")
    foreground = object_label_dense_array(labels.data).squeeze() == 1
    (invocation,) = group.invocations
    (output,) = invocation.artifact_output_plans
    (measurement,) = context.runtime_value_store.find(
        name=output.name, artifact_type=MeasurementsArtifactType, axis_id="A01",
    )
    expected_images = {
        "DNA": dna * current_scale, "Actin": actin * current_scale, "DNAHalf": dna / 2,
    }
    for image_name in image_names:
        values = expected_images[image_name][foreground]
        assert values.size and values.std() > 0
        for feature, expected in (("MeanIntensity", values.mean()), ("MinIntensity", values.min()),
                                  ("MaxIntensity", values.max()), ("StdIntensity", values.std())):
            actual = measurement_values_for_feature(
                (measurement.data,), f"Intensity_{feature}_{image_name}",
                object_count=1, object_name="Cells", dialect=CELLPROFILER_MEASUREMENT_LOOKUP_DIALECT,
            )
            assert tuple(actual) == pytest.approx((expected,), abs=1e-7)


def test_label_only_measurement_keeps_stored_cohort(tmp_path):
    from openhcs.processing.backends.cellprofiler.shape import (
        MeasureObjectSizeShapeModule, measure_object_size_shape,
    )
    _write_plate(tmp_path)
    document = _document()
    document.pipeline_steps[-1] = _step(measure_object_size_shape, "Label-only area", {
        MeasureObjectSizeShapeModule.object_measurement_binding.require_parameter_name(): ("Cells",),
        "calculate_advanced": False, "calculate_zernikes": False,
    })
    document = PipelineDocumentCodec.from_source(PipelineDocumentCodec.render(document))
    bundle = _compile(tmp_path, document, GlobalPipelineConfig(num_workers=1, use_threading=True))
    context = bundle.runtime_contexts["A01"]
    plan = context.step_plans[len(document.pipeline_steps) - 1]
    group = plan.compiled_function_pattern.default_group
    cohort = plan.stored_primary_input_edges_for_group(group, None)
    assert cohort is not None
    assert tuple(edge.spec.name for edge in cohort) == ("Cells",)
    results = _execute(tmp_path, document, bundle)
    assert results["A01"].is_success(), results["A01"].error_message
    (labels,) = context.runtime_value_store.find(name="Cells", axis_id="A01")
    (invocation,) = group.invocations
    (output,) = invocation.artifact_output_plans
    (measurement,) = context.runtime_value_store.find(
        name=output.name, artifact_type=MeasurementsArtifactType, axis_id="A01",
    )
    actual = measurement_values_for_feature(
        (measurement.data,), "AreaShape_Area", object_count=1, object_name="Cells",
        dialect=CELLPROFILER_MEASUREMENT_LOOKUP_DIALECT,
    )
    assert tuple(actual) == (np.count_nonzero(object_label_dense_array(labels.data)),)


@pytest.mark.parametrize("same_source", [True, False], ids=["single-source", "paired-channels"])
def test_exact_secondary_selector_survives_authoring_compile_and_execution(tmp_path, same_source):
    _write_plate(tmp_path, same_source=same_source)
    document = _document(same_source=same_source)
    selector = MeasureObjectIntensityModule.object_measurement_binding.require_parameter_name()
    source = PipelineDocumentCodec.render(document)
    reconstructed = PipelineDocumentCodec.from_source(source)
    measurement = reconstructed.pipeline_steps[-1]
    step_source = FunctionStepDocumentCodec.render(
        FunctionStepDocumentCodec.from_value(measurement)
    )
    measurement = FunctionStepDocumentCodec.from_source(step_source).step
    reconstructed.pipeline_steps[-1] = measurement
    authored = next(normalize_function_pattern(measurement.func).iter_items())
    assert authored.kwargs_dict[selector] == ("Cells",)
    assert "labels" not in authored.kwargs_dict

    global_config = GlobalPipelineConfig(num_workers=1, use_threading=True)
    bundle = _compile(tmp_path, reconstructed, global_config)
    context = bundle.runtime_contexts["A01"]
    secondary_invocation = next(
        context.step_plans[1].compiled_function_pattern.iter_invocations()
    )
    label_input, image_input = IdentifySecondaryObjectsModule.segmentation_inputs(
        secondary_invocation.contract.artifact_inputs
    )
    assert label_input.source_context_sources() == (image_input.ref(),)
    assert image_input.name == ("DNA" if same_source else "Actin")
    plan = context.step_plans[2]
    invocation = next(plan.compiled_function_pattern.iter_invocations())
    (edge,) = (
        edge for edge in invocation.artifact_input_edges
        if edge.spec.artifact_type is ObjectLabelsArtifactType
    )
    assert edge.spec.name == "Cells"
    assert edge.spec.parameter_name == "labels"
    assert edge.storage_plan.source_step_id == 1
    producer_output = next(
        output for output in secondary_invocation.artifact_output_plans
        if output.ref() == edge.spec.ref().for_plan_type(ArtifactOutputPlan)
    )
    assert edge.storage_plan.relations == producer_output.relations
    assert selector not in invocation.kwargs_dict
    assert "labels" not in invocation.kwargs_dict

    results = _execute(tmp_path, reconstructed, bundle)
    assert results["A01"].is_success(), results["A01"].error_message
    store = context.runtime_value_store
    [primary] = store.find(name="Nuclei", axis_id="A01")
    [secondary] = store.find(name="Cells", axis_id="A01")
    assert primary.key.scope.value_text_for_component(Microscopy.Channel) == "1"
    assert secondary.key.scope.value_text_for_component(Microscopy.Channel) == (
        "1" if same_source else "2"
    )
    primary_area = np.count_nonzero(object_label_dense_array(primary.data))
    secondary_area = np.count_nonzero(object_label_dense_array(secondary.data))
    assert secondary_area > primary_area > 0
    [output] = invocation.artifact_output_plans
    [measurement] = store.find(name=output.name, artifact_type=MeasurementsArtifactType, axis_id="A01")
    assert measurement.data.subject.object_name == "Cells"
    image_name = "DNA" if same_source else "Actin"
    values = measurement_values_for_feature(
        (measurement.data,),
        f"Intensity_IntegratedIntensity_{image_name}",
        object_count=1,
        object_name="Cells",
        dialect=CELLPROFILER_MEASUREMENT_LOOKUP_DIALECT,
    )
    # The DNA seed is four bright pixels; the grown cell adds dim background.
    # Measuring primary labels instead would return exactly 4.0.
    expected = 4.0 + 0.25 * (secondary_area - 4) if same_source else float(secondary_area)
    assert tuple(values) == (expected,)


def test_omitted_secondary_selector_still_fails_closed(tmp_path):
    _write_plate(tmp_path)
    with pytest.raises(ValueError, match="cannot reconstruct an exact module block"):
        _compile(
            tmp_path,
            _document(selected=False),
            GlobalPipelineConfig(num_workers=1, use_threading=True),
        )


@pytest.mark.parametrize("producer_group_by", [Ungrouped, Microscopy.Channel])
def test_explicit_measurement_rosters_preserve_compiled_source_groups(
    tmp_path, producer_group_by,
):
    from openhcs.core.steps.function_execution import FunctionStepExecutor

    _write_plate(tmp_path)
    original = _document()
    for producer in original.pipeline_steps[:-1]:
        producer.processing_config = replace(
            producer.processing_config, group_by=producer_group_by,
        )
    original.pipeline_steps[-1] = _step(
        measure_object_intensity,
        "Measure both source images and object sets",
        {
            MeasureObjectIntensityModule.image_measurement_binding.require_parameter_name(): ("DNA", "Actin"),
            MeasureObjectIntensityModule.object_measurement_binding.require_parameter_name(): ("Nuclei", "Cells"),
        },
    )
    document = PipelineDocumentCodec.from_values(
        pipeline_config=replace(
            original.pipeline_config,
            source_bindings_config=LazySourceBindingsConfig(
                bindings=(_source("DNA", "1"), _source("Actin", "2")),
                match_plan=SourceBindingMatchPlan(method=SourceBindingMatchMethod.ORDER),
            ),
        ),
        pipeline_steps=original.pipeline_steps,
    )
    document = PipelineDocumentCodec.from_source(PipelineDocumentCodec.render(document))
    bundle = _compile(tmp_path, document, GlobalPipelineConfig(num_workers=1, use_threading=True))
    context = bundle.runtime_contexts["A01"]
    executor = FunctionStepExecutor(context, 2)
    prepared = executor._prepare_groups(executor._detect_patterns())
    expected_keys = (None,) if producer_group_by is Ungrouped else ("1", "2")
    assert context.step_plans[2].execution_group_scope.keys == expected_keys
    assert tuple(prepared) == expected_keys
    assert all(len(patterns) == 1 for patterns in prepared.values())
    invocation = next(executor.plan.compiled_function_pattern.iter_invocations())
    assert tuple(
        spec.name for spec in invocation.contract.artifact_inputs.of_artifact_type(ImageArtifactType)
    ) == ("DNA", "Actin")
    results = _execute(tmp_path, document, bundle)
    assert results["A01"].is_success(), results["A01"].error_message
    (output,) = invocation.artifact_output_plans
    measurements = context.runtime_value_store.find(
        name=output.name, artifact_type=MeasurementsArtifactType, axis_id="A01",
    )
    assert len(measurements) == len(expected_keys)
    assert tuple(record.key.scope.value_text for record in measurements) == expected_keys
    for object_name in ("Nuclei", "Cells"):
        (labels,) = context.runtime_value_store.find(name=object_name, axis_id="A01")
        area = np.count_nonzero(object_label_dense_array(labels.data))
        for image_name, integrated in (("DNA", 4.0), ("Actin", float(area))):
            expected_features = {
                "IntegratedIntensity": integrated,
                "MeanIntensity": integrated / area,
                "MinIntensity": 1.0 if integrated == area else 0.0,
                "MaxIntensity": 1.0,
            }
            for feature, expected in expected_features.items():
                values = measurement_values_for_feature(
                    tuple(measurement.data for measurement in measurements),
                    f"Intensity_{feature}_{image_name}",
                    object_count=1,
                    object_name=object_name,
                    dialect=CELLPROFILER_MEASUREMENT_LOOKUP_DIALECT,
                )
                assert tuple(values) == pytest.approx((expected,))


def test_omitted_selector_remains_valid_for_one_label_producer(tmp_path):
    _write_plate(tmp_path)
    bundle = _compile(
        tmp_path,
        _document(selected=False, two_producers=False),
        GlobalPipelineConfig(num_workers=1, use_threading=True),
    )
    invocation = next(
        bundle.runtime_contexts["A01"].step_plans[1].compiled_function_pattern.iter_invocations()
    )
    (edge,) = (
        edge for edge in invocation.artifact_input_edges
        if edge.spec.artifact_type is ObjectLabelsArtifactType
    )
    assert edge.spec.name == "Nuclei"


@pytest.mark.parametrize("valid", [False, True])
def test_headless_entrypoint_requires_subject_and_executes_corrected_rows(
    tmp_path, valid, registered_count_callable,
):
    _write_plate(tmp_path)
    document = PipelineDocumentCodec.from_values(
        pipeline_config=PipelineConfig(
            dataset_source=SourceBindingsSource,
            source_bindings_config=LazySourceBindingsConfig(
                bindings=(_source("DNA", "1"),),
            ),
        ),
        pipeline_steps=[_step(
            registered_count_callable,
            "Count pixels", {},
        )],
    )
    document = PipelineDocumentCodec.from_source(
        PipelineDocumentCodec.render(document)
    )
    invocation = next(
        normalize_function_pattern(document.pipeline_steps[0].func).iter_items()
    )
    [rows] = (
        spec for spec in invocation.contract.artifact_specs.specs
        if spec.artifact_type is MeasurementsArtifactType
    )
    assert rows.measurement_feature_owner is CountFeatureOwner
    source_input = _source("DNA", "1").input_spec()
    binding = MainFlowArtifactContractProvider()(
        invocation,
        ArtifactDeclarationStepContext(
            main_flow_artifacts=ArtifactSpecCollection((source_input,)),
        ),
    )
    assert binding is not None
    assert binding.contract.group_scope_inputs.specs == (source_input,)
    bound_rows = binding.contract.artifact_outputs.by_ref(rows.ref())
    assert bound_rows is not None
    assert bound_rows.source_stack_scope_sources() == (source_input.ref(),)
    assert binding.contract.output_group_scope_sources == (source_input.ref(),)
    assert (
        ImageMeasurementSubjectRelation(COUNT_IMAGE.ref()) in bound_rows.relations
    ) is valid
    global_config = GlobalPipelineConfig(num_workers=1, use_threading=True)
    if not valid:
        with pytest.raises(ValueError, match="PixelCounts.*no declared measurement subject") as exc:
            _compile(tmp_path, document, global_config)
        assert "ImageMeasurementSubjectRelation" in str(exc.value)
        return
    bundle = _compile(tmp_path, document, global_config)
    results = _execute(tmp_path, document, bundle)
    assert results["A01"].is_success(), results["A01"].error_message
    store = bundle.runtime_contexts["A01"].runtime_value_store
    [counts] = store.find(name="PixelCounts", axis_id="A01")
    [image] = store.find(name="CountedImage", axis_id="A01")
    assert image.key.artifact_type is ImageArtifactType
    assert counts.data.subject.source_image_name == "CountedImage"
    assert tuple(counts.data.rows.column_values("pixel_count")) == (4,)
    step_plan = bundle.runtime_contexts["A01"].step_plans[0]
    [csv_path] = step_plan.artifact_analysis_output_dir.glob(
        f"*_{counts.key.name}_step{step_plan.step_index}_details.csv"
    )
    with csv_path.open(newline="") as stream:
        [persisted] = DictReader(stream)
    assert persisted["pixel_count"] == "4"
    assert persisted["source_image_name"] == counts.data.subject.source_image_name
