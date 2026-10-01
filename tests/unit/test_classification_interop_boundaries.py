"""Real declaration-to-runtime regressions for classification authoring."""

from __future__ import annotations

import inspect
from dataclasses import dataclass, replace

import numpy as np
import pytest

from openhcs.constants.constants import Backend
from openhcs.core.artifacts import (
    ArtifactInputPlan,
    ArtifactOutputPlan,
    ArtifactSpec,
    ArtifactSpecCollection,
    GroupLineageSourceRelation,
    ImageArtifactType,
    MeasurementsArtifactType,
    ObjectLabelsArtifactType,
    ObjectMeasurementSubjectRelation,
    SourceStackLineageSourceRelation,
)
from openhcs.core.callable_contract import CallableContract
from openhcs.core.component_group_scope import (
    ComponentGroupScope,
    RuntimeExecutionAxisScope,
)
from openhcs.core.function_patterns import DEFAULT_GROUP_KEY, FunctionInvocationKey
from openhcs.core.invocation_artifacts import ArtifactDeclarationStepContext
from openhcs.core.measurement_row_materialization import (
    DataclassMeasurementColumnarRows,
)
from openhcs.core.pipeline.artifact_planning import artifact_producers_for_outputs
from openhcs.core.pipeline.function_contracts import (
    runtime_bound_parameters,
    special_inputs,
)
from openhcs.core.runtime_artifact_values import RuntimeValue
from openhcs.core.runtime_image_values import image_payload_data
from openhcs.core.runtime_measurements import (
    MeasurementScope,
    MeasurementSubject,
    MeasurementTable,
    RuntimeMeasurementFeature,
    RuntimeMeasurementFeatureOwner,
)
from openhcs.core.runtime_object_labels import ObjectLabelSet
from openhcs.core.runtime_plane_projection import RuntimePlaneProjection
from openhcs.core.runtime_stores import RuntimeValueStore
from openhcs.interop.cellprofiler.module_artifact_declarations import (
    PriorMeasurementArtifactInputModule,
)
from openhcs.interop.cellprofiler.parser import ModuleBlock, ModuleSetting
from openhcs.interop.cellprofiler.runtime.artifact_binding import (
    RuntimeInputBindingRequest,
)
from openhcs.interop.cellprofiler.setting_names import SettingNameFamily
from openhcs.interop.cellprofiler.settings_binder import (
    MeasurementFeatureSettingBinding,
    SettingToKeywordBinding,
)
from openhcs.processing.backends.cellprofiler.classification import (
    ClassificationBinChoice,
    ClassifiedImageSourceRelation,
    ClassifyObjectsSingleMeasurementModule,
    _ClassificationMeasurementVectorRuntimeParameter,
    _SingleClassifiedImageOutputRuntimeBinding,
    classification_rgb_image,
    classify_objects_single_measurement,
    classify_objects_two_measurements,
)
from tests.unit.cellprofiler_runtime_test_support import (
    cellprofiler_runtime_adapter_for_test,
    cellprofiler_runtime_input_edge_for_test,
)
from tests.unit.test_cellprofiler_conditional_analysis_images import (
    _classification_context,
    _contract,
    _module_block,
    _object_payload,
    _public_function_step_contract,
)


@dataclass(frozen=True)
class _AreaRow:
    object_label: int
    AreaShape_Area: float


def _runtime_request(contract, kwargs, table=None):
    """Load real compiled inputs through the original store and runtime adapter."""
    store = RuntimeValueStore()
    edges = {}
    labels = _object_payload()
    objects = ObjectLabelSet(
        name="Cells", variant_data=labels.variant_data, domain=labels.domain
    )
    if table is None:
        table = MeasurementTable(
            name="MeasureObjectSizeShape_1_measurements",
            rows=DataclassMeasurementColumnarRows(
                (_AreaRow(1, 9.0), _AreaRow(2, 300.0))
            ),
            subject=MeasurementSubject(
                MeasurementScope.OBJECT, "Cells", "object_label"
            ),
        )
    payloads = {objects.name: objects, table.name: table}
    for index, spec in enumerate(contract.artifact_inputs):
        path = f"/memory/{spec.name}"
        plan = ArtifactInputPlan(spec.name, path, artifact_type=spec.artifact_type)
        edge = cellprofiler_runtime_input_edge_for_test(
            plan,
            spec=spec,
            input_index=index,
            invocation_scope=ComponentGroupScope.ungrouped(),
            producer_selection_scope=ComponentGroupScope.ungrouped(),
            component_scopes=(),
            consumer_variable_components=(),
        )
        edges[edge.key] = edge
        output = ArtifactOutputPlan(spec.name, path, artifact_type=spec.artifact_type)
        store.replace(
            RuntimeValue.normalize(output, payloads[spec.name], axis_id="A01"),
            path=path,
            backend=Backend.MEMORY.value,
        )
    return RuntimeInputBindingRequest(
        adapter=cellprofiler_runtime_adapter_for_test(
            runtime_value_store=store,
            callable_contract=contract,
            artifact_inputs=edges,
            axis_scope=RuntimeExecutionAxisScope.from_raw(
                "A01", component=None, value=None
            ),
            plane_projection=RuntimePlaneProjection.selected(0, 1),
        ),
        kwargs=kwargs,
        current_image=np.zeros((8, 8), dtype=np.float32),
    )


def _scalar_kwargs():
    return dict(
        select_the_object_to_be_classified="Cells",
        measurement_feature="AreaShape_Area",
        bin_choice=ClassificationBinChoice.EVEN,
        bin_count=2,
        low_threshold=0.0,
        high_threshold=512.0,
        bin_names=("Small", "Large"),
        retained_image_name="engineering_class_rgb",
    )


def test_scalar_retained_image_survives_compilation_and_real_runtime_binding():
    authored = _scalar_kwargs()
    contract = _public_function_step_contract(
        ClassifyObjectsSingleMeasurementModule,
        classify_objects_single_measurement,
        authored,
        _classification_context(),
    )
    # These selectors are consumed by compilation, not supplied again at runtime.
    kwargs = {
        key: value
        for key, value in authored.items()
        if key not in ("select_the_object_to_be_classified", "retained_image_name")
    }
    request = _runtime_request(contract, kwargs)
    bound = ClassifyObjectsSingleMeasurementModule.bind_runtime_inputs(request)
    assert bound["classified_image_rule_indices"] == (0,)
    output, rows = inspect.unwrap(classify_objects_single_measurement)(
        request.current_image, **kwargs, **bound
    )
    assert bound["retained_image_name"] == "engineering_class_rgb"
    assert image_payload_data(output).shape == (8, 8, 3)
    assert (
        len(rows) == 1
    )  # Original ClassificationResult owns one aggregate row per rule.
    assert rows.rows[0].total_objects == 2
    np.testing.assert_array_equal(
        image_payload_data(output),
        classification_rgb_image(_object_payload().variant_data.labels),
    )
    np.testing.assert_array_equal(bound["measurement_values"], (9.0, 300.0))


def test_scalar_runtime_keeps_strict_declared_output_check():
    with pytest.raises(ValueError, match="declared image outputs do not match"):
        inspect.unwrap(classify_objects_single_measurement)(
            np.zeros((8, 8)),
            _object_payload(),
            measurement_values=np.array((9.0, 300.0)),
            retained_image_name=None,
            classified_image_rule_indices=(0,),
        )


class _IndependentFeature(RuntimeMeasurementFeature):
    PIXEL_COUNT = "pixel_count"


class _IndependentFeatureOwner(RuntimeMeasurementFeatureOwner):
    @classmethod
    def owns_measurement_feature_name(cls, feature_name):
        return any(
            member.feature_name == feature_name for member in _IndependentFeature
        )

    @classmethod
    def owns_primary_measurement_feature_name(cls, feature_name):
        return cls.owns_measurement_feature_name(feature_name)


class _IndependentPriorConsumerModule(PriorMeasurementArtifactInputModule):
    module_name = "ClassificationInteropPriorProbe"
    function_name = "classification_interop_prior_probe"
    feature_binding = MeasurementFeatureSettingBinding(
        SettingNameFamily("Choose probe feature"), "probe_feature"
    )


def _producer_context(*outputs):
    return ArtifactDeclarationStepContext(
        step_name="classification_interop",
        step_index=1,
        available_artifacts=ArtifactSpecCollection(outputs),
        main_flow_artifacts=ArtifactSpecCollection(()),
        available_artifact_producers=artifact_producers_for_outputs(
            outputs,
            groups=(None,),
            invocation_keys=(
                FunctionInvocationKey("independent_producer", DEFAULT_GROUP_KEY, 0),
            ),
        ),
    )


def _feature_probe_module(feature="pixel_count"):
    return ModuleBlock(
        name=_IndependentPriorConsumerModule.module_name,
        module_num=1,
        setting_records=[ModuleSetting("Choose probe feature", feature)],
    )


@pytest.mark.parametrize("subject_role", (ArtifactInputPlan, ArtifactOutputPlan))
def test_independent_custom_producer_and_consumer_resolve_both_reference_roles(
    subject_role,
):
    labels = ArtifactSpec.output("Cells", ObjectLabelsArtifactType)
    rows = ArtifactSpec.output(
        "IndependentRows",
        MeasurementsArtifactType,
        relations=(
            ObjectMeasurementSubjectRelation(
                labels.for_plan_type(subject_role).ref(), id_field="object_label"
            ),
        ),
        measurement_feature_owner=_IndependentFeatureOwner,
    )
    assert _IndependentPriorConsumerModule.prior_measurement_feature_names(
        _feature_probe_module()
    ) == ("pixel_count",)
    (selected,) = _IndependentPriorConsumerModule.prior_measurement_artifact_inputs(
        _feature_probe_module(),
        step_context=_producer_context(labels, rows),
        direct_inputs=ArtifactSpecCollection(
            (labels.for_plan_type(ArtifactInputPlan),)
        ),
    )
    assert selected.ref() == rows.for_plan_type(ArtifactInputPlan).ref()
    assert (
        rows.relations[0].source.plan_type is subject_role
    )  # The producer declaration is NOT rewritten.


@dataclass(frozen=True)
class _IndependentPixelRow:
    object_label: int
    pixel_count: int


def test_independent_custom_feature_compiles_and_binds_real_rows_to_original_scalar_callable():
    labels = ArtifactSpec.output("Cells", ObjectLabelsArtifactType)
    rows = ArtifactSpec.output(
        "IndependentRows",
        MeasurementsArtifactType,
        relations=(
            ObjectMeasurementSubjectRelation(labels.ref(), id_field="object_label"),
        ),
        measurement_feature_owner=_IndependentFeatureOwner,
    )
    context = _producer_context(labels, rows)
    authored = {**_scalar_kwargs(), "measurement_feature": "pixel_count"}
    contract = _public_function_step_contract(
        ClassifyObjectsSingleMeasurementModule,
        classify_objects_single_measurement,
        authored,
        context,
    )
    assert (
        contract.artifact_inputs.by_ref(rows.for_plan_type(ArtifactInputPlan).ref())
        is not None
    )
    table = MeasurementTable(
        name=rows.name,
        rows=DataclassMeasurementColumnarRows(
            (_IndependentPixelRow(1, 9), _IndependentPixelRow(2, 300))
        ),
        subject=MeasurementSubject(
            MeasurementScope.OBJECT, labels.name, "object_label"
        ),
        measurement_feature_owner=_IndependentFeatureOwner,
    )
    kwargs = {
        key: value
        for key, value in authored.items()
        if key not in ("select_the_object_to_be_classified", "retained_image_name")
    }
    request = _runtime_request(contract, kwargs, table)
    bound = ClassifyObjectsSingleMeasurementModule.bind_runtime_inputs(request)
    image, result = inspect.unwrap(classify_objects_single_measurement)(
        request.current_image, **kwargs, **bound
    )
    np.testing.assert_array_equal(bound["measurement_values"], (9, 300))
    np.testing.assert_array_equal(
        image_payload_data(image),
        classification_rgb_image(_object_payload().variant_data.labels),
    )
    assert result.rows[0].total_objects == 2


@pytest.mark.parametrize("subject_count", (1, 2))
def test_projected_prior_group_lineage_retains_exact_source_and_rejects_ambiguity(
    subject_count,
):
    objects = tuple(
        ArtifactSpec.output(name, ObjectLabelsArtifactType)
        for name in ("Cells", "OtherCells")
    )[:subject_count]
    rows = ArtifactSpec.output(
        "IndependentRows",
        MeasurementsArtifactType,
        relations=(
            ObjectMeasurementSubjectRelation(objects[0].ref(), id_field="object_label"),
            *(GroupLineageSourceRelation(obj.ref()) for obj in objects),
        ),
        measurement_feature_owner=_IndependentFeatureOwner,
    )
    inputs = ArtifactSpecCollection(
        tuple(obj.for_plan_type(ArtifactInputPlan) for obj in objects)
    )
    if subject_count == 2:
        with pytest.raises(ValueError, match="multiple group-lineage sources"):
            _IndependentPriorConsumerModule.prior_measurement_artifact_inputs(
                _feature_probe_module(),
                step_context=_producer_context(*objects, rows),
                direct_inputs=inputs,
            )
    else:
        (selected,) = _IndependentPriorConsumerModule.prior_measurement_artifact_inputs(
            _feature_probe_module(),
            step_context=_producer_context(*objects, rows),
            direct_inputs=inputs,
        )
        assert selected.group_scope_sources() == (
            objects[0].for_plan_type(ArtifactInputPlan).ref(),
        )


@pytest.mark.parametrize(
    "defect",
    (
        "unknown_feature",
        "wrong_object",
        "missing_subject",
        "missing_owner",
        "wrong_payload",
    ),
)
def test_custom_feature_selection_keeps_declared_owner_subject_and_payload_negatives(
    defect,
):
    labels = ArtifactSpec.output("Cells", ObjectLabelsArtifactType)
    subject = (
        ArtifactSpec.output("OtherCells", ObjectLabelsArtifactType)
        if defect == "wrong_object"
        else labels
    )
    rows = (
        ArtifactSpec.output(
            "IndependentRows",
            ImageArtifactType
            if defect == "wrong_payload"
            else MeasurementsArtifactType,
            relations=()
            if defect == "missing_subject"
            else (
                ObjectMeasurementSubjectRelation(
                    subject.ref(), id_field="object_label"
                ),
            ),
            measurement_feature_owner=None
            if defect in ("missing_owner", "wrong_payload")
            else _IndependentFeatureOwner,
        )
        if defect != "wrong_payload"
        else ArtifactSpec.output("IndependentRows", ImageArtifactType)
    )
    with pytest.raises(ValueError, match="cannot resolve prior measurement feature"):
        _IndependentPriorConsumerModule.prior_measurement_artifact_inputs(
            _feature_probe_module(
                "unknown" if defect == "unknown_feature" else "pixel_count"
            ),
            step_context=_producer_context(labels, rows),
            direct_inputs=ArtifactSpecCollection(
                (labels.for_plan_type(ArtifactInputPlan),)
            ),
        )


def test_projected_lineage_preserves_both_object_and_source_constraints():
    labels = ArtifactSpec.output("Cells", ObjectLabelsArtifactType)
    image = ArtifactSpec.output("DNA", ImageArtifactType)
    rows = ArtifactSpec.output(
        "IndependentRows",
        MeasurementsArtifactType,
        relations=(
            ObjectMeasurementSubjectRelation(labels.ref(), id_field="object_label"),
            SourceStackLineageSourceRelation(image.ref()),
        ),
        measurement_feature_owner=_IndependentFeatureOwner,
    )
    object_refs = frozenset((labels.for_plan_type(ArtifactInputPlan).ref(),))
    source_refs = frozenset((image.for_plan_type(ArtifactInputPlan).ref(),))
    assert _IndependentPriorConsumerModule.prior_measurement_matches_lineage(
        rows, object_refs=object_refs, source_refs=source_refs
    )
    wrong = frozenset((ArtifactSpec.input("FITC", ImageArtifactType).ref(),))
    assert not _IndependentPriorConsumerModule.prior_measurement_matches_lineage(
        rows, object_refs=object_refs, source_refs=wrong
    )
    wrong_type = frozenset((ArtifactSpec.input("Cells", ImageArtifactType).ref(),))
    assert not _IndependentPriorConsumerModule.prior_measurement_matches_lineage(
        rows, object_refs=wrong_type, source_refs=source_refs
    )


class _IndependentVectorRuntimeParameter(
    _SingleClassifiedImageOutputRuntimeBinding,
    _ClassificationMeasurementVectorRuntimeParameter,
):
    parameter_name = "independent_values"
    feature_binding = MeasurementFeatureSettingBinding(
        SettingNameFamily("Independent feature"), "independent_feature"
    )
    output_binding = SettingToKeywordBinding.output(
        SettingNameFamily("Independent image"),
        ImageArtifactType,
        "independent_image_name",
    )

    @classmethod
    def measurement_feature_binding(cls):
        return cls.feature_binding

    @classmethod
    def classified_image_output_binding(cls):
        return cls.output_binding


def test_new_runtime_declaration_is_discovered_and_cooperatively_binds_vector_and_output():
    compiled = _public_function_step_contract(
        ClassifyObjectsSingleMeasurementModule,
        classify_objects_single_measurement,
        _scalar_kwargs(),
        _classification_context(),
    )
    declared = CallableContract.from_callable(_independent_runtime_callable)
    contract = replace(
        declared,
        module_name=compiled.module_name,
        metadata=replace(
            declared.metadata,
            artifact_inputs=compiled.metadata.artifact_inputs,
            artifact_outputs=compiled.metadata.artifact_outputs,
        ),
    )
    bound = ClassifyObjectsSingleMeasurementModule.bind_runtime_inputs(
        _runtime_request(contract, {"independent_feature": "AreaShape_Area"})
    )
    assert bound["independent_image_name"] == "engineering_class_rgb"
    np.testing.assert_array_equal(bound["independent_values"], (9.0, 300.0))
    assert "measurement_values" not in bound and "retained_image_name" not in bound
    result = _independent_runtime_callable(
        np.zeros((8, 8)), independent_feature="AreaShape_Area", **bound
    )
    assert result[0] == "engineering_class_rgb"
    np.testing.assert_array_equal(result[1], (9.0, 300.0))
    assert _IndependentVectorRuntimeParameter.__mro__.index(
        _SingleClassifiedImageOutputRuntimeBinding
    ) < _IndependentVectorRuntimeParameter.__mro__.index(
        _ClassificationMeasurementVectorRuntimeParameter
    )


@special_inputs("labels")
@runtime_bound_parameters(_IndependentVectorRuntimeParameter)
def _independent_runtime_callable(
    image,
    labels,
    independent_feature="",
    independent_values=None,
    independent_image_name=None,
    classified_image_rule_indices=(),
):
    del image, labels, independent_feature
    assert classified_image_rule_indices == (0,)
    return independent_image_name, independent_values


def test_two_measurement_runtime_has_no_scalar_output_keyword():
    authored = dict(
        select_the_object_to_be_classified="Cells",
        measurement1_feature="AreaShape_Area",
        measurement2_feature="AreaShape_Area",
    )
    # A parsed two-measurement declaration must retain its declared mode.
    module = _module_block(
        ClassifyObjectsSingleMeasurementModule,
        (
            (
                "Make each classification decision on how many measurements?",
                "Two measurements",
            ),
            ("Select the object to be classified", "Cells"),
            ("Select the first measurement", "AreaShape_Area"),
            ("Select the second measurement", "AreaShape_Area"),
            ("Retain an image of the classified objects?", "No"),
        ),
    )
    contract = _contract(
        ClassifyObjectsSingleMeasurementModule,
        module,
        classify_objects_two_measurements,
        _classification_context(),
    )
    bound = ClassifyObjectsSingleMeasurementModule.bind_runtime_inputs(
        _runtime_request(
            contract,
            {
                key: value
                for key, value in authored.items()
                if key != "select_the_object_to_be_classified"
            },
        )
    )
    assert "retained_image_name" not in bound
    np.testing.assert_array_equal(bound["measurement1_values"], (9.0, 300.0))
    np.testing.assert_array_equal(bound["measurement2_values"], (9.0, 300.0))


@pytest.mark.parametrize(
    "defect", ("duplicate_image", "missing_relation", "wrong_rule_index")
)
def test_scalar_output_binding_rejects_inconsistent_compiled_declarations(defect):
    authored = _scalar_kwargs()
    contract = _public_function_step_contract(
        ClassifyObjectsSingleMeasurementModule,
        classify_objects_single_measurement,
        authored,
        _classification_context(),
    )
    images = contract.artifact_outputs.of_artifact_type(ImageArtifactType)
    image = images[0]
    outputs = tuple(
        output for output in contract.artifact_outputs if output not in images
    )
    if defect == "duplicate_image":
        outputs += (image, replace(image, name="AnotherClassified"))
    elif defect == "missing_relation":
        outputs += (replace(image, relations=()),)
    else:
        relation = next(
            relation
            for relation in image.relations
            if isinstance(relation, ClassifiedImageSourceRelation)
        )
        outputs += (replace(image, relations=(replace(relation, rule_index=1),)),)
    contract = replace(
        contract, metadata=replace(contract.metadata, artifact_outputs=outputs)
    )
    kwargs = {
        key: value
        for key, value in authored.items()
        if key not in ("select_the_object_to_be_classified", "retained_image_name")
    }
    request = _runtime_request(contract, kwargs)
    with pytest.raises(
        ValueError, match="at most one|one exact|declared image outputs do not match"
    ):
        bound = ClassifyObjectsSingleMeasurementModule.bind_runtime_inputs(request)
        inspect.unwrap(classify_objects_single_measurement)(
            request.current_image, **kwargs, **bound
        )
