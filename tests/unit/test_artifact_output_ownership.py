"""Compile invariants apply independently of artifact recording ownership."""

from dataclasses import replace
from types import SimpleNamespace

import pytest

from openhcs.core.artifacts import (
    ArtifactSpec,
    ArtifactType,
    ArtifactMeasurementSubjectRelation,
    ImageArtifactType,
    ImageMeasurementSubjectRelation,
    MeasurementsArtifactType,
    ObjectLabelsArtifactType,
    ObjectMeasurementSubjectRelation,
)
from openhcs.core.artifact_key_selection import (
    AdapterRecordedArtifactOutputPolicy,
    ArtifactOutputPolicy,
    NativeReturnArtifactOutputPolicy,
)
from openhcs.core.callable_contract import CallableContract
from openhcs.core.function_patterns import (
    compile_function_pattern,
    normalize_function_pattern,
)
from openhcs.core.pipeline.function_contracts import artifact_inputs, artifact_outputs
from openhcs.core.runtime_adapters import RuntimeAdapterSpec, runtime_adapter
from openhcs.interop.cellprofiler.runtime.adapter import (
    CellProfilerRecordedArtifactOutputPolicy,
)
from openhcs.processing.materialization import CsvOptions, MaterializationSpec


@pytest.mark.parametrize("invalid_policy", [None, False, ArtifactOutputPolicy])
def test_adapter_declaration_requires_a_concrete_output_policy(invalid_policy):
    with pytest.raises(TypeError, match="concrete ArtifactOutputPolicy declaration"):
        RuntimeAdapterSpec(
            "runtime",
            lambda request: object(),
            artifact_output_policy=invalid_policy,
        )


@pytest.fixture
def materialized_output_kind(monkeypatch):
    # Isolate the declaration, not the compiler or its registration mechanism.
    monkeypatch.setattr(ArtifactType, "__registry__", dict(ArtifactType.__registry__))

    class MaterializedAuditArtifactType(ArtifactType):
        value = "materialized_output_policy_audit"

        @classmethod
        def validate_output_declaration(cls, spec):
            if spec.materialization is None:
                raise ValueError("Audit output requires declared materialization")

    return MaterializedAuditArtifactType


@pytest.mark.parametrize("boundary", ["contract", "compile"])
@pytest.mark.parametrize(
    "output_policy",
    [
        NativeReturnArtifactOutputPolicy,
        AdapterRecordedArtifactOutputPolicy,
        CellProfilerRecordedArtifactOutputPolicy,
    ],
    ids=["native", "recorded", "cellprofiler-recorded"],
)
@pytest.mark.parametrize(
    "manages_inputs", [False, True], ids=["native-inputs", "adapter-inputs"]
)
def test_new_output_kind_invariant_is_not_exempted_by_recording_owner(
    materialized_output_kind,
    boundary,
    output_policy,
    manages_inputs,
):
    spec = ArtifactSpec.output("Audit", materialized_output_kind)

    def declared(output):
        @runtime_adapter(
            "runtime",
            lambda request: object(),
            manages_artifact_inputs=manages_inputs,
            artifact_output_policy=output_policy,
        )
        @artifact_outputs(output)
        def publish(image, *, runtime):
            raise AssertionError("Compile validation must not execute a callable")

        return publish

    def validate(func):
        if boundary == "contract":
            CallableContract.from_callable(func).validate_artifact_output_declarations()
        else:
            compile_function_pattern(func, {}, {})

    with pytest.raises(ValueError, match="requires declared materialization"):
        validate(declared(spec))
    validate(declared(replace(spec, materialization=MaterializationSpec(CsvOptions()))))


@pytest.mark.parametrize(
    "output_policy",
    [
        NativeReturnArtifactOutputPolicy,
        AdapterRecordedArtifactOutputPolicy,
    ],
)
def test_single_subject_output_policy_rejects_missing_measurement_subject(
    output_policy,
):
    @runtime_adapter(
        "runtime", lambda request: object(), artifact_output_policy=output_policy
    )
    @artifact_outputs(ArtifactSpec.output("Counts", MeasurementsArtifactType))
    def count(image, *, runtime):
        raise AssertionError("Invalid declarations must not execute")

    with pytest.raises(ValueError, match="no declared measurement subject"):
        compile_function_pattern(count, {}, {})


@pytest.mark.parametrize(
    "output_policy",
    [
        NativeReturnArtifactOutputPolicy,
        AdapterRecordedArtifactOutputPolicy,
        CellProfilerRecordedArtifactOutputPolicy,
    ],
)
def test_scalar_input_ambiguity_precedes_dependent_output_subject_validation(
    output_policy,
):
    inputs = tuple(
        ArtifactSpec.input(name, ObjectLabelsArtifactType, parameter_name="labels")
        for name in ("Nuclei", "Cells")
    )
    rows = ArtifactSpec.output(
        "Measurements",
        MeasurementsArtifactType,
        relations=tuple(ObjectMeasurementSubjectRelation(spec.ref()) for spec in inputs),
    )

    @runtime_adapter(
        "runtime", lambda request: object(), artifact_output_policy=output_policy
    )
    @artifact_inputs(*inputs)
    @artifact_outputs(rows)
    def measure(image, labels=None, *, runtime):
        raise AssertionError("Invalid declarations must not execute")

    with pytest.raises(ValueError, match="labels.*multiple exact artifact occurrences"):
        compile_function_pattern(measure, {}, {})

    # Output obligations remain mandatory once input selection is unambiguous.
    with pytest.raises(ValueError, match="multiple measurement subjects"):
        CallableContract.from_callable(measure).validate_artifact_output_declarations()


def test_cellprofiler_recording_policy_still_rejects_conflicting_explicit_subjects():
    image = ArtifactSpec.output("Image", ImageArtifactType)
    measurements = ArtifactSpec.output(
        "Measurements",
        MeasurementsArtifactType,
        relations=(
            ImageMeasurementSubjectRelation(image.ref()),
            ArtifactMeasurementSubjectRelation(),
        ),
    )

    @runtime_adapter(
        "runtime",
        lambda request: object(),
        artifact_output_policy=CellProfilerRecordedArtifactOutputPolicy,
    )
    @artifact_outputs(image, measurements)
    def count(image, *, runtime):
        raise AssertionError("Invalid declarations must not execute")

    with pytest.raises(ValueError, match="multiple measurement subjects"):
        compile_function_pattern(count, {}, {})


def test_cellprofiler_recording_requires_its_declared_measurement_row_owner():
    @runtime_adapter(
        "runtime",
        lambda request: object(),
        artifact_output_policy=CellProfilerRecordedArtifactOutputPolicy,
    )
    @artifact_outputs(ArtifactSpec.output("Measurements", MeasurementsArtifactType))
    def measure(image, *, runtime):
        raise AssertionError("Invalid declarations must not execute")

    with pytest.raises(ValueError, match="declared measurement_feature_owner"):
        compile_function_pattern(measure, {}, {})


def test_real_cellprofiler_declaration_compiles_without_a_table_wide_subject():
    """The real module/provider declares the owner, not a compiler exemption."""
    from openhcs.core.compiled_step_plan import CompiledStepPlan
    from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
    from openhcs.core.context.processing_context import ProcessingContext
    from openhcs.core.invocation_artifacts import ArtifactDeclarationStepContext
    from openhcs.core.pipeline.compilation_session import CompilationSession
    from openhcs.core.pipeline.step_snapshot import StepSnapshot
    from openhcs.core.source_bindings import (
        NamedSourceBinding,
        StepSourceBindingsConfig,
    )
    from openhcs.core.steps.function_step import FunctionStep
    from openhcs.interop.cellprofiler.compile_time_contracts import (
        CellProfilerInvocationContractProviderFactory,
    )
    from openhcs.processing.backends.cellprofiler.primary_objects import (
        IdentifyPrimaryObjectsModule,
        identify_primary_objects,
    )
    from openhcs.core.artifacts import (
        ArtifactInputPlan,
        ArtifactOutputPlan,
        ArtifactSpecRelation,
        ObjectLabelsArtifactType,
    )

    (input_binding,) = IdentifyPrimaryObjectsModule.declared_artifact_bindings(
        plan_type=ArtifactInputPlan,
        artifact_type=ImageArtifactType,
    )
    (output_binding,) = IdentifyPrimaryObjectsModule.declared_artifact_bindings(
        plan_type=ArtifactOutputPlan,
        artifact_type=ObjectLabelsArtifactType,
    )
    step = FunctionStep(
        func=(
            identify_primary_objects,
            {
                input_binding.require_parameter_name(): "DNA",
                output_binding.require_parameter_name(): "Nuclei",
            },
        ),
        name="Primary",
        source_bindings=StepSourceBindingsConfig(
            enabled=True,
            bindings=(NamedSourceBinding(alias="DNA"),),
        ),
    )
    session = CompilationSession.from_context(
        context=ProcessingContext(
            axis_id="A01",
            step_plans={
                0: CompiledStepPlan(
                    step_index=0,
                    step_name=step.name,
                    step_type="FunctionStep",
                    axis_id="A01",
                ),
            },
        ),
        steps=[step],
        orchestrator=SimpleNamespace(pipeline_config=PipelineConfig()),
        global_config=GlobalPipelineConfig(),
        step_state_map={0: object()},
        snapshots=(StepSnapshot(index=0, scope_id="test::cp-output-owner", step=step),),
    )
    provider = CellProfilerInvocationContractProviderFactory.provider_for_session(
        session
    )
    authored = next(normalize_function_pattern(step.func).iter_items())
    contract = provider.plans[(0, authored.key)].contract
    assert contract.artifact_output_policy is CellProfilerRecordedArtifactOutputPolicy
    (measurement,) = contract.artifact_outputs.of_artifact_type(
        MeasurementsArtifactType
    )
    assert measurement.measurement_feature_owner is IdentifyPrimaryObjectsModule
    assert ArtifactSpecRelation.measurement_subject_for_output(measurement) is None

    compiled = compile_function_pattern(
        step.func,
        {},
        {},
        invocation_contract_provider=provider,
        step_context=ArtifactDeclarationStepContext(
            step_index=0, source_bindings=step.source_bindings
        ),
    )
    assert compiled.default_group.invocations[0].contract is contract

    # The same declaration is not valid under the native return carrier's
    # single-subject obligation. Only that obligation differs between owners.
    native = replace(
        contract, metadata=replace(contract.metadata, runtime_adapter=None)
    )
    with pytest.raises(ValueError, match="no declared measurement subject"):
        native.validate_artifact_output_declarations()
