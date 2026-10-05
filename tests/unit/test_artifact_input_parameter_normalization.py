"""Normalization of artifact-fed callable parameter declarations."""

from dataclasses import dataclass, replace

import pytest

from openhcs.core.artifacts import ArtifactSpec, ObjectLabelsArtifactType, SpecialArtifactType
from openhcs.core.callable_contract import CallableContract
from openhcs.core.function_patterns import compile_function_pattern
from openhcs.core.invocation_artifacts import (
    InvocationContractPlan,
    InvocationContractProvider,
)
from openhcs.core.runtime_adapters import runtime_adapter
from openhcs.core.pipeline.function_contracts import (
    artifact_inputs,
    special_input_names_from_callable,
    special_inputs,
)


@pytest.mark.parametrize("authored_kwargs", [{}, {"labels": "unbound-value"}])
def test_required_abi_only_parameter_rejects_missing_exact_binding(
    authored_kwargs,
) -> None:
    @special_inputs("labels")
    def consume(image, *, labels):
        del labels
        return image

    contract = CallableContract.from_callable(consume)

    assert contract.artifact_input_parameter_names == ("labels",)
    assert contract.artifact_inputs.names() == ()

    with pytest.raises(
        ValueError, match="'labels' has no exact artifact declaration binding"
    ):
        contract.validate_artifact_input_parameter_bindings()
    with pytest.raises(
        ValueError, match="'labels' has no exact artifact declaration binding"
    ):
        compile_function_pattern((consume, authored_kwargs), {}, {})


def test_optional_abi_only_parameter_keeps_its_declared_default() -> None:
    received = []

    @special_inputs("labels")
    def consume(image, *, labels=None):
        received.append(labels)
        return image

    compiled = compile_function_pattern(consume, {}, {})
    (invocation,) = compiled.default_group.invocations
    assert invocation.contract.artifact_input_parameter_names == ("labels",)
    assert invocation.contract.artifact_inputs.names() == ()
    assert invocation.kwargs_dict == {}
    assert invocation.artifact_input_edges == ()
    image = object()
    assert invocation.func(image) is image
    assert received == [None]


@pytest.mark.parametrize("managed", [False, True])
def test_scalar_artifact_roster_cardinality_belongs_to_its_runtime_binder(managed) -> None:
    inputs = tuple(
        ArtifactSpec.input(name, ObjectLabelsArtifactType, parameter_name="labels")
        for name in ("Nuclei", "Cells")
    )

    @runtime_adapter("runtime", lambda request: object(), manages_artifact_inputs=managed)
    @artifact_inputs(*inputs)
    def consume(image, *, labels, runtime):
        raise AssertionError("Contract admission must not execute the callable")

    if not managed:
        with pytest.raises(ValueError, match="labels.*multiple exact artifact occurrences"):
            compile_function_pattern(consume, {}, {})
        return
    compiled = compile_function_pattern(consume, {}, {})
    (invocation,) = compiled.default_group.invocations
    assert invocation.contract.artifact_inputs.specs == inputs
    assert invocation.contract.artifact_input_parameter_names == ("labels",)


def test_artifact_spec_only_parameter_declaration_compiles() -> None:
    labels = ArtifactSpec.input(
        "StoredLabels",
        SpecialArtifactType,
        parameter_name="labels",
    )

    @artifact_inputs(labels)
    def consume(image, *, labels):
        del labels
        return image

    compiled = compile_function_pattern(consume, {}, {})
    contract = compiled.default_group.invocations[0].contract

    assert contract.artifact_input_parameter_names == ("labels",)
    assert special_input_names_from_callable(consume) == ("labels",)


def test_matching_legacy_and_artifact_spec_declarations_compile() -> None:
    labels = ArtifactSpec.input(
        "StoredLabels",
        SpecialArtifactType,
        parameter_name="labels",
    )

    @artifact_inputs(labels)
    @special_inputs("labels")
    def consume(image, *, labels):
        del labels
        return image

    compiled = compile_function_pattern(consume, {}, {})

    assert compiled.default_group.invocations[
        0
    ].contract.artifact_input_parameter_names == ("labels",)


def test_conflicting_legacy_and_artifact_spec_declarations_fail_compilation() -> None:
    labels = ArtifactSpec.input(
        "StoredLabels",
        SpecialArtifactType,
        parameter_name="labels",
    )

    @artifact_inputs(labels)
    @special_inputs("mask")
    def consume(image, *, labels, mask):
        del labels, mask
        return image

    with pytest.raises(
        ValueError, match="artifact-fed parameter declarations disagree"
    ):
        compile_function_pattern(consume, {}, {})


def test_legacy_declaration_agrees_with_compiled_exact_artifact_binding() -> None:
    @special_inputs("labels")
    def consume(image, *, labels):
        del labels
        return image

    contract = CallableContract.from_callable(consume)
    labels = ArtifactSpec.input(
        "StoredLabels",
        SpecialArtifactType,
        parameter_name="labels",
    )
    compiled_contract = replace(
        contract,
        metadata=replace(contract.metadata, artifact_inputs=(labels,)),
    )

    compiled_contract.validate_artifact_input_parameter_bindings()
    assert compiled_contract.artifact_input_parameter_names == ("labels",)


@dataclass
class _DeclaredInputProvider(InvocationContractProvider):
    inputs: tuple[ArtifactSpec, ...]
    events: list[str]

    def __call__(self, invocation, step_context):
        self.events.append("declare")
        contract = replace(
            invocation.contract,
            metadata=replace(invocation.contract.metadata, artifact_inputs=self.inputs),
        )
        return InvocationContractPlan(contract)


class _ValidateFinalizedInputs:
    def __call__(self, invocation, step_context):
        plan = super().__call__(invocation, step_context)
        plan.contract.validate_artifact_input_parameter_bindings()
        self.events.append("validate")
        return plan


class _RecordFinalizedInputs:
    def __call__(self, invocation, step_context):
        self.events.append("start")
        plan = super().__call__(invocation, step_context)
        self.events.append("ready")
        return plan


class _CheckedInputProvider(
    _RecordFinalizedInputs, _ValidateFinalizedInputs, _DeclaredInputProvider
):
    pass


@pytest.mark.parametrize("artifact_name", ["StoredLabels", "IndependentSeedRegions"])
def test_new_provider_finalizes_exact_input_through_cooperative_hooks(
    artifact_name,
) -> None:
    @special_inputs("labels")
    def consume(image, *, labels):
        del labels
        return image

    labels = ArtifactSpec.input(
        artifact_name, SpecialArtifactType, parameter_name="labels"
    )
    events = []
    provider = _CheckedInputProvider((labels,), events)
    compiled = compile_function_pattern(
        consume, {}, {}, invocation_contract_provider=provider
    )
    (invocation,) = compiled.default_group.invocations
    assert invocation.contract.artifact_input_parameter_names == ("labels",)
    assert invocation.contract.artifact_inputs.specs == (labels,)
    assert CallableContract.from_callable(consume).artifact_inputs.names() == ()
    assert events == ["start", "declare", "validate", "ready"]

    events.clear()
    with pytest.raises(
        ValueError, match="'labels' has no exact artifact declaration binding"
    ):
        compile_function_pattern(
            consume,
            {},
            {},
            invocation_contract_provider=_CheckedInputProvider((), events),
        )
    assert events == ["start", "declare"]
