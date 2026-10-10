"""Artifact graph extraction for compiled function patterns."""

import inspect
from collections import Counter, OrderedDict, defaultdict
from abc import ABC, abstractmethod
from dataclasses import dataclass, field, replace
from typing import Any, ClassVar, Iterable, Mapping, Optional, TYPE_CHECKING

from openhcs.core.artifact_key_selection import ArtifactPlanKeySelector
from openhcs.core.artifacts import (
    ArtifactInputPlan,
    ArtifactMaterializationPayload,
    ArtifactOutputPlan,
    ArtifactSpec,
    ArtifactSpecAccumulator,
    ArtifactSpecCollection,
    ArtifactSpecRef,
    ArtifactType,
    ArtifactTypeStrategyMatchMixin,
    ImageArtifactType,
    MeasurementsArtifactType,
    ObjectLabelsArtifactType,
)
from openhcs.core.function_patterns import DEFAULT_GROUP_KEY
from openhcs.core.function_patterns import FunctionInvocationKey
from openhcs.core.function_patterns import (
    normalize_function_pattern,
    NormalizedFunctionPattern,
    NormalizedFunctionItem,
)
from openhcs.core.invocation_artifacts import (
    ArtifactDeclarationStepContext,
    CompositeInvocationContractProvider,
    InvocationContractProvider,
    InvocationContractPlan,
    unnamed_main_flow_artifact_name,
    InvocationArtifactDeclarationProviderLike,
    callable_contract_artifact_declarations,
)
from openhcs.core.registry_strategies import MostDerivedContextStrategyMixin
from openhcs.processing.materialization import (
    CsvOptions,
    ImageFileOptions,
    MaterializedFilenameIdentity,
    ROIOptions,
    TerminalMaterializationSpec,
)

from openhcs.constants.input_source import InputSource
from openhcs.core.callable_contract import FunctionStepExecutionScope
from openhcs.core.source_bindings import CompiledSourceBindingPlan, StepSourceBindingsConfig
from openhcs.core.step_dependencies import StepInputDependency
from openhcs.core.steps.function_step import FunctionStep

if TYPE_CHECKING:
    from openhcs.core.steps.abstract import AbstractStep

class AutomaticArtifactOutputMaterializationStrategy(
    ArtifactTypeStrategyMatchMixin,
    MostDerivedContextStrategyMixin[type[ArtifactType]],
    ABC,
):
    """Nominal owner of automatic materialization by artifact type."""

    artifact_type: ClassVar[type[ArtifactType] | None] = None

    @abstractmethod
    def materialization(self) -> ArtifactMaterializationPayload:
        """Return the explicit materialization contract for this artifact family."""

    def materializes_consumed_outputs(self) -> bool:
        """Return whether consumed outputs retain automatic materialization."""

        return False


class AutomaticImageArtifactOutputMaterializationStrategy(
    AutomaticArtifactOutputMaterializationStrategy,
):
    """Materialize unconsumed image-family outputs as TIFF files."""

    artifact_type = ImageArtifactType

    def materialization(self) -> ArtifactMaterializationPayload:
        return TerminalMaterializationSpec(ImageFileOptions(filename_suffix=".tif"))


class AutomaticObjectLabelsArtifactOutputMaterializationStrategy(
    AutomaticArtifactOutputMaterializationStrategy,
):
    """Retain and stream object labels through their canonical representations."""

    artifact_type = ObjectLabelsArtifactType

    def materialization(self) -> ArtifactMaterializationPayload:
        return TerminalMaterializationSpec(
            ROIOptions(
                min_area=1,
                filename_identity=MaterializedFilenameIdentity.ARTIFACT_NAME,
            ),
            ImageFileOptions(
                filename_suffix=".labels.tif",
                filename_identity=MaterializedFilenameIdentity.ARTIFACT_NAME,
            ),
        )

    def materializes_consumed_outputs(self) -> bool:
        return True


class AutomaticMeasurementsArtifactOutputMaterializationStrategy(
    AutomaticArtifactOutputMaterializationStrategy,
):
    """Retain terminal measurement tables as artifact-named CSV files."""

    artifact_type = MeasurementsArtifactType

    def materialization(self) -> ArtifactMaterializationPayload:
        return TerminalMaterializationSpec(
            CsvOptions(
                filename_identity=MaterializedFilenameIdentity.ARTIFACT_NAME,
            )
        )


class ArtifactOutputMaterializationPlanner:
    """Promote terminal outputs to explicit nominal materialization contracts."""

    @staticmethod
    def materialization_for(
        spec: ArtifactSpec,
        future_input_refs: Iterable[ArtifactSpecRef],
    ) -> ArtifactMaterializationPayload | None:
        """Preserve explicit contracts and materialize unconsumed nominal outputs."""

        if spec.materialization is not None:
            return spec.materialization
        strategy = AutomaticArtifactOutputMaterializationStrategy.for_context(
            spec.artifact_type,
            required=False,
        )
        if strategy is None:
            return None
        input_ref = spec.ref().for_plan_type(ArtifactInputPlan)
        if (
            input_ref in frozenset(future_input_refs)
            and not strategy.materializes_consumed_outputs()
        ):
            return None
        return strategy.materialization()


@dataclass(frozen=True, slots=True)
class ArtifactProducer:
    """Compiled artifact producer identity and scope."""

    spec: ArtifactSpec
    groups: tuple[Optional[str], ...]
    invocation_keys: tuple[FunctionInvocationKey, ...]
    producer_step_index: int | None = None

    def __post_init__(self) -> None:
        if self.producer_step_index is not None and (
            type(self.producer_step_index) is not int or self.producer_step_index < 0
        ):
            raise ValueError(
                "ArtifactProducer.producer_step_index must be a non-negative "
                "integer or None."
            )

    def has_explicit_invocation_group_ownership(self) -> bool:
        """Return whether grouped pattern dispatch owns this output's groups."""

        return bool(self.invocation_keys) and all(
            key.group_key != DEFAULT_GROUP_KEY for key in self.invocation_keys
        )

    def owns_invocation(self, invocation_key: FunctionInvocationKey) -> bool:
        """Return whether this producer owns the consumer's compile-time group."""

        return invocation_key in self.invocation_keys


def artifact_producers_for_outputs(
    outputs: Iterable[ArtifactSpec],
    *,
    groups: Iterable[Optional[str]],
    invocation_keys: Iterable[FunctionInvocationKey],
) -> tuple[ArtifactProducer, ...]:
    """Bind declared outputs to their exact invocation and group ownership."""

    resolved_groups = ArtifactGraph.unique_preserving_order(groups)
    resolved_invocation_keys = tuple(dict.fromkeys(invocation_keys))
    if not resolved_invocation_keys:
        raise ValueError("Artifact producers require at least one invocation key.")
    return tuple(
        ArtifactProducer(
            spec=spec,
            groups=resolved_groups,
            invocation_keys=resolved_invocation_keys,
        )
        for spec in outputs
    )


@dataclass(frozen=True, slots=True)
class ArtifactConsumer:
    """Compiled artifact consumer identity and declared contract."""

    spec: ArtifactSpec
    invocation_keys: tuple[FunctionInvocationKey, ...]

    @property
    def groups(self) -> tuple[Optional[str], ...]:
        """Return invocation groups that consume this artifact."""

        return ArtifactGraph.unique_preserving_order(
            None if key.group_key == DEFAULT_GROUP_KEY else key.group_key
            for key in self.invocation_keys
        )


@dataclass(frozen=True, slots=True)
class ArtifactGraph:
    """Producer/consumer graph owned by one FunctionStep pattern.

    The graph is the compiler source of truth for artifact names, kinds,
    materialization intent, invocation ownership, and grouped output scope.
    """

    producers: tuple[ArtifactProducer, ...] = ()
    consumers: tuple[ArtifactConsumer, ...] = ()
    non_plan_consumers: tuple[ArtifactConsumer, ...] = ()
    pattern: NormalizedFunctionPattern | None = field(default=None, repr=False)
    invocation_contract_plans: Mapping[
        FunctionInvocationKey, InvocationContractPlan | None
    ] = field(default_factory=dict, repr=False)
    invocation_declarations: Mapping[FunctionInvocationKey, ArtifactPlanKeySelector] = (
        field(default_factory=dict, repr=False)
    )
    main_input_dependency: StepInputDependency = field(
        default_factory=StepInputDependency.unresolved
    )
    source_binding_plan: CompiledSourceBindingPlan = field(
        default_factory=CompiledSourceBindingPlan.empty
    )
    _input_lineage_order: (
        tuple[tuple[ArtifactSpecRef, tuple[ArtifactSpecRef, ...]], ...] | None
    ) = field(default=None, init=False, repr=False, compare=False)

    _config_bound_parameters: tuple[inspect.Parameter, ...] | None = field(
        default=None, init=False, repr=False, compare=False
    )

    def resolve_main_input_dependency(
        self,
        step: "AbstractStep",
        step_index: int,
        *,
        execution_scope: FunctionStepExecutionScope,
        source_bindings: StepSourceBindingsConfig,
        context: ArtifactDeclarationStepContext,
        declared: Mapping[ArtifactSpecRef, ArtifactOutputPlan],
        step_scope_ids: Mapping[int, str],
        previous_dependency: StepInputDependency | None,
        previous_preserves_input_main_flow: bool,
    ) -> StepInputDependency:
        """Resolve fixed topology or a standalone planner's explicit producer facts."""
        if (
            isinstance(step, FunctionStep)
            and execution_scope is FunctionStepExecutionScope.PLATE
        ):
            return StepInputDependency.no_main_flow()

        if (
            step_index == 0
            or step.processing_config.input_source == InputSource.PIPELINE_START
        ):
            return StepInputDependency.pipeline_start()

        local_output_refs = frozenset(
            producer.spec.ref() for producer in self.producers
        )
        main_input_specs = tuple(
            dict.fromkeys(
                consumer.spec
                for consumer in self.non_plan_consumers
                if not source_bindings.declares_artifact_ref(consumer.spec.ref())
                and consumer.spec.ref().for_plan_type(ArtifactOutputPlan)
                not in local_output_refs
            )
        )
        producer_step_indices: list[int | str] = []
        for main_input_spec in main_input_specs:
            producer_ref = main_input_spec.ref().for_plan_type(ArtifactOutputPlan)
            producer_plan = declared.get(producer_ref)
            context_producer = (
                context.available_artifact_producer_for(
                    main_input_spec
                )
            )
            candidate_indices = tuple(
                dict.fromkeys(
                    candidate
                    for candidate in (
                        (
                            None
                            if producer_plan is None
                            else producer_plan.producer_step_index
                        ),
                        (
                            None
                            if context_producer is None
                            else context_producer.producer_step_index
                        ),
                    )
                    if candidate is not None
                )
            )
            if not candidate_indices:
                from openhcs.core.pipeline.path_planner import MissingArtifactInputError

                raise MissingArtifactInputError(
                    step_id=step_index,
                    artifact_key=producer_ref.name,
                    step_name=step.name,
                )
            if len(candidate_indices) > 1:
                raise ValueError(
                    f"Main-flow artifact {producer_ref!r} has conflicting producer "
                    f"steps {candidate_indices!r}."
                )
            producer_step_indices.append(candidate_indices[0])

        producer_step_indices = tuple(dict.fromkeys(producer_step_indices))
        if len(producer_step_indices) > 1:
            raise ValueError(
                f"Step {step.name!r} declares main-flow inputs from multiple "
                f"producer steps {producer_step_indices!r}: {main_input_specs!r}."
            )
        if producer_step_indices:
            producer_index = producer_step_indices[0]
            if not isinstance(producer_index, int):
                raise TypeError(
                    f"Main-flow artifact producer for step {step.name!r} has "
                    f"non-integer step identity {producer_index!r}."
                )
            producer_scope_id = step_scope_ids[producer_index]
            if not producer_scope_id:
                raise ValueError(
                    f"Main-flow artifact producer step {producer_index} has no "
                    "compiled scope identity."
                )
            return StepInputDependency.step_output(
                source_step_index=producer_index,
                source_step_scope_id=producer_scope_id,
            )

        producer_index = step_index - 1
        if previous_preserves_input_main_flow:
            if previous_dependency is None or not previous_dependency.is_resolved:
                raise RuntimeError(
                    f"Main-flow-preserving step {producer_index} has no resolved "
                    "main-input dependency."
                )
            return previous_dependency

        producer_scope_id = step_scope_ids[producer_index]
        return StepInputDependency.step_output(
            source_step_index=producer_index,
            source_step_scope_id=producer_scope_id,
        )

    def with_source_binding_plan(
        self,
        config: StepSourceBindingsConfig,
        dependency: StepInputDependency,
        context: ArtifactDeclarationStepContext,
    ) -> "ArtifactGraph":
        """Capture fixed source routing once per graph."""
        binding_plan = CompiledSourceBindingPlan.from_contracts(
            config,
            () if self.pattern is None else (
                item.contract for item in self.pattern.iter_items()
            ),
            dependency,
            context.available_artifacts,
        )
        return replace(
            self,
            main_input_dependency=dependency,
            source_binding_plan=binding_plan,
        )

    def config_parameters_for_step(
        self, step_name: str
    ) -> tuple[inspect.Parameter, ...]:
        """Admit the shared signature roster before binding axis-local values."""
        if self._config_bound_parameters is None:
            parameters: dict[str, inspect.Parameter] = {}
            for item in () if self.pattern is None else self.pattern.iter_items():
                for parameter in item.contract.config_bound_parameters:
                    prior = parameters.setdefault(parameter.name, parameter)
                    if prior.annotation is not parameter.annotation:
                        raise TypeError(
                            f"FunctionStep {step_name!r} callable pattern "
                            f"declares incompatible config parameter {parameter.name!r}: "
                            f"{prior.annotation!r} and {parameter.annotation!r}."
                        )
            object.__setattr__(
                self, "_config_bound_parameters", tuple(parameters.values())
            )
        return self._config_bound_parameters

    @property
    def input_lineage_order(
        self,
    ) -> tuple[tuple[ArtifactSpecRef, tuple[ArtifactSpecRef, ...]], ...]:
        """Admit output-reachable input topology once, retaining self-lineage leaves."""
        if self._input_lineage_order is not None:
            return self._input_lineage_order
        inputs = self.inputs
        order: list[tuple[ArtifactSpecRef, tuple[ArtifactSpecRef, ...]]] = []
        visited: set[ArtifactSpecRef] = set()
        resolving: set[ArtifactSpecRef] = set()

        def visit(ref: ArtifactSpecRef) -> None:
            if ref in visited:
                return
            if ref in resolving:
                raise ValueError(
                    f"Input group-lineage declarations contain a cycle at {ref!r}."
                )
            resolving.add(ref)
            spec = inputs.get(ref)
            sources = () if spec is None else spec.group_scope_sources()
            for source in sources:
                if source != ref:
                    visit(source)
            resolving.remove(ref)
            visited.add(ref)
            order.append((ref, sources))

        for output in self.outputs.values():
            for ref in output.group_scope_sources():
                visit(ref)
        object.__setattr__(self, "_input_lineage_order", tuple(order))
        return self._input_lineage_order

    def advance_declaration_context(
        self,
        context: ArtifactDeclarationStepContext,
    ) -> ArtifactDeclarationStepContext:
        """Advance plate-fixed named and anonymous flow before axis specialization."""
        producers = tuple(
            replace(producer, producer_step_index=context.step_index)
            for producer in self.producers
        )
        main_flow = context.main_flow_artifacts
        pattern = self.pattern
        if pattern and not all(
            item.contract.preserves_input_main_flow() for item in pattern.iter_items()
        ):
            main_specs: list[ArtifactSpec] = []
            outputs = self.outputs
            for group in pattern.groups:
                named_refs: tuple[ArtifactSpecRef, ...] = ()
                implicit_owner = None
                for item in group.items:
                    selected_refs = frozenset(
                        spec.ref()
                        for spec in self.invocation_declarations[
                            item.key
                        ].artifact_key_specs.for_plan_type(ArtifactOutputPlan)
                    )
                    refs = tuple(
                        spec.ref()
                        for spec in item.contract.canonical_return_output_specs
                        if spec.ref() in selected_refs
                    )
                    if refs:
                        named_refs, implicit_owner = refs, None
                    elif not item.contract.preserves_input_main_flow():
                        named_refs, implicit_owner = (), item
                if named_refs:
                    main_specs.extend(
                        spec.for_plan_type(ArtifactInputPlan)
                        for ref, spec in outputs.items()
                        if ref in named_refs
                    )
                elif implicit_owner is not None:
                    spec = ArtifactSpec.output(
                        unnamed_main_flow_artifact_name(
                            context.step_index, implicit_owner.key
                        ),
                        ImageArtifactType,
                    )
                    producers += (
                        ArtifactProducer(
                            spec=spec,
                            groups=(
                                None
                                if group.group_key == DEFAULT_GROUP_KEY
                                else group.group_key,
                            ),
                            invocation_keys=(implicit_owner.key,),
                            producer_step_index=context.step_index,
                        ),
                    )
                    main_specs.append(spec.for_plan_type(ArtifactInputPlan))
            main_flow = ArtifactSpecCollection(
                ArtifactSpecCollection(main_specs).unique(
                    conflict_context="compiled main flow"
                )
            )
        return context.advance_artifact_graph(
            replace(self, producers=producers),
            main_flow_artifacts=main_flow,
        )

    @classmethod
    def empty(cls) -> "ArtifactGraph":
        return cls()

    @property
    def outputs(self) -> OrderedDict[ArtifactSpecRef, ArtifactSpec]:
        """Produced artifact specs in first declaration order."""
        return OrderedDict(
            (producer.spec.ref(), producer.spec) for producer in self.producers
        )

    def output_storage_keys(self) -> OrderedDict[ArtifactSpecRef, str]:
        """Return collision-safe storage keys for exact output declarations."""

        output_refs = tuple(self.outputs)
        name_counts = Counter(ref.name for ref in output_refs)
        storage_keys = OrderedDict(
            (
                ref,
                (
                    ref.name
                    if name_counts[ref.name] == 1
                    else f"{ref.name}__{ref.artifact_type.require_value()}"
                ),
            )
            for ref in output_refs
        )
        refs_by_storage_key: dict[str, list[ArtifactSpecRef]] = defaultdict(list)
        for ref, storage_key in storage_keys.items():
            refs_by_storage_key[storage_key].append(ref)
        collisions = {
            storage_key: tuple(refs)
            for storage_key, refs in refs_by_storage_key.items()
            if len(refs) > 1
        }
        if collisions:
            raise ValueError(
                "Artifact output declarations produce conflicting storage keys: "
                f"{collisions!r}. Rename the conflicting artifact outputs."
            )
        return storage_keys

    def require_output_storage_key(self, ref: ArtifactSpecRef) -> str:
        """Return the storage key derived for one exact output declaration."""

        storage_key = self.output_storage_keys().get(ref)
        if storage_key is None:
            raise KeyError(f"Artifact graph has no output declaration {ref!r}.")
        return storage_key

    @property
    def output_groups(self) -> dict[ArtifactSpecRef, set[Optional[str]]]:
        """Runtime groups that may produce each exact artifact."""
        groups: dict[ArtifactSpecRef, set[Optional[str]]] = defaultdict(set)
        for producer in self.producers:
            groups[producer.spec.ref()].update(producer.groups)
        return groups

    @property
    def inputs(self) -> OrderedDict[ArtifactSpecRef, ArtifactSpec]:
        """Consumed artifact specs in first declaration order."""
        return OrderedDict(
            (consumer.spec.ref(), consumer.spec) for consumer in self.consumers
        )

    def invocation_keys(self) -> tuple[FunctionInvocationKey, ...]:
        """Return exact invocation identities represented by this graph."""

        return tuple(
            dict.fromkeys(
                key
                for endpoint in (*self.producers, *self.consumers)
                for key in endpoint.invocation_keys
            )
        )

    def with_output_groups(
        self,
        output_groups: Mapping[ArtifactSpecRef, Iterable[Optional[str]]],
    ) -> "ArtifactGraph":
        """Return a graph with compiler-resolved output scopes."""
        declared_outputs = self.outputs
        for output_ref in output_groups:
            if not isinstance(output_ref, ArtifactSpecRef):
                raise TypeError(
                    "Artifact output-group maps require ArtifactSpecRef keys, "
                    f"got {type(output_ref).__name__}."
                )
            if output_ref not in declared_outputs:
                raise ValueError(
                    f"Artifact output-group key {output_ref!r} is not an exact "
                    "declared output."
                )

        producers: list[ArtifactProducer] = []
        for producer in self.producers:
            output_ref = producer.spec.ref()
            groups = (
                self._require_output_group_values(
                    output_ref,
                    output_groups[output_ref],
                )
                if output_ref in output_groups
                else producer.groups
            )
            producers.append(
                ArtifactProducer(
                    spec=producer.spec,
                    groups=groups,
                    invocation_keys=producer.invocation_keys,
                    producer_step_index=producer.producer_step_index,
                )
            )
        return replace(self, producers=tuple(producers))

    @staticmethod
    def _require_output_group_values(
        output_ref: ArtifactSpecRef,
        groups: Iterable[Optional[str]],
    ) -> tuple[Optional[str], ...]:
        """Return one declared output's validated unique group keys."""

        if isinstance(groups, (str, bytes)):
            raise TypeError(
                f"Artifact output groups for {output_ref!r} must be an iterable "
                "of string or None keys, not a string."
            )
        try:
            group_values = tuple(groups)
        except TypeError as exc:
            raise TypeError(
                f"Artifact output groups for {output_ref!r} must be iterable."
            ) from exc
        for group in group_values:
            if group is not None and not isinstance(group, str):
                raise TypeError(
                    f"Artifact output groups for {output_ref!r} require string "
                    f"or None keys, got {type(group).__name__}."
                )
        return ArtifactGraph.unique_preserving_order(group_values)

    @staticmethod
    def unique_preserving_order(
        values: Iterable[Optional[str]],
    ) -> tuple[Optional[str], ...]:
        """Return unique group keys while preserving declaration order."""
        unique: list[Optional[str]] = []
        for value in values:
            if value not in unique:
                unique.append(value)
        return tuple(unique)


def extract_artifact_declarations(
    pattern: Any,
    declaration_provider: InvocationArtifactDeclarationProviderLike = (
        callable_contract_artifact_declarations
    ),
    invocation_contract_provider: InvocationContractProvider = (
        CompositeInvocationContractProvider(())
    ),
    step_context: ArtifactDeclarationStepContext = (
        ArtifactDeclarationStepContext.empty()
    ),
) -> ArtifactGraph:
    """Extract artifact metadata and per-group ownership from a function pattern."""
    producer_specs = ArtifactSpecAccumulator.empty("producer")
    producer_groups: defaultdict[
        ArtifactSpecRef,
        list[Optional[str]],
    ] = defaultdict(list)
    producer_invocations: defaultdict[
        ArtifactSpecRef,
        list[FunctionInvocationKey],
    ] = defaultdict(list)
    consumers: list[ArtifactConsumer] = []
    declared_input_consumers: list[ArtifactConsumer] = []
    contract_plans: dict[FunctionInvocationKey, InvocationContractPlan | None] = {}
    declarations: dict[FunctionInvocationKey, ArtifactPlanKeySelector] = {}
    normalized = normalize_function_pattern(pattern)
    resolved_items: dict[FunctionInvocationKey, NormalizedFunctionItem] = {}

    for invocation in normalized.iter_items():
        contract_plan = invocation_contract_provider(invocation, step_context)
        contract_plans[invocation.key] = contract_plan
        if contract_plan is not None:
            invocation = replace(invocation, contract=contract_plan.contract)
        resolved_items[invocation.key] = invocation
        artifact_selector = declaration_provider(invocation, step_context)
        declarations[invocation.key] = artifact_selector
        artifact_selector.validate_artifact_relation_refs(
            owner_name=invocation.contract.function_name,
        )
        group_key = invocation.key.group_key
        normalized_key = None if group_key == DEFAULT_GROUP_KEY else group_key

        for spec in artifact_selector.artifact_specs.for_plan_type(
            ArtifactInputPlan
        ).specs:
            declared_input_consumers.append(
                ArtifactConsumer(
                    spec=spec,
                    invocation_keys=(invocation.key,),
                )
            )

        for spec in artifact_selector.artifact_key_specs.for_plan_type(
            ArtifactOutputPlan
        ).specs:
            ref = spec.ref()
            producer_specs.add(spec)
            producer_groups[ref].append(normalized_key)
            producer_invocations[ref].append(invocation.key)

        for spec in artifact_selector.artifact_key_specs.for_plan_type(
            ArtifactInputPlan
        ).specs:
            consumers.append(
                ArtifactConsumer(
                    spec=spec,
                    invocation_keys=(invocation.key,),
                )
            )

    planned_input_refs = frozenset(consumer.spec.ref() for consumer in consumers)
    resolved_pattern = replace(
        normalized,
        groups=tuple(
            replace(
                group, items=tuple(resolved_items[item.key] for item in group.items)
            )
            for group in normalized.groups
        ),
    )
    return ArtifactGraph(
        pattern=resolved_pattern,
        invocation_contract_plans=contract_plans,
        invocation_declarations=declarations,
        producers=tuple(
            ArtifactProducer(
                spec=spec,
                groups=ArtifactGraph.unique_preserving_order(producer_groups[ref]),
                invocation_keys=tuple(producer_invocations[ref]),
            )
            for ref, spec in producer_specs.specs.items()
        ),
        consumers=tuple(consumers),
        non_plan_consumers=tuple(
            consumer
            for consumer in declared_input_consumers
            if consumer.spec.ref() not in planned_input_refs
        ),
    )
