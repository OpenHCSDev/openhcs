"""
Pipeline path planning - actually reduced duplication.

This version ACTUALLY eliminates duplication instead of adding abstraction theater.
"""

from __future__ import annotations

import logging
from collections import defaultdict
from collections.abc import Callable, Hashable, Iterable, Sequence
from dataclasses import dataclass, replace
from functools import lru_cache
from pathlib import Path
from typing import Dict, List, Mapping, Optional

from openhcs.constants import AllComponents, GroupBy, VariableComponents
from openhcs.constants.input_source import InputSource
from openhcs.core.axis_filter import StepAxisFilterSet
from openhcs.core.artifacts import (
    ArtifactInputProjectionPlan,
    ArtifactInputPlan,
    ArtifactOutputPlan,
    ArtifactSpecCollection,
    ArtifactSpecRef,
    ArtifactSpec,
    grouped_artifact_path,
)
from openhcs.core.function_patterns import (
    CompiledFunctionGroup,
    CompiledFunctionInvocation,
    CompiledFunctionPattern,
    FunctionPatternSyntax,
    InvocationArtifactInputEdgePlan,
    InvocationArtifactInputProjectionKey,
    MainFlowInputProjection,
    RuntimeParameterBinding,
    compile_function_pattern,
    inject_artifact_input_values,
    normalize_function_pattern,
)
from openhcs.core.callable_contract import CallableContract, FunctionStepExecutionScope
from objectstate import get_base_type_for_lazy
from openhcs.core.invocation_artifacts import (
    ArtifactDeclarationStepContext,
    PIPELINE_INPUT_ARTIFACT,
)
from openhcs.core.compiled_step_plan import (
    CompiledStepPlan,
    InputConversionPlan,
    MaterializedOutputPlan,
)
from openhcs.core.component_group_scope import ComponentGroupScope
from openhcs.core.component_set import ComponentSet
from openhcs.core.config import PathPlanningConfig
from openhcs.core.pipeline.artifact_planning import (
    ArtifactGraph,
    ArtifactOutputMaterializationPlanner,
    ArtifactProducer,
)
from openhcs.core.pipeline.compilation_session import (
    CompilationPlateScope,
    CompilationSession,
)
from openhcs.core.source_bindings import (
    CompiledSourceBindingPlan,
    CompiledSourceUniversePlan,
    EMPTY_SOURCE_BINDINGS,
    StepSourceBindingsConfig,
    SourceBindingDeclarationsMixin,
    source_binding_group_keys_for_group_by,
)
from openhcs.core.step_dependencies import (
    StepInputDependency,
    StepInputDependencyKind,
)
from openhcs.core.steps.abstract import AbstractStep
from openhcs.core.steps.function_step import FunctionStep

logger = logging.getLogger(__name__)


PlannerGroupKey = str | None
PathPlannerStepDisplayName = str | int


class MissingArtifactInputError(ValueError):
    """Raised when a step consumes an artifact that no prior producer provides."""

    def __init__(
        self,
        *,
        step_id: int,
        artifact_key: str,
        step_name: str | None,
    ) -> None:
        self.step_id = step_id
        self.artifact_key = artifact_key
        self.step_name = step_name
        step_label = step_name or str(step_id)
        super().__init__(
            f"Step {step_id} ({step_label}) needs artifact input "
            f"{artifact_key!r}, but no previous step, source binding, or "
            "metadata resolver provides it."
        )


class PathPlannerGroupScope(ComponentGroupScope):
    """Component-group scope with artifact-planner projections."""

    @classmethod
    def from_output_plan(
        cls,
        output_plan: ArtifactOutputPlan,
    ) -> "PathPlannerGroupScope":
        if output_plan.group_keys:
            return cls.from_raw(
                output_plan.group_keys,
                component=output_plan.group_component,
            )
        return cls.ungrouped()

    @classmethod
    def from_plan(
        cls,
        plan: ArtifactInputPlan | ArtifactOutputPlan,
    ) -> "PathPlannerGroupScope":
        if plan.group_keys:
            return cls.from_raw(
                plan.group_keys,
                component=plan.group_component,
            )
        return cls.ungrouped()

    @classmethod
    def relation_scope_from_plan(
        cls,
        plan: ArtifactInputPlan | ArtifactOutputPlan,
        component: AllComponents | None,
    ) -> "PathPlannerGroupScope":
        """Return the plan domain relevant to one relation component."""

        domain = None if component is None else plan.component_domain(component)
        if domain is None:
            return cls.from_plan(plan)
        return cls.from_raw(domain.keys, component=domain.component)

    def output_groups_for(
        self,
        output_refs: Iterable[ArtifactSpecRef],
    ) -> dict[ArtifactSpecRef, tuple[PlannerGroupKey, ...]]:
        return {output_ref: self.keys for output_ref in output_refs}

    @classmethod
    def union_compatible(
        cls,
        scopes: Sequence["PathPlannerGroupScope"],
    ) -> "PathPlannerGroupScope | None":
        """Union scopes that describe the same grouped component."""

        if not scopes:
            return None
        component = scopes[0].component
        if any(scope.component != component for scope in scopes[1:]):
            return None
        if any(scope.is_dynamic for scope in scopes):
            if component is None:
                raise RuntimeError(
                    "Dynamic component scope lost its component identity."
                )
            return cls.dynamic(component)
        return cls.from_raw(
            dict.fromkeys(key for scope in scopes for key in scope.keys),
            component=component,
        )

    def missing_from(
        self,
        producer_scope: "PathPlannerGroupScope",
    ) -> list[PlannerGroupKey]:
        return [group for group in self.keys if group not in producer_scope.keys]

    def single_group_key(self) -> PlannerGroupKey | None:
        return self.require_single_static_key() if self.has_single_static_key else None


@dataclass(frozen=True)
class PathPlannerComponentScopes:
    """Component value scopes carried by the main-flow image branch."""

    scopes: Mapping[VariableComponents, PathPlannerGroupScope]

    @classmethod
    def empty(cls) -> "PathPlannerComponentScopes":
        return cls({})

    def scope_for_group_by(
        self,
        group_by: GroupBy | None,
    ) -> PathPlannerGroupScope | None:
        group_by_component = self.component_from_group_by(group_by)
        if group_by_component is None:
            return PathPlannerGroupScope.ungrouped()
        return self.scopes.get(group_by_component)

    def output_after(
        self,
        step: AbstractStep,
        execution_scope: PathPlannerGroupScope,
        compiled_pattern: CompiledFunctionPattern | None,
    ) -> "PathPlannerComponentScopes":
        if not isinstance(step, FunctionStep):
            return self
        if compiled_pattern is None:
            raise TypeError(
                "FunctionStep component-scope planning requires its compiled "
                "function pattern."
            )
        if compiled_pattern.preserves_input_main_flow():
            return self

        scopes = dict(self.scopes)
        variable_components = tuple(step.processing_config.variable_components or ())
        for component in variable_components:
            scopes.pop(component, None)
            if compiled_pattern.collapses_input_plane_axis():
                scopes[component] = PathPlannerGroupScope.ungrouped()

        group_by = PathPlannerExecutionGroups.normalized_group_by(step)
        group_by_component = self.component_from_group_by(group_by)
        if (
            group_by_component is not None
            and group_by_component not in variable_components
            and not execution_scope.is_ungrouped
        ):
            scopes[group_by_component] = execution_scope

        return PathPlannerComponentScopes(scopes)

    @staticmethod
    def component_from_group_by(group_by: GroupBy | None) -> VariableComponents | None:
        if group_by is None or group_by is GroupBy.NONE:
            return None
        return VariableComponents(group_by.value)


@dataclass(frozen=True)
class ArtifactPlanMaps:
    """Compiled artifact I/O maps for one step."""

    declarations: ArtifactGraph
    group_scope: PathPlannerGroupScope
    inputs: dict[ArtifactSpecRef, ArtifactInputPlan]
    outputs: dict[ArtifactSpecRef, ArtifactOutputPlan]
    relation_source_scopes: Mapping[ArtifactSpecRef, PathPlannerGroupScope]
    source_binding_plan: CompiledSourceBindingPlan
    source_universe_plan: CompiledSourceUniversePlan


@dataclass(frozen=True)
class PathPlannerExecutionGroups:
    """Execution-group discovery stage for path planning."""

    planner: PathPlanner

    @staticmethod
    def normalize_group_key(key: Hashable | None) -> PlannerGroupKey:
        return PathPlannerGroupScope.normalize_key(key)

    def context_producer_scope(
        self,
        producer: ArtifactProducer,
        *,
        source_component: AllComponents | None,
    ) -> PathPlannerGroupScope:
        """Resolve producer groups against their own compiled axis authority."""

        output_plan = self.planner.declared.get(
            producer.spec.ref().for_plan_type(ArtifactOutputPlan)
        )
        if output_plan is not None:
            return PathPlannerGroupScope.relation_scope_from_plan(
                output_plan, source_component
            )
        if producer.producer_step_index is not None:
            scope = self.planner.plans[producer.producer_step_index].execution_group_scope
            return PathPlannerGroupScope.from_raw(scope.keys, component=scope.component)
        if producer.spec.ref() != PIPELINE_INPUT_ARTIFACT.ref():
            return PathPlannerGroupScope.from_raw(
                producer.groups, component=source_component
            )
        if source_component is None:
            return PathPlannerGroupScope.ungrouped()
        source_keys = tuple(
            self.planner.orchestrator.get_component_keys(
                source_component, resolved_config=self.planner.session.global_config
            )
        )
        return (
            PathPlannerGroupScope.from_raw(source_keys, component=source_component)
            if source_keys else PathPlannerGroupScope.dynamic(source_component)
        )

    def get_execution_groups(
        self,
        step: AbstractStep,
        input_component_scopes: PathPlannerComponentScopes | None = None,
        *,
        source_bindings: SourceBindingDeclarationsMixin | None = None,
        contracts: Sequence[CallableContract] = (),
    ) -> PathPlannerGroupScope:
        """Determine which component groups this step will execute for."""
        if not isinstance(step, FunctionStep):
            return PathPlannerGroupScope.ungrouped()

        func_pattern = normalize_function_pattern(step.func)
        group_by = self.normalized_group_by(step)
        if func_pattern.is_grouped:
            scope = PathPlannerGroupScope.from_raw(
                func_pattern.source_group_keys,
                component=self.execution_component_for_dict_pattern(
                    group_by,
                    step.name,
                ),
            )
            logger.debug("Dict function pattern groups: %s", scope.keys)
            return scope

        component_scopes = (
            PathPlannerComponentScopes.empty()
            if input_component_scopes is None
            else input_component_scopes
        )
        artifact_owned = bool(contracts) and all(
            contract.invocation_domain_inputs for contract in contracts
        )
        if artifact_owned:
            source_bindings = (
                step.source_bindings if source_bindings is None else source_bindings
            ).for_artifact_refs(
                spec.ref()
                for contract in contracts
                for spec in contract.invocation_domain_inputs
            )
        scope = component_scopes.scope_for_group_by(
            group_by,
        )
        if scope is None:
            source_scope = self.source_binding_scope_for_group_by(
                step,
                group_by,
                source_bindings=source_bindings,
            )
            scope = (
                self.dynamic_execution_scope_for_group_by(step, group_by)
                if source_scope.is_ungrouped
                else source_scope
            )
        if artifact_owned:
            scope = self.artifact_owned_execution_scope(
                step,
                contracts,
                consumer_scope=scope,
            )
            logger.debug(
                "Artifact-managed FunctionStep groups for %s: %s",
                step.name,
                scope.keys,
            )
            return scope
        logger.debug("FunctionStep groups for %s: %s", step.name, scope.keys)
        return scope

    def artifact_owned_execution_scope(
        self,
        step: AbstractStep,
        contracts: Sequence[CallableContract],
        *,
        consumer_scope: PathPlannerGroupScope,
    ) -> PathPlannerGroupScope:
        """Resolve invocation groups from their declared input-domain owners."""

        owner_specs = tuple(
            dict.fromkeys(
                spec
                for contract in contracts
                for spec in contract.invocation_domain_inputs
            )
        )
        if not owner_specs:
            raise ValueError(
                f"Artifact-owned FunctionStep {step.name!r} declares no "
                "artifact group-scope owner."
            )

        available_artifacts = self.planner.artifact_context.available_artifacts
        contract_source_bindings = step.source_bindings
        group_by = self.normalized_group_by(step)
        group_component = PathPlannerComponentScopes.component_from_group_by(group_by)
        normalized_group_component = (
            None
            if group_component is None
            else ComponentSet.coerce_component(group_component)
        )
        scopes: list[PathPlannerGroupScope] = []
        for spec in owner_specs:
            producer_ref = spec.ref().for_plan_type(ArtifactOutputPlan)
            producer = self.planner.declared.get(producer_ref)
            if producer is not None:
                scopes.append(
                    PathPlannerGroupScope.relation_scope_from_plan(
                        producer,
                        normalized_group_component,
                    )
                )
                continue

            context_producer = (
                self.planner.artifact_context.available_artifact_producer_for(spec)
            )
            if context_producer is not None:
                scopes.append(
                    self.context_producer_scope(
                        context_producer,
                        source_component=normalized_group_component,
                    )
                )
                continue

            has_source_lineage = (
                contract_source_bindings.binding_for_artifact_ref(spec.ref()) is not None
                or available_artifacts.by_name_and_artifact_type(
                    spec.name,
                    spec.artifact_type,
                )
                is not None
            )
            if not has_source_lineage:
                if self.planner.ctx.microscope_handler.can_resolve_metadata_artifact(
                    spec.name
                ):
                    continue
                if group_by is not GroupBy.NONE:
                    raise ValueError(
                        f"Artifact-owned FunctionStep {step.name!r} cannot "
                        f"resolve group scope for {spec.ref()!r}."
                    )
                scopes.append(PathPlannerGroupScope.ungrouped())
                continue

            source_group_keys = (
                ()
                if normalized_group_component is None
                else contract_source_bindings.component_group_keys_for_artifact_specs(
                    normalized_group_component,
                    (spec,),
                    available_artifacts,
                    realized_source_metadata=(
                        self.planner.session.realized_source_metadata
                    ),
                )
            )
            source_scope = (
                PathPlannerGroupScope.from_raw(
                    source_group_keys,
                    component=normalized_group_component,
                )
                if source_group_keys
                else PathPlannerGroupScope.ungrouped()
            )
            if source_scope.is_ungrouped and group_by is not GroupBy.NONE:
                raise ValueError(
                    f"Artifact-owned FunctionStep {step.name!r} cannot "
                    f"resolve group scope for {spec.ref()!r}."
                )
            scopes.append(source_scope)

        if not scopes:
            return consumer_scope

        consumer_variable_components = ComponentSet.from_enum_values(
            step.processing_config.variable_components or ()
        )
        projected_scopes = tuple(
            scope.output_lineage_scope(
                consumer_scope,
                consumer_variable_components,
            )
            for scope in scopes
        )
        execution_scope = PathPlannerGroupScope.union_compatible(projected_scopes)
        if execution_scope is None:
            raise ValueError(
                f"Artifact-owned FunctionStep {step.name!r} has "
                f"incompatible declared owner scopes {projected_scopes!r}."
            )
        return execution_scope

    def dynamic_execution_scope_for_group_by(
        self,
        step: AbstractStep,
        group_by: GroupBy | None,
    ) -> PathPlannerGroupScope:
        """Return a typed runtime-discovered scope for a concrete group axis."""
        group_by_component = PathPlannerComponentScopes.component_from_group_by(group_by)
        if group_by_component is None:
            return PathPlannerGroupScope.ungrouped()
        source_keys = (
            tuple(
                self.planner.orchestrator.get_component_keys(
                    group_by_component,
                    resolved_config=self.planner.session.global_config,
                )
            )
            if step.processing_config.input_source is InputSource.PIPELINE_START
            else ()
        )
        if source_keys:
            return PathPlannerGroupScope.from_raw(
                source_keys,
                component=ComponentSet.coerce_component(group_by_component),
            )
        return PathPlannerGroupScope.dynamic(
            ComponentSet.coerce_component(group_by_component)
        )

    def source_binding_scope_for_group_by(
        self,
        step: AbstractStep,
        group_by: GroupBy | None,
        *,
        source_bindings: SourceBindingDeclarationsMixin | None = None,
    ) -> PathPlannerGroupScope:
        """Derive execution groups declared by source-binding component identity."""
        group_by_component = PathPlannerComponentScopes.component_from_group_by(group_by)
        if group_by_component is None:
            return PathPlannerGroupScope.ungrouped()

        if source_bindings is None:
            source_bindings = step.source_bindings
        if not source_bindings.binding_declarations:
            return PathPlannerGroupScope.ungrouped()
        component = ComponentSet.coerce_component(group_by_component)
        group_keys = source_binding_group_keys_for_group_by(
            source_bindings,
            group_by,
            realized_source_metadata=self.planner.session.realized_source_metadata,
        )
        if not group_keys:
            return PathPlannerGroupScope.ungrouped()
        return PathPlannerGroupScope.from_raw(group_keys, component=component)

    @staticmethod
    def execution_component_for_dict_pattern(
        group_by: GroupBy | None,
        step_name: str | None,
    ) -> AllComponents:
        """Return the declared component for dict-pattern runtime dispatch."""
        if group_by is None or group_by is GroupBy.NONE or group_by.value is None:
            raise ValueError(
                f"Step '{step_name}' uses a dict function pattern without a "
                "concrete group_by component. Dict keys are dispatch groups; "
                "GroupBy.NONE is only valid for non-dict function patterns."
            )
        return AllComponents.from_value(group_by.value)

    @staticmethod
    def normalized_group_by(step: AbstractStep) -> GroupBy:
        """Use the same group_by normalization as compiled execution plans."""
        from openhcs.core.pipeline.funcstep_contract_validator import (
            FuncStepContractValidator,
        )

        return FuncStepContractValidator.normalized_group_by(
            step.processing_config.group_by,
            step.processing_config.variable_components,
            step.name,
            normalize_function_pattern(step.func),
        )


@dataclass(frozen=True)
class PathPlannerMetadataArtifactInjection:
    """Shared provider selection and invocation-owned metadata injection."""

    planner: PathPlanner

    def metadata_artifact_available(self, artifact_name: str) -> bool:
        """Derive availability from the original microscope provider owner."""
        return self.planner.ctx.microscope_handler.can_resolve_metadata_artifact(
            artifact_name
        )

    def inject_metadata(
        self,
        pattern: FunctionPatternSyntax,
        inputs: Mapping[ArtifactSpecRef, ArtifactSpec],
    ) -> FunctionPatternSyntax:
        """Inject values once; compiled metadata edges reference these kwargs."""
        for spec in inputs.values():
            if (
                spec.ref().for_plan_type(ArtifactOutputPlan) not in self.planner.declared
                and self.metadata_artifact_available(spec.name)
            ):
                value = self.planner.ctx.microscope_handler.resolve_metadata_artifact(
                    spec.name,
                    self.planner.ctx.plate_path,
                )
                pattern = inject_artifact_input_values(pattern, {spec.name: value})
        return pattern


@dataclass(frozen=True)
class PathPlannerArtifactStage(PathPlannerMetadataArtifactInjection):
    """Artifact declaration and I/O planning with inherited metadata binding."""

    def source_binding_component_domains(
        self,
        specs: Iterable[ArtifactSpec],
        source_bindings: SourceBindingDeclarationsMixin,
        available_artifacts: ArtifactSpecCollection,
    ) -> tuple[PathPlannerGroupScope, ...]:
        """Compile every declared component domain owned by source bindings."""

        bindings = source_bindings.bindings_for_artifact_specs(
            specs,
            available_artifacts,
        )
        binding_domains = tuple(
            binding.component_domains(
                realized_source_metadata=self.planner.session.realized_source_metadata
            )
            for binding in bindings
        )
        return tuple(
            PathPlannerGroupScope.from_raw(values, component=component)
            for component in AllComponents
            for values in (
                tuple(dict.fromkeys(
                    value
                    for domains in binding_domains
                    for value in domains.get(component, ())
                )),
            )
            if values
        )

    def compile_plan_maps(
        self,
        step: AbstractStep,
        step_index: int,
        declarations: ArtifactGraph,
        group_scope: PathPlannerGroupScope,
        execution_scope: FunctionStepExecutionScope = FunctionStepExecutionScope.AXIS,
        source_bindings: StepSourceBindingsConfig | CompiledSourceBindingPlan = EMPTY_SOURCE_BINDINGS,
    ) -> ArtifactPlanMaps:
        """Compile artifact declarations into runtime I/O maps."""
        step_name = step.name
        group_by = PathPlannerExecutionGroups.normalized_group_by(step)
        source_binding_plan = (
            source_bindings
            if isinstance(source_bindings, CompiledSourceBindingPlan)
            else (
                CompiledSourceBindingPlan.from_config(
                    source_bindings,
                    realized_source_metadata=self.planner.session.realized_source_metadata,
                )
                if source_bindings.binding_declarations
                else CompiledSourceBindingPlan.empty()
            )
        )
        source_universe_plan = CompiledSourceUniversePlan.from_source_binding_plan(
            source_binding_plan
        )
        consumer_variable_components = ComponentSet.from_enum_values(
            step.processing_config.variable_components or ()
        )
        artifact_inputs = self.process_artifact_inputs(
            declarations,
            step_index,
            consumer_scope=group_scope,
            source_bindings=source_bindings,
            variable_components=consumer_variable_components,
            step_name=step_name,
            execution_scope=execution_scope,
        )
        relation_source_scopes = self.relation_source_scopes_by_ref(
            declarations,
            artifact_inputs,
            group_scope=group_scope,
            source_bindings=source_bindings,
            group_by=group_by,
        )
        output_relation_source_scopes = self.output_relation_source_scopes_by_ref(
            declarations,
            relation_source_scopes,
        )
        output_groups = self.output_groups_from_declared_relations(
            declarations,
            group_scope=group_scope,
            relation_source_scopes=output_relation_source_scopes,
            consumer_variable_components=consumer_variable_components,
            step_index=step_index,
            step_name=step_name,
        )
        artifact_outputs = self.process_artifact_outputs(
            declarations,
            step_index,
            output_groups,
            execution_scope=execution_scope,
            artifact_inputs=artifact_inputs,
            relation_source_scopes=output_relation_source_scopes,
            source_bindings=source_bindings,
            variable_components=consumer_variable_components,
            step_name=step_name,
        )
        artifact_inputs = {
            input_ref: (
                self._producer_artifact_input_plan(
                    input_plan.ref().for_plan_type(ArtifactOutputPlan),
                    declarations.inputs[input_ref],
                    step_index,
                    step_name,
                )
                if input_plan.source_step_id == step_index
                else input_plan
            )
            for input_ref, input_plan in artifact_inputs.items()
        }
        relation_source_scopes = self.relation_source_scopes_by_ref(
            declarations,
            artifact_inputs,
            group_scope=group_scope,
            source_bindings=source_bindings,
            group_by=group_by,
        )
        return ArtifactPlanMaps(
            declarations=declarations,
            group_scope=group_scope,
            inputs=artifact_inputs,
            outputs=artifact_outputs,
            relation_source_scopes=relation_source_scopes,
            source_binding_plan=source_binding_plan,
            source_universe_plan=source_universe_plan,
        )

    def output_groups_from_declared_relations(
        self,
        declarations: ArtifactGraph,
        *,
        group_scope: PathPlannerGroupScope,
        relation_source_scopes: Mapping[ArtifactSpecRef, PathPlannerGroupScope],
        consumer_variable_components: ComponentSet,
        step_index: int,
        step_name: str | None,
    ) -> Mapping[ArtifactSpecRef, PathPlannerGroupScope]:
        """Return output groups after applying declared artifact relations."""
        output_groups: dict[ArtifactSpecRef, PathPlannerGroupScope] = {}
        for producer in declarations.producers:
            output_ref = producer.spec.ref()
            if producer.has_explicit_invocation_group_ownership():
                output_groups[output_ref] = PathPlannerGroupScope.from_raw(
                    producer.groups,
                    component=group_scope.component,
                )
                continue
            lineage_refs = producer.spec.group_scope_sources()
            if not lineage_refs:
                output_groups[output_ref] = group_scope
                continue
            try:
                lineage_scopes = tuple(
                    relation_source_scopes[source] for source in lineage_refs
                )
            except KeyError as exc:
                source = exc.args[0]
                if not isinstance(source, ArtifactSpecRef):
                    raise
                raise MissingArtifactInputError(
                    step_id=step_index,
                    artifact_key=source.name,
                    step_name=step_name,
                ) from exc
            projected_scopes = tuple(
                lineage_scope.output_lineage_scope(
                    group_scope,
                    consumer_variable_components,
                )
                for lineage_scope in lineage_scopes
            )
            first_scope = projected_scopes[0]
            output_groups[output_ref] = (
                first_scope
                if all(scope == first_scope for scope in projected_scopes[1:])
                else group_scope
            )
        return output_groups

    @staticmethod
    def output_relation_source_scopes_by_ref(
        declarations: ArtifactGraph,
        relation_source_scopes: Mapping[
            ArtifactSpecRef,
            PathPlannerGroupScope,
        ],
    ) -> dict[ArtifactSpecRef, PathPlannerGroupScope]:
        """Project input-qualified lineage for outputs without changing storage scope."""

        resolved = dict(relation_source_scopes)

        def declared_scope(source_ref: ArtifactSpecRef) -> PathPlannerGroupScope:
            try:
                return relation_source_scopes[source_ref]
            except KeyError as exc:
                raise ValueError(
                    "Output lineage source has no compiled scope: " f"{source_ref!r}."
                ) from exc

        for source_ref, lineage_refs in declarations.input_lineage_order:
            if not lineage_refs:
                declared_scope(source_ref)
                continue
            lineage_scopes = tuple(
                declared_scope(source_ref) if ref == source_ref else resolved[ref]
                for ref in lineage_refs
            )
            projected = PathPlannerGroupScope.union_compatible(lineage_scopes)
            if projected is None:
                raise ValueError(
                    f"Input {source_ref!r} has incompatible group-lineage scopes "
                    f"{lineage_scopes!r}."
                )
            resolved[source_ref] = projected
        return resolved

    @staticmethod
    def output_group_scope_sources_by_group(
        spec: ArtifactSpec,
        group_scope: PathPlannerGroupScope,
        relation_source_scopes: Mapping[ArtifactSpecRef, PathPlannerGroupScope],
    ) -> dict[str | None, tuple[ArtifactSpecRef, ...]]:
        """Compile exact relation sources for each output component group."""

        source_refs = spec.group_scope_sources()
        if not source_refs:
            return {}
        sources_by_group: dict[str | None, tuple[ArtifactSpecRef, ...]] = {}
        for group_key in group_scope.keys:
            if group_scope.is_ungrouped or group_key is None:
                selected = source_refs
            else:
                selected = tuple(
                    source_ref
                    for source_ref in source_refs
                    for source_scope in (relation_source_scopes[source_ref],)
                    if (
                        source_scope.is_ungrouped
                        or source_scope.component is not group_scope.component
                        or source_scope.is_dynamic
                        or source_scope.contains_runtime_key(group_key)
                    )
                )
            if not selected:
                raise ValueError(
                    f"Artifact output {spec.ref()!r} group {group_key!r} has no "
                    "declared group-scope source."
                )
            sources_by_group[group_key] = selected
        return sources_by_group

    def relation_source_scopes_by_ref(
        self,
        declarations: ArtifactGraph,
        artifact_inputs: Mapping[ArtifactSpecRef, ArtifactInputPlan],
        *,
        group_scope: PathPlannerGroupScope,
        source_bindings: SourceBindingDeclarationsMixin,
        group_by: GroupBy | None,
    ) -> dict[ArtifactSpecRef, PathPlannerGroupScope]:
        """Return exact group scopes for every declared relation source."""

        source_scopes_by_ref: dict[ArtifactSpecRef, PathPlannerGroupScope] = {}
        ArtifactInputPlan.require_exact_map(
            artifact_inputs,
            boundary="Path planner artifact input",
        )
        component = group_scope.component
        if component is None:
            grouped_component = PathPlannerComponentScopes.component_from_group_by(
                group_by
            )
            if grouped_component is not None:
                component = ComponentSet.coerce_component(grouped_component)
        for input_ref, spec in declarations.inputs.items():
            input_plan = artifact_inputs.get(input_ref)
            if input_plan is None:
                context_producer = (
                    self.planner.artifact_context.available_artifact_producer_for(spec)
                )
                if context_producer is not None:
                    source_scopes_by_ref[spec.ref()] = (
                        self.planner.execution_groups.context_producer_scope(
                            context_producer,
                            source_component=component,
                        )
                    )
                continue
            source_scopes_by_ref[spec.ref()] = (
                PathPlannerGroupScope.relation_scope_from_plan(
                    input_plan,
                    component,
                )
            )
        for binding in source_bindings.binding_declarations:
            identity_values = (
                binding.component_values(
                    component,
                    realized_source_metadata=(
                        self.planner.session.realized_source_metadata
                    ),
                )
                if component is not None
                else ()
            )
            binding_scope = (
                PathPlannerGroupScope.from_raw(
                    identity_values,
                    component=component,
                )
                if identity_values
                else group_scope
            )
            source_scopes_by_ref.setdefault(
                binding.input_spec().ref(),
                binding_scope,
            )
        for consumer in declarations.non_plan_consumers:
            producer_ref = consumer.spec.ref().for_plan_type(ArtifactOutputPlan)
            producer_plan = self.planner.declared.get(producer_ref)
            source_scopes_by_ref.setdefault(
                consumer.spec.ref(),
                (
                    PathPlannerGroupScope.relation_scope_from_plan(
                        producer_plan,
                        component,
                    )
                    if producer_plan is not None
                    else group_scope
                ),
            )
        relation_sources = tuple(
            dict.fromkeys(
                source_ref
                for spec in (
                    *declarations.inputs.values(),
                    *declarations.outputs.values(),
                )
                for source_ref in spec.dependency_refs()
            )
        )
        for source_ref in relation_sources:
            if source_ref in source_scopes_by_ref:
                continue
            producer_plan = self.planner.declared.get(
                source_ref.for_plan_type(ArtifactOutputPlan)
            )
            if producer_plan is None:
                continue
            source_scopes_by_ref[source_ref] = (
                PathPlannerGroupScope.relation_scope_from_plan(
                    producer_plan,
                    component,
                )
            )
        for spec in dict.fromkeys(
            consumer.spec
            for consumer in (
                *declarations.consumers,
                *declarations.non_plan_consumers,
            )
        ):
            active_spec = self.planner.artifact_context.available_artifacts.by_name_and_artifact_type(
                spec.name, spec.artifact_type
            )
            lineage_spec = spec if active_spec is None else active_spec
            source_stack_scopes = tuple(
                source_scopes_by_ref[source_ref]
                for source_ref in lineage_spec.source_stack_scope_sources()
                if source_ref in source_scopes_by_ref
                and source_scopes_by_ref[source_ref].component is group_scope.component
            )
            inherited_scope = PathPlannerGroupScope.union_compatible(
                source_stack_scopes
            )
            if inherited_scope is not None:
                source_scopes_by_ref[spec.ref()] = inherited_scope
        return source_scopes_by_ref

    def build_step_compiled_function_pattern(
        self,
        step: AbstractStep,
        step_index: int,
        is_function_step: bool,
        func_pattern: FunctionPatternSyntax | None,
        artifact_inputs: Mapping[ArtifactSpecRef, ArtifactInputPlan],
        artifact_outputs: Mapping[ArtifactSpecRef, ArtifactOutputPlan],
        relation_source_scopes: Mapping[
            ArtifactSpecRef,
            PathPlannerGroupScope,
        ],
        execution_group_scope: PathPlannerGroupScope,
        declarations: ArtifactGraph,
    ) -> CompiledFunctionPattern | None:
        """Build the executable function-pattern graph for a FunctionStep."""
        if not is_function_step or not func_pattern:
            return None

        step_context = self.planner.artifact_context
        step_values = vars(step)
        pipeline_values = vars(self.planner.session.global_config)
        runtime_parameter_bindings: list[RuntimeParameterBinding] = []
        for parameter in declarations.config_parameters_for_step(step.name):
            parameter_name = parameter.name
            provider = (
                step_values[parameter_name]
                if parameter_name in step_values
                else pipeline_values[parameter_name]
            )
            parameter_type = (
                get_base_type_for_lazy(parameter.annotation) or parameter.annotation
            )
            if not isinstance(provider, parameter_type):
                raise TypeError(
                    f"FunctionStep {step.name!r} config parameter "
                    f"{parameter_name!r} requires {parameter_type.__name__}, got "
                    f"{type(provider).__name__}."
                )
            runtime_parameter_bindings.append(
                RuntimeParameterBinding(
                    parameter_name=parameter_name,
                    value=provider,
                )
            )

        compiled_pattern = compile_function_pattern(
            func_pattern,
            artifact_inputs,
            artifact_outputs,
            artifact_graph=declarations,
            step_context=step_context,
            runtime_parameter_bindings=tuple(runtime_parameter_bindings),
            path_resolver=self.planner.session.path_resolver,
        )
        available_artifacts = step_context.available_artifacts.rebind(
            compiled_pattern.coalesced_artifact_output_specs()
        )
        return self.compile_invocation_input_edges(
            compiled_pattern,
            artifact_inputs=artifact_inputs,
            relation_source_scopes=relation_source_scopes,
            execution_group_scope=execution_group_scope,
            consumer_variable_components=ComponentSet.from_enum_values(
                step.processing_config.variable_components or ()
            ),
            source_bindings=step_context.source_bindings,
            available_artifacts=available_artifacts,
            main_flow_artifacts=step_context.main_flow_artifacts,
            metadata_artifact_available=self.metadata_artifact_available,
        )

    def compile_invocation_input_edges(
        self,
        compiled_pattern: CompiledFunctionPattern,
        *,
        artifact_inputs: Mapping[ArtifactSpecRef, ArtifactInputPlan],
        relation_source_scopes: Mapping[
            ArtifactSpecRef,
            PathPlannerGroupScope,
        ],
        execution_group_scope: PathPlannerGroupScope,
        consumer_variable_components: ComponentSet,
        source_bindings: StepSourceBindingsConfig | CompiledSourceBindingPlan = EMPTY_SOURCE_BINDINGS,
        available_artifacts: ArtifactSpecCollection = ArtifactSpecCollection(()),
        main_flow_artifacts: ArtifactSpecCollection = ArtifactSpecCollection(()),
        metadata_artifact_available: Callable[[str], bool] = lambda _name: False,
    ) -> CompiledFunctionPattern:
        """Compile exact invocation-to-input projections from nominal contracts."""

        groups: list[CompiledFunctionGroup] = []
        for group in compiled_pattern.groups:
            invocations: list[CompiledFunctionInvocation] = []
            for invocation in group.invocations:
                if compiled_pattern.is_grouped:
                    if execution_group_scope.is_ungrouped:
                        raise ValueError(
                            f"Grouped invocation {invocation.key!r} has no grouped "
                            "execution component."
                        )
                    invocation_scope = PathPlannerGroupScope.from_raw(
                        (
                            execution_group_scope.resolve_runtime_key(
                                invocation.key.group_key
                            ),
                        ),
                        component=execution_group_scope.component,
                    )
                elif execution_group_scope.is_ungrouped:
                    invocation_scope = execution_group_scope
                elif execution_group_scope.has_single_static_key:
                    invocation_scope = execution_group_scope
                else:
                    invocation_scope = PathPlannerGroupScope.dynamic(
                        execution_group_scope.component
                    )
                selected_plans = invocation.contract.select_plans(
                    ArtifactInputPlan,
                    artifact_inputs,
                )
                input_edge_keys = InvocationArtifactInputProjectionKey.for_input_count(
                    invocation.key,
                    len(invocation.contract.artifact_inputs),
                )
                selected_plans_by_ref = {plan.ref(): plan for plan in selected_plans}
                adapter = invocation.contract.runtime_adapter
                owns_artifact_inputs = (
                    adapter is not None and adapter.manages_artifact_inputs
                )
                raw_main_flow_refs = (
                    main_flow_artifacts.ref_set()
                    .intersection(invocation.contract.output_group_scope_sources)
                    if not owns_artifact_inputs
                    else frozenset()
                )
                edges: list[InvocationArtifactInputEdgePlan] = []
                for input_edge_key, input_spec in zip(
                    input_edge_keys,
                    invocation.contract.artifact_inputs,
                    strict=True,
                ):
                    storage_plan = (
                        None if input_spec.ref() in raw_main_flow_refs
                        else selected_plans_by_ref.get(input_spec.ref())
                    )
                    if storage_plan is None:
                        edges.append(
                            InvocationArtifactInputEdgePlan.from_source_declarations(
                                key=input_edge_key,
                                spec=input_spec,
                                main_flow_artifacts=main_flow_artifacts,
                                invocation_sources=invocation.contract.group_scope_inputs,
                                metadata_available=metadata_artifact_available(input_spec.name),
                                source_binding_available=source_bindings.declares_artifact_ref(input_spec.ref()),
                            )
                        )
                        continue
                    edges.append(
                        self.invocation_input_edge(
                            invocation,
                            input_edge_key,
                            input_spec=input_spec,
                            storage_plan=storage_plan,
                            invocation_scope=invocation_scope,
                            relation_source_scopes=relation_source_scopes,
                            consumer_variable_components=consumer_variable_components,
                            source_bindings=source_bindings,
                            available_artifacts=available_artifacts,
                            main_flow_projection=InvocationArtifactInputEdgePlan.source_projection(
                                input_spec,
                                main_flow_artifacts,
                                invocation.contract.group_scope_inputs,
                            ) if owns_artifact_inputs else None,
                        )
                    )
                invocations.append(invocation.with_artifact_input_edges(tuple(edges)))
            groups.append(replace(group, invocations=tuple(invocations)))
        return replace(compiled_pattern, groups=tuple(groups))

    def invocation_input_edge(
        self,
        invocation: CompiledFunctionInvocation,
        input_edge_key: InvocationArtifactInputProjectionKey,
        *,
        input_spec: ArtifactSpec,
        storage_plan: ArtifactInputPlan,
        invocation_scope: PathPlannerGroupScope,
        relation_source_scopes: Mapping[
            ArtifactSpecRef,
            PathPlannerGroupScope,
        ],
        consumer_variable_components: ComponentSet,
        source_bindings: SourceBindingDeclarationsMixin,
        available_artifacts: ArtifactSpecCollection,
        main_flow_projection: MainFlowInputProjection | None,
    ) -> InvocationArtifactInputEdgePlan:
        """Compile one exact relation-owned invocation input edge."""

        if input_edge_key.invocation_key != invocation.key:
            raise ValueError(
                f"Invocation {invocation.key!r} cannot compile input edge for "
                f"{input_edge_key.invocation_key!r}."
            )
        artifact_ref = storage_plan.ref()
        if input_spec.ref() != artifact_ref:
            raise ValueError(
                f"Invocation {invocation.key!r} input declaration "
                f"{input_spec.ref()!r} does not match compiled plan {artifact_ref!r}."
            )
        if invocation.contract.execution_scope is FunctionStepExecutionScope.PLATE:
            projection = ArtifactInputProjectionPlan(
                invocation_scope=invocation_scope,
                producer_selection_scope=PathPlannerGroupScope.from_plan(storage_plan),
            )
            return InvocationArtifactInputEdgePlan(
                key=input_edge_key,
                spec=input_spec,
                storage_plan=storage_plan,
                projection=projection,
                main_flow_projection=main_flow_projection,
            )

        relation_scopes = tuple(
            self.require_relation_source_scope(
                source_ref,
                relation_source_scopes,
                invocation,
            )
            for source_ref in input_spec.group_scope_sources()
        )
        source_binding_domains = (
            ()
            if storage_plan.source_step_id is not None
            else self.source_binding_component_domains(
                (input_spec,),
                source_bindings,
                available_artifacts,
            )
        )
        storage_domains = tuple(
            PathPlannerGroupScope.from_raw(
                domain.keys,
                component=domain.component,
            )
            for domain in storage_plan.component_domains
        )
        component_scopes = self.exact_component_scopes(
            storage_domains,
            relation_scopes,
            component_domains=(
                *storage_domains,
                *source_binding_domains,
            ),
            invocation_scope=invocation_scope,
            invocation=invocation,
            artifact_ref=artifact_ref,
        )
        producer_selection_scope = ArtifactInputProjectionPlan.producer_selection_for_invocation(
            input_spec=input_spec,
            storage_plan=storage_plan,
            component_scopes=component_scopes,
            consumer_variable_components=consumer_variable_components,
            invocation_key=invocation.key,
            execution_scope=invocation.contract.execution_scope,
        )

        projection = ArtifactInputProjectionPlan(
            invocation_scope=invocation_scope,
            producer_selection_scope=producer_selection_scope,
            component_scopes=component_scopes,
            consumer_variable_components=consumer_variable_components.as_tuple(),
        )
        return InvocationArtifactInputEdgePlan(
            key=input_edge_key,
            spec=input_spec,
            storage_plan=storage_plan,
            projection=projection,
            main_flow_projection=main_flow_projection,
        )

    @staticmethod
    def require_relation_source_scope(
        source_ref: ArtifactSpecRef,
        relation_source_scopes: Mapping[
            ArtifactSpecRef,
            PathPlannerGroupScope,
        ],
        invocation: CompiledFunctionInvocation,
    ) -> PathPlannerGroupScope:
        """Return one exact compiler-resolved relation source scope."""

        try:
            return relation_source_scopes[source_ref]
        except KeyError as exc:
            raise ValueError(
                f"Invocation {invocation.key!r} relation source {source_ref!r} "
                "has no compiled scope."
            ) from exc

    @staticmethod
    def exact_component_scopes(
        storage_domains: Sequence[ComponentGroupScope],
        relation_scopes: Sequence[ComponentGroupScope],
        *,
        component_domains: Sequence[ComponentGroupScope],
        invocation_scope: ComponentGroupScope,
        invocation: CompiledFunctionInvocation,
        artifact_ref: ArtifactSpecRef,
    ) -> tuple[ComponentGroupScope, ...]:
        """Resolve exact producer coordinates without conflating consumer scope."""

        by_component: dict[AllComponents, ComponentGroupScope] = {}
        storage_components: set[AllComponents] = set()
        for domain in storage_domains:
            if domain.is_ungrouped or domain.is_dynamic or len(domain.keys) != 1:
                continue
            component = domain.component
            if component is None:
                raise RuntimeError("Grouped storage domain lost its component.")
            by_component[component] = domain
            storage_components.add(component)

        for scope in relation_scopes:
            if scope.is_ungrouped:
                continue
            component = scope.component
            if component is None:
                raise RuntimeError("Grouped projection scope lost its component.")
            existing = by_component.get(component)
            if component in storage_components:
                continue
            if existing is not None and existing != scope:
                raise ValueError(
                    f"Invocation {invocation.key!r} input {artifact_ref!r} declares "
                    f"conflicting {component.value!r} coordinates {existing!r} and "
                    f"{scope!r}."
                )
            by_component[component] = scope

        for domain in component_domains:
            if domain.is_ungrouped:
                continue
            component = domain.component
            if component is None:
                raise RuntimeError("Grouped component domain lost its component.")
            exact_scope = by_component.get(component)
            if (
                exact_scope is not None
                and not exact_scope.is_dynamic
                and not domain.contains_scope(exact_scope)
            ):
                raise ValueError(
                    f"Invocation {invocation.key!r} input {artifact_ref!r} "
                    f"has exact {component.value!r} coordinate {exact_scope!r} "
                    f"outside component domain {domain!r}."
                )

        if not invocation_scope.is_ungrouped:
            component = invocation_scope.component
            if component is None:
                raise RuntimeError("Grouped invocation scope lost its component.")
            by_component.setdefault(component, invocation_scope)
        return tuple(by_component.values())

    def process_artifact_outputs(
        self,
        declarations: ArtifactGraph,
        sid: int,
        output_groups: Mapping[ArtifactSpecRef, PathPlannerGroupScope] | None = None,
        *,
        execution_scope: FunctionStepExecutionScope,
        artifact_inputs: Mapping[ArtifactSpecRef, ArtifactInputPlan],
        relation_source_scopes: (
            Mapping[
                ArtifactSpecRef,
                PathPlannerGroupScope,
            ]
            | None
        ) = None,
        source_bindings: SourceBindingDeclarationsMixin,
        variable_components: ComponentSet,
        step_name: Optional[str] = None,
    ) -> dict[ArtifactSpecRef, ArtifactOutputPlan]:
        """Compile storage plans for artifacts produced by this step."""
        result: dict[ArtifactSpecRef, ArtifactOutputPlan] = {}
        outputs = declarations.outputs
        ArtifactInputPlan.require_exact_map(
            artifact_inputs,
            boundary="Path planner artifact input",
        )
        if output_groups is not None:
            for output_ref, output_scope in output_groups.items():
                if not isinstance(output_ref, ArtifactSpecRef):
                    raise TypeError(
                        "Path planner output-group maps require ArtifactSpecRef "
                        f"keys, got {type(output_ref).__name__}."
                    )
                if not isinstance(output_scope, PathPlannerGroupScope):
                    raise TypeError(
                        "Path planner output-group maps require "
                        "PathPlannerGroupScope values, got "
                        f"{type(output_scope).__name__} for {output_ref!r}."
                    )
                if output_ref not in outputs:
                    raise ValueError(
                        f"Path planner output-group key {output_ref!r} is not an "
                        "exact declared output."
                    )
        if not outputs:
            return result

        relation_source_scopes = relation_source_scopes or {}
        available_artifacts = self.planner.artifact_context.available_artifacts
        main_flow_artifacts = self.planner.artifact_context.main_flow_artifacts

        for output_ref, spec in sorted(
            outputs.items(),
            key=lambda item: item[1].name,
        ):
            key = spec.name
            path = self.planner.paths.artifact_path(
                declarations.require_output_storage_key(output_ref),
                sid,
                execution_scope=execution_scope,
            )
            group_scope = (
                output_groups[output_ref]
                if output_groups is not None and output_ref in output_groups
                else PathPlannerGroupScope.ungrouped()
            )
            normalized_groups = list(group_scope.keys)
            paths_by_group = self.planner.paths.paths_by_group(
                str(path),
                normalized_groups,
            )
            source_stack_axes: list[ComponentSet] = []
            source_stack_domains: list[PathPlannerGroupScope] = []
            source_binding_domains: list[PathPlannerGroupScope] = []
            for source_ref in spec.source_stack_scope_sources():
                source_plan = artifact_inputs.get(source_ref)
                relation_scope = relation_source_scopes.get(source_ref)
                if relation_scope is not None and not relation_scope.is_ungrouped:
                    source_stack_domains.append(relation_scope)
                if source_plan is not None:
                    source_stack_domains.extend(
                        PathPlannerGroupScope.from_raw(
                            domain.keys,
                            component=domain.component,
                        )
                        for domain in source_plan.component_domains
                    )
                    source_stack_axes.append(
                        source_plan.runtime_variable_components(variable_components)
                    )
                    continue

                source_binding = source_bindings.binding_for_artifact_ref(source_ref)
                main_flow_spec = main_flow_artifacts.by_ref(source_ref)
                source_spec = (
                    source_binding.input_spec()
                    if source_binding is not None
                    else main_flow_spec
                )
                if source_spec is not None:
                    source_binding_domains.extend(
                        self.source_binding_component_domains(
                            (source_spec,),
                            source_bindings,
                            available_artifacts,
                        )
                    )

                if source_spec is None:
                    raise ValueError(
                        f"Artifact output {spec.ref()!r} preserves the stack of "
                        f"undeclared input {source_ref!r}."
                    )
                source_binding_axes = (
                    source_bindings.runtime_variable_components_for_artifact_specs(
                        (source_spec,),
                        available_artifacts,
                        variable_components,
                    )
                )
                if source_binding_axes is not None:
                    source_stack_axes.append(source_binding_axes)
                    continue
                if main_flow_spec is not None:
                    source_stack_axes.append(variable_components)
                    continue
                raise ValueError(
                    f"Artifact output {spec.ref()!r} preserves the stack of "
                    f"undeclared input {source_ref!r}."
                )
            lineage_domains_by_component: dict[
                AllComponents,
                list[PathPlannerGroupScope],
            ] = defaultdict(list)
            for domain in source_stack_domains:
                if domain.component is None:
                    raise RuntimeError(
                        "Artifact output source-stack domain lost its component."
                    )
                if domain not in lineage_domains_by_component[domain.component]:
                    lineage_domains_by_component[domain.component].append(domain)
            binding_domains_by_component: dict[
                AllComponents,
                list[PathPlannerGroupScope],
            ] = defaultdict(list)
            for domain in source_binding_domains:
                if domain.component is None:
                    raise RuntimeError(
                        "Artifact output source-binding domain lost its component."
                    )
                if domain not in binding_domains_by_component[domain.component]:
                    binding_domains_by_component[domain.component].append(domain)
            component_domains_list: list[PathPlannerGroupScope] = []
            components = ComponentSet.collect(
                lineage_domains_by_component,
                binding_domains_by_component,
            )
            for component in components:
                lineage_domain = PathPlannerGroupScope.union_compatible(
                    lineage_domains_by_component[component]
                )
                binding_domain = PathPlannerGroupScope.union_compatible(
                    binding_domains_by_component[component]
                )
                if (
                    lineage_domain is not None
                    and binding_domain is not None
                    and not lineage_domain.is_dynamic
                    and not binding_domain.contains_scope(lineage_domain)
                ):
                    raise ValueError(
                        f"Artifact output {spec.ref()!r} inherits "
                        f"{component.value!r} lineage {lineage_domain!r} outside "
                        f"source-binding domain {binding_domain!r}."
                    )
                component_domain = lineage_domain or binding_domain
                if component_domain is None:
                    raise RuntimeError(
                        "Artifact output component-domain compilation lost its scope."
                    )
                component_domains_list.append(component_domain)
            component_domains = tuple(component_domains_list)
            if source_stack_axes and any(
                axes != source_stack_axes[0] for axes in source_stack_axes[1:]
            ):
                raise ValueError(
                    f"Artifact output {spec.ref()!r} declares incompatible "
                    "source-stack axes: "
                    f"{tuple(axes.as_tuple() for axes in source_stack_axes)!r}."
                )
            result[output_ref] = ArtifactOutputPlan(
                name=key,
                path=str(path),
                artifact_type=spec.artifact_type,
                materialization=(
                    ArtifactOutputMaterializationPlanner.materialization_for(
                        spec,
                        self.planner.future_artifact_inputs[sid],
                    )
                ),
                viewer_streaming=spec.viewer_streaming,
                sidecar_role=spec.sidecar_role,
                relations=spec.relations,
                group_scope_sources_by_group=(
                    self.output_group_scope_sources_by_group(
                        spec,
                        group_scope,
                        relation_source_scopes,
                    )
                ),
                group_keys=tuple(normalized_groups),
                group_component=group_scope.component,
                variable_components=(
                    source_stack_axes[0].as_tuple() if source_stack_axes else ()
                ),
                component_domains=component_domains,
                paths_by_group=paths_by_group,
                producer_step_index=sid,
                producer_step_scope_id=self.planner.plans[sid].step_scope_id,
                producer_step_name=step_name,
            )
            self.planner.declared[output_ref] = result[output_ref]

        return result

    def process_artifact_inputs(
        self,
        declarations: ArtifactGraph,
        sid: int,
        consumer_scope: PathPlannerGroupScope,
        source_bindings: SourceBindingDeclarationsMixin,
        variable_components: ComponentSet,
        step_name: Optional[str] = None,
        *,
        execution_scope: FunctionStepExecutionScope,
    ) -> dict[ArtifactSpecRef, ArtifactInputPlan]:
        """Compile storage plans for artifacts consumed by this step."""
        result: dict[ArtifactSpecRef, ArtifactInputPlan] = {}
        if not declarations.consumers:
            return result

        step_outputs = declarations.outputs
        consumers = sorted(
            declarations.consumers,
            key=lambda consumer: consumer.spec.name,
        )
        for consumer in consumers:
            input_spec = consumer.spec
            input_ref = input_spec.ref()
            key = input_spec.name
            producer_ref = input_ref.for_plan_type(ArtifactOutputPlan)
            if producer_ref in self.planner.declared:
                result[input_ref] = self._producer_artifact_input_plan(
                    producer_ref,
                    input_spec,
                    sid,
                    step_name,
                )
            elif producer_ref in step_outputs:
                output_spec = step_outputs[producer_ref]
                if output_spec.sidecar_role is not input_spec.sidecar_role:
                    raise ValueError(
                        f"Artifact '{key}' is produced with sidecar role "
                        f"{output_spec.sidecar_role!r} but consumed with "
                        f"{input_spec.sidecar_role!r} in step '{step_name or sid}'."
                    )
                result[input_ref] = ArtifactInputPlan(
                    name=key,
                    path=str(
                        self.planner.paths.artifact_path(
                            declarations.require_output_storage_key(producer_ref),
                            sid,
                            execution_scope=execution_scope,
                        )
                    ),
                    artifact_type=input_spec.artifact_type,
                    sidecar_role=input_spec.sidecar_role,
                    relations=output_spec.relations,
                    group_keys=consumer_scope.keys,
                    group_component=consumer_scope.component,
                    variable_components=variable_components.as_tuple(),
                    source_step_id=sid,
                    source_step_scope_id=self.planner.plans[sid].step_scope_id,
                )
            elif source_bindings.binding_for_artifact_ref(input_spec.ref()) is not None:
                continue
            elif (
                self.planner.artifact_context.main_flow_artifacts.by_ref(input_ref)
                is not None
            ):
                continue
            elif not self.planner.ctx.microscope_handler.can_resolve_metadata_artifact(
                key
            ):
                raise MissingArtifactInputError(
                    step_id=sid,
                    artifact_key=key,
                    step_name=step_name,
                )

        return result

    def _producer_artifact_input_plan(
        self,
        producer_ref: ArtifactSpecRef,
        input_spec: ArtifactSpec,
        sid: int,
        step_name: Optional[str],
    ) -> ArtifactInputPlan:
        producer = self.planner.declared[producer_ref]
        key = input_spec.name
        if producer.artifact_type != input_spec.artifact_type:
            producer_name = self._producer_artifact_display_name(producer)
            consumer_name = self._consumer_step_display_name(step_name, sid)
            raise ValueError(
                f"Artifact input '{key}' in step '{consumer_name}' expects "
                f"{input_spec.artifact_type.value}, but producer step '{producer_name}' "
                f"provides {producer.artifact_type.value}."
            )
        if producer.sidecar_role is not input_spec.sidecar_role:
            producer_name = self._producer_artifact_display_name(producer)
            consumer_name = self._consumer_step_display_name(step_name, sid)
            raise ValueError(
                f"Artifact input '{key}' in step '{consumer_name}' expects "
                f"sidecar role {input_spec.sidecar_role!r}, but producer step "
                f"'{producer_name}' provides {producer.sidecar_role!r}."
            )
        producer_scope = PathPlannerGroupScope.from_output_plan(producer)
        producer_paths_by_group = self._producer_artifact_paths_by_group(producer)

        return ArtifactInputPlan(
            name=key,
            path=self._producer_artifact_input_path(
                producer,
                producer_scope,
                producer_paths_by_group,
            ),
            artifact_type=producer.artifact_type,
            sidecar_role=input_spec.sidecar_role,
            relations=producer.relations,
            paths_by_group=producer_paths_by_group,
            group_keys=producer_scope.keys,
            group_component=producer_scope.component,
            variable_components=producer.variable_components,
            component_domains=producer.component_domains,
            source_step_id=producer.producer_step_index,
            source_step_scope_id=producer.producer_step_scope_id,
        )

    @staticmethod
    def _producer_artifact_display_name(
        producer: ArtifactOutputPlan,
    ) -> PathPlannerStepDisplayName:
        if producer.producer_step_name is not None:
            return producer.producer_step_name
        if producer.producer_step_index is not None:
            return producer.producer_step_index
        return "unknown"

    @staticmethod
    def _consumer_step_display_name(
        step_name: Optional[str],
        sid: int,
    ) -> PathPlannerStepDisplayName:
        if step_name is not None:
            return step_name
        return sid

    @staticmethod
    def _producer_artifact_paths_by_group(
        producer: ArtifactOutputPlan,
    ) -> dict[Optional[str], str]:
        if producer.paths_by_group is None:
            return {}
        return dict(producer.paths_by_group)

    @staticmethod
    def _producer_artifact_input_path(
        producer: ArtifactOutputPlan,
        producer_scope: PathPlannerGroupScope,
        paths_by_group: Mapping[str | None, str],
    ) -> str:
        producer_group = producer_scope.single_group_key()
        if producer_group is not None:
            return paths_by_group.get(producer_group, producer.path)
        return producer.path


@dataclass(frozen=True)
class PathPlannerMaterializationStage:
    """Input conversion and materialized-output planning stage."""

    planner: PathPlanner

    def materialized_output_dir_for_step(
        self,
        step: AbstractStep,
        step_index: int,
    ) -> Optional[Path]:
        """Resolve optional per-step materialization output directory."""
        materialization_config = step.step_materialization_config
        if not materialization_config or not materialization_config.enabled:
            return None

        step_axis_filters = self.planner.ctx.step_axis_filters.get(
            step_index,
            StepAxisFilterSet.empty(),
        )
        if not step_axis_filters.allows(materialization_config, self.planner.ctx.axis_id):
            logger.debug(
                "Skipping materialization for step %s, axis %s (filtered out)",
                step.name,
                self.planner.ctx.axis_id,
            )
            return None

        return self.planner.paths.build_output_path(materialization_config)

    def input_conversion_plan_for_step(
        self,
        step_index: int,
        input_dir: Path,
    ) -> Optional[InputConversionPlan]:
        """Resolve optional compiler-provided or config-provided input conversion."""
        existing_plan = self.planner.plans[step_index].input_conversion
        if existing_plan is not None:
            return existing_plan

        output_dir = self.planner.paths.input_conversion_output_path(step_index)
        if output_dir is None:
            return None

        return InputConversionPlan(
            output_dir=output_dir,
            backend=self.planner.vfs.materialization_backend.value,
            uses_virtual_workspace=False,
            original_subdir=input_dir.name,
        )

    def apply_materialization_plan(
        self,
        step: AbstractStep,
        step_index: int,
        materialized_output_dir: Optional[Path],
    ) -> None:
        """Attach optional materialization path fields to a step plan."""
        if not materialized_output_dir:
            return

        materialization_config = step.step_materialization_config
        materialized_plate_root = self.planner.paths.build_output_plate_root(
            self.planner.plate_path,
            materialization_config,
            is_per_step_materialization=False,
        )
        self.planner.plans[step_index].materialized_output = MaterializedOutputPlan(
            output_dir=materialized_output_dir,
            backend=self.planner.vfs.materialization_backend.value,
            plate_root=str(materialized_plate_root),
            sub_dir=materialization_config.sub_dir,
            analysis_results_dir=str(
                self.planner.paths.analysis_results_dir_for(materialized_output_dir)
            ),
        )
        self.planner.plans[step_index].materialization_config = materialization_config

    def apply_input_conversion_plan(
        self,
        step_index: int,
        input_conversion_plan: Optional[InputConversionPlan],
    ) -> None:
        """Attach optional input conversion path fields to a step plan."""
        if input_conversion_plan is None:
            return

        self.planner.plans[step_index].input_conversion = input_conversion_plan


@dataclass(frozen=True)
class PathPlannerValidationStage:
    """Connectivity and materialization path validation stage."""

    planner: PathPlanner

    def validate(self) -> None:
        """Validate connectivity and materialization paths."""
        for i in range(1, self.planner.session.step_count):
            curr = self.planner.session.pipeline.steps[i]
            dependency = self.planner.plans[i].main_input_dependency
            if dependency.kind in (
                StepInputDependencyKind.NO_MAIN_FLOW,
                StepInputDependencyKind.PIPELINE_START,
            ):
                continue
            if dependency.kind is not StepInputDependencyKind.STEP_OUTPUT:
                raise ValueError(f"Step {curr.name} has unresolved main input dependency.")
            source_step_index = dependency.source_step_index
            if source_step_index is None:
                raise ValueError(
                    f"Step {curr.name} main input dependency is missing source_step_index."
                )
            curr_in = self.planner.plans[i].input_dir
            source_out = self.planner.plans[source_step_index].output_dir
            if curr_in != source_out:
                has_artifact_bridge = any(
                    inp.source_step_id in [source_step_index, "prev"]
                    or inp.source_step_scope_id == dependency.source_step_scope_id
                    for inp in self.planner.plans[i].artifact_inputs.values()
                )
                if not has_artifact_bridge:
                    producer_name = self.planner.session.pipeline.steps[
                        source_step_index
                    ].name
                    raise ValueError(f"Disconnect: {producer_name} -> {curr.name}")

        self.validate_materialization_paths()

    def validate_materialization_paths(self) -> None:
        """Validate and resolve materialization path collisions."""
        global_path = self.planner.paths.build_output_path(self.planner.cfg)

        mat_steps = [
            (
                step,
                self.planner.plans[i].pipeline_position or i,
                self.planner.paths.build_output_path(step.step_materialization_config),
            )
            for i, step in enumerate(self.planner.session.pipeline.steps)
            if step.step_materialization_config and step.step_materialization_config.enabled
        ]

        path_groups = defaultdict(list)
        for step, pos, path in mat_steps:
            if path == global_path:
                self.resolve_and_update_paths(step, pos, path, "main flow")
            else:
                path_groups[str(path)].append((step, pos, path))

        for path_key, step_list in path_groups.items():
            if len(step_list) > 1:
                for step, pos, path in step_list:
                    self.resolve_and_update_paths(step, pos, path, f"pos {pos}")

    def resolve_and_update_paths(
        self,
        step: AbstractStep,
        position: int,
        original_path: Path,
        conflict_type: str,
    ) -> None:
        """Resolve path conflict by updating the compiled plan only."""
        del original_path, conflict_type
        materialization_config = step.step_materialization_config

        original_sub_dir = materialization_config.sub_dir
        new_sub_dir = f"{original_sub_dir}_step{position}"

        from dataclasses import replace

        updated_config = replace(materialization_config, sub_dir=new_sub_dir)

        resolved_path = self.planner.paths.build_output_path(updated_config)
        resolved_analysis_results_dir = self.planner.paths.analysis_results_dir_for(
            resolved_path
        )

        if step_plan := self.planner.plans.get(position):
            if step_plan.materialized_output is not None:
                step_plan.materialized_output = MaterializedOutputPlan(
                    output_dir=resolved_path,
                    backend=step_plan.materialized_output.backend,
                    plate_root=step_plan.materialized_output.plate_root,
                    sub_dir=new_sub_dir,
                    analysis_results_dir=str(resolved_analysis_results_dir),
                )
                step_plan.materialization_config = updated_config


@dataclass(frozen=True)
class PathPlannerPathAuthority:
    """Path and grouped-artifact expansion authority for compiled step plans."""

    planner: PathPlanner

    @staticmethod
    def build_output_plate_root(
        plate_path: Path,
        path_config,
        is_per_step_materialization: bool = False,
    ) -> Path:
        """Build output plate root directory directly from configuration components.

        Results always use the output plate path so metadata remains colocated with
        processed images instead of the original input images.
        """
        del is_per_step_materialization

        if not path_config.output_dir_suffix:
            raise ValueError(
                f"output_dir_suffix cannot be None or empty. "
                f"Results must always use output plate path, not input plate path. "
                f"Config: {path_config}"
            )

        return Path(
            _cached_output_plate_root(
                str(plate_path),
                (
                    None
                    if path_config.global_output_folder is None
                    else str(path_config.global_output_folder)
                ),
                path_config.output_dir_suffix,
            )
        )

    @staticmethod
    def paths_by_group(
        base_path: str,
        group_keys: List[Optional[str]],
    ) -> Dict[Optional[str], str]:
        """Expand one artifact path into per-execution-group artifact paths."""
        return dict(_cached_paths_by_group(base_path, tuple(group_keys)))

    @staticmethod
    def analysis_results_dir_for(image_dir: Path) -> Path:
        """Return the analysis-results sibling directory for an image directory."""
        return Path(_cached_analysis_results_dir_for(str(image_dir)))

    def build_output_path(
        self,
        path_config: PathPlanningConfig | None = None,
    ) -> Path:
        """Build complete output path: plate_root + sub_dir."""
        config = path_config or self.planner.cfg
        if not config.output_dir_suffix:
            raise ValueError(
                f"output_dir_suffix cannot be None or empty. "
                f"Results must always use output plate path, not input plate path. "
                f"Config: {config}"
            )
        return Path(
            _cached_output_path(
                str(self.planner.plate_path),
                (
                    None
                    if config.global_output_folder is None
                    else str(config.global_output_folder)
                ),
                config.output_dir_suffix,
                config.sub_dir,
            )
        )

    def input_conversion_output_path(self, step_index: int) -> Optional[Path]:
        """Get input conversion output path if config exists."""
        config = self.planner.plans[step_index].input_conversion_config
        if config is not None:
            return self.build_output_path(config)
        return None

    def results_path(self) -> Path:
        """Get analysis results path from global pipeline configuration."""
        path = self.planner.session.global_config.materialization_results_path
        if not self.planner.cfg.output_dir_suffix:
            raise ValueError(
                f"output_dir_suffix cannot be None or empty. "
                f"Results must always use output plate path, not input plate path. "
                f"Config: {self.planner.cfg}"
            )
        return Path(
            _cached_results_path(
                str(self.planner.plate_path),
                (
                    None
                    if self.planner.cfg.global_output_folder is None
                    else str(self.planner.cfg.global_output_folder)
                ),
                self.planner.cfg.output_dir_suffix,
                str(path),
            )
        )

    def artifact_path(
        self,
        name: str,
        step_index: int,
        *,
        execution_scope: FunctionStepExecutionScope,
    ) -> Path:
        """Return the canonical storage path for one compiled artifact output."""

        filename = (
            f"{name}_step{step_index}.pkl"
            if execution_scope is FunctionStepExecutionScope.PLATE
            else PipelinePathPlanner._build_axis_filename(
                self.planner.ctx.axis_id,
                name,
                step_index=step_index,
            )
        )
        return self.results_path() / filename


@dataclass(frozen=True)
class PathPlannerStepAssemblyStage:
    """Per-step dependency, directory, and compiled-plan assembly stage."""

    planner: PathPlanner

    def plan_step(self, step: AbstractStep, step_index: int) -> None:
        """Plan one step's directories, artifacts, and executable pattern."""
        self.planner.plans[step_index].step_scope_id = (
            self.planner.session.pipeline.step_scope_ids[step_index]
        )
        pipeline = self.planner.session.pipeline
        self.planner.artifact_context = pipeline.artifact_contexts[step_index]
        declarations = pipeline.artifact_graphs[step_index]
        func_pattern = declarations.pattern
        contracts = (
            () if func_pattern is None
            else tuple(item.contract for item in func_pattern.iter_items())
        )
        execution_scope = FunctionStepExecutionScope.require_uniform(contracts)
        main_input_dependency = declarations.main_input_dependency
        contract_source_bindings = declarations.source_binding_plan
        if contract_source_bindings.binding_declarations:
            fields = step.source_bindings.metadata_fields_for_literal_types(
                self.planner.session.source_literal_field_types
            )
            if fields != contract_source_bindings.metadata_fields:
                contract_source_bindings = replace(
                    contract_source_bindings, metadata_fields=fields
                )
        input_component_scopes = self.input_component_scopes(main_input_dependency)
        input_dir, output_dir = self.step_io_dirs(main_input_dependency, step_index)
        group_scope = (
            PathPlannerGroupScope.ungrouped()
            if execution_scope is FunctionStepExecutionScope.PLATE
            else self.planner.execution_groups.get_execution_groups(
                step,
                input_component_scopes,
                source_bindings=contract_source_bindings,
                contracts=contracts,
            )
        )
        artifact_maps = self.planner.artifacts.compile_plan_maps(
            step,
            step_index,
            declarations,
            group_scope,
            execution_scope,
            contract_source_bindings,
        )

        if isinstance(step, FunctionStep):
            func_pattern = self.planner.artifacts.inject_metadata(
                func_pattern,
                declarations.inputs,
            )

        self.planner.plans[step_index].func = func_pattern
        compiled_pattern = self.planner.artifacts.build_step_compiled_function_pattern(
            step,
            step_index,
            isinstance(step, FunctionStep),
            func_pattern,
            artifact_maps.inputs,
            artifact_maps.outputs,
            artifact_maps.relation_source_scopes,
            artifact_maps.group_scope,
            declarations,
        )
        self.update_core_step_plan(
            step,
            step_index,
            main_input_dependency,
            input_dir,
            output_dir,
            artifact_maps,
            compiled_pattern,
        )
        self.planner.materialization.apply_materialization_plan(
            step,
            step_index,
            self.planner.materialization.materialized_output_dir_for_step(step, step_index),
        )
        self.planner.materialization.apply_input_conversion_plan(
            step_index,
            self.planner.materialization.input_conversion_plan_for_step(
                step_index,
                input_dir,
            ),
        )
        self.planner.main_flow_component_scopes[step_index] = (
            input_component_scopes.output_after(
                step,
                artifact_maps.group_scope,
                compiled_pattern,
            )
        )

    def input_component_scopes(
        self,
        main_input_dependency: StepInputDependency,
    ) -> PathPlannerComponentScopes:
        """Return component scopes visible on a step's main-flow input branch."""
        if main_input_dependency.kind is StepInputDependencyKind.PIPELINE_START:
            return PathPlannerComponentScopes.empty()
        source_step_index = main_input_dependency.source_step_index
        if source_step_index is None:
            return PathPlannerComponentScopes.empty()
        return self.planner.main_flow_component_scopes.get(
            source_step_index,
            PathPlannerComponentScopes.empty(),
        )

    def update_core_step_plan(
        self,
        step: AbstractStep,
        step_index: int,
        main_input_dependency: StepInputDependency,
        input_dir: Path,
        output_dir: Path,
        artifact_maps: ArtifactPlanMaps,
        compiled_function_pattern: CompiledFunctionPattern | None,
    ) -> None:
        """Write the always-present path and artifact planning fields."""
        main_plate_root = self.planner.paths.build_output_plate_root(
            self.planner.plate_path,
            self.planner.cfg,
            is_per_step_materialization=False,
        )
        step_plan = self.planner.plans[step_index]
        step_plan.input_dir = input_dir
        step_plan.output_dir = output_dir
        step_plan.output_plate_root = str(main_plate_root)
        step_plan.sub_dir = self.planner.cfg.sub_dir
        step_plan.analysis_results_dir = str(self.planner.paths.results_path())
        step_plan.pipeline_position = step_index
        step_plan.input_source = self.input_source(step)
        step_plan.group_by = PathPlannerExecutionGroups.normalized_group_by(step)
        step_plan.main_input_dependency = main_input_dependency
        step_plan.artifact_inputs = artifact_maps.inputs
        step_plan.artifact_outputs = artifact_maps.outputs
        step_plan.future_artifact_inputs = self.planner.future_artifact_inputs[step_index]
        step_plan.execution_group_scope = artifact_maps.group_scope
        step_plan.compiled_function_pattern = compiled_function_pattern
        step_plan.source_binding_plan = artifact_maps.source_binding_plan
        step_plan.source_universe_plan = artifact_maps.source_universe_plan

    def main_input_dependency(
        self,
        step: AbstractStep,
        step_index: int,
        *,
        declarations: ArtifactGraph = ArtifactGraph(),
        execution_scope: FunctionStepExecutionScope = FunctionStepExecutionScope.AXIS,
        source_bindings: StepSourceBindingsConfig | CompiledSourceBindingPlan = EMPTY_SOURCE_BINDINGS,
    ) -> StepInputDependency:
        """Resolve the explicit main-input edge for one step."""
        existing_plan = self.planner.plans.get(step_index)
        if existing_plan is not None and existing_plan.main_input_dependency.is_resolved:
            return existing_plan.main_input_dependency

        previous = self.planner.plans.get(step_index - 1)
        return declarations.resolve_main_input_dependency(
            step,
            step_index,
            execution_scope=execution_scope,
            source_bindings=source_bindings,
            context=self.planner.artifact_context,
            declared=self.planner.declared,
            step_scope_ids={
                index: plan.step_scope_id for index, plan in self.planner.plans.items()
            },
            previous_dependency=(
                None if previous is None else previous.main_input_dependency
            ),
            previous_preserves_input_main_flow=(
                previous is not None
                and previous.compiled_function_pattern is not None
                and previous.compiled_function_pattern.preserves_input_main_flow()
            ),
        )

    def step_io_dirs(
        self,
        main_input_dependency: StepInputDependency,
        step_index: int,
    ) -> tuple[Path, Path]:
        """Resolve read/write directories for one step."""
        plan = self.planner.plans.get(step_index)
        reads_from_pipeline_start = (
            main_input_dependency.kind is StepInputDependencyKind.PIPELINE_START
        )
        has_no_main_flow = (
            main_input_dependency.kind is StepInputDependencyKind.NO_MAIN_FLOW
        )

        if plan is not None and plan.input_dir is not None:
            input_dir = Path(plan.input_dir)
        elif reads_from_pipeline_start:
            input_dir = self.planner.initial_input
        elif has_no_main_flow:
            input_dir = self.planner.paths.build_output_path()
        else:
            source_step_index = main_input_dependency.source_step_index
            if source_step_index is None:
                raise ValueError(
                    f"Step {step_index} main input dependency is missing source_step_index."
                )
            input_dir = Path(self.planner.plans[source_step_index].output_dir)

        if plan is not None and plan.output_dir is not None:
            output_dir = Path(plan.output_dir)
        elif reads_from_pipeline_start or has_no_main_flow:
            output_dir = self.planner.paths.build_output_path()
        else:
            output_dir = input_dir

        return input_dir, output_dir

    @staticmethod
    def input_source(step: AbstractStep) -> str:
        """Get input source string."""
        if step.processing_config.input_source == InputSource.PIPELINE_START:
            return "PIPELINE_START"
        return "PREVIOUS_STEP"


# ===== PATH PLANNING (NO duplication) =====


class PathPlanner:
    """Minimal path planner with zero duplication."""

    def __init__(
        self,
        session: CompilationSession,
    ):
        self.session = session
        self.ctx = session.context
        self.cfg = session.global_config.path_planning_config
        self.vfs = session.global_config.vfs_config
        self.plans: dict[int, CompiledStepPlan] = session.plans
        self.declared: dict[ArtifactSpecRef, ArtifactOutputPlan] = {}
        self.orchestrator = session.orchestrator
        self.future_artifact_inputs = session.pipeline.future_artifact_inputs
        self.artifact_context = ArtifactDeclarationStepContext.empty()
        self.main_flow_component_scopes: dict[int, PathPlannerComponentScopes] = {}
        self.execution_groups = PathPlannerExecutionGroups(self)
        self.paths = PathPlannerPathAuthority(self)
        self.artifacts = PathPlannerArtifactStage(self)
        self.materialization = PathPlannerMaterializationStage(self)
        self.validation = PathPlannerValidationStage(self)
        self.steps = PathPlannerStepAssemblyStage(self)

        # Initial input determination (once)
        self.initial_input = Path(self.ctx.input_dir)
        self.plate_scope = CompilationPlateScope.from_context(self.ctx)
        self.plate_path = self.plate_scope.path

    def plan(self) -> dict[int, CompiledStepPlan]:
        """Plan all paths with zero duplication."""
        for i, step in enumerate(self.session.pipeline.steps):
            self.steps.plan_step(step, i)

        self.validation.validate()

        # Set output_plate_root and sub_dir for metadata writing
        if self.session.step_count:
            self.ctx.output_plate_root = self.paths.build_output_plate_root(
                self.plate_path,
                self.cfg,
                is_per_step_materialization=False,
            )
            self.ctx.sub_dir = self.cfg.sub_dir

        return self.plans


# ===== PUBLIC API =====


class PipelinePathPlanner:
    """Public API matching original interface."""

    @staticmethod
    def prepare_pipeline_paths(
        session: CompilationSession,
    ) -> Dict:
        """Prepare path plans for an already resolved compilation session."""
        return PathPlanner(session).plan()

    @staticmethod
    def build_output_plate_root(
        plate_path: Path,
        path_config,
        is_per_step_materialization: bool = False,
    ) -> Path:
        """Build output plate root from configuration components."""
        return PathPlannerPathAuthority.build_output_plate_root(
            plate_path,
            path_config,
            is_per_step_materialization=is_per_step_materialization,
        )

    @staticmethod
    def _build_axis_filename(
        axis_id: str, key: str, extension: str = "pkl", step_index: Optional[int] = None
    ) -> str:
        """Build standardized axis-based filename with optional step index.

        Args:
            axis_id: Well/axis identifier (e.g., "R02C02")
            key: Artifact output key (e.g., "match_results")
            extension: File extension (default: "pkl")
            step_index: Optional step index to prevent collisions when multiple steps
                       produce the same artifact output

        Returns:
            Filename string (e.g., "R02C02_match_results_step3.pkl")
        """
        return _cached_axis_filename(axis_id, key, extension, step_index)

    @staticmethod
    def build_dict_pattern_path(base_path: str, dict_key: str) -> str:
        """Build channel-specific path for dict patterns.

        Inserts _w{dict_key} after well ID in the filename.
        Example: "dir/A01_rois_step7.pkl" + "1" -> "dir/A01_w1_rois_step7.pkl"

        Args:
            base_path: Base path without channel component
            dict_key: Dict pattern key (e.g., "1" for channel 1)

        Returns:
            Channel-specific path
        """
        return _cached_dict_pattern_path(base_path, dict_key)


@lru_cache(maxsize=65536)
def _cached_output_plate_root(
    plate_path: str,
    global_output_folder: str | None,
    output_dir_suffix: str,
) -> str:
    """Return the output plate root for one normalized path config."""
    path = Path(plate_path)
    if plate_path.startswith("/omero/"):
        base = path.parent
    elif global_output_folder:
        base = Path(global_output_folder)
        if not base.is_absolute():
            raise ValueError(
                "PathPlanner requires compiled global_output_folder to be "
                f"absolute, got {global_output_folder!r}."
            )
    else:
        base = path.parent
    return str(base / f"{path.name}{output_dir_suffix}")


@lru_cache(maxsize=65536)
def _cached_output_path(
    plate_path: str,
    global_output_folder: str | None,
    output_dir_suffix: str,
    sub_dir: str,
) -> str:
    """Return the configured image output path for one normalized path config."""
    return str(
        Path(
            _cached_output_plate_root(
                plate_path,
                global_output_folder,
                output_dir_suffix,
            )
        )
        / sub_dir
    )


@lru_cache(maxsize=65536)
def _cached_results_path(
    plate_path: str,
    global_output_folder: str | None,
    output_dir_suffix: str,
    materialization_results_path: str,
) -> str:
    """Return the artifact results path for one normalized path config."""
    results_path = Path(materialization_results_path)
    output_plate_root = Path(
        _cached_output_plate_root(
            plate_path,
            global_output_folder,
            output_dir_suffix,
        )
    )
    results_path = (output_plate_root / results_path).resolve()
    try:
        relative_results = results_path.relative_to(output_plate_root.resolve())
    except ValueError as error:
        raise ValueError(
            "materialization_results_path must be inside the output plate root "
            f"{output_plate_root}; got {results_path}."
        ) from error
    # Preserve the compiled plate spelling, including a symlinked ancestor:
    # persistence projects addresses relative to that same lexical authority.
    return str(output_plate_root / relative_results)


@lru_cache(maxsize=131072)
def _cached_axis_filename(
    axis_id: str,
    key: str,
    extension: str,
    step_index: int | None,
) -> str:
    """Return the standard artifact filename for one axis/output/step."""
    if step_index is not None:
        return f"{axis_id}_{key}_step{step_index}.{extension}"
    return f"{axis_id}_{key}.{extension}"


@lru_cache(maxsize=65536)
def _cached_dict_pattern_path(base_path: str, dict_key: str) -> str:
    """Return the grouped artifact path for one base path and group key."""
    return grouped_artifact_path(base_path, dict_key)


@lru_cache(maxsize=32768)
def _cached_paths_by_group(
    base_path: str,
    group_keys: tuple[str | None, ...],
) -> tuple[tuple[str | None, str], ...]:
    """Return immutable grouped-path items for cache-safe reuse."""
    return tuple(
        (
            group_key,
            (
                base_path
                if group_key is None
                else _cached_dict_pattern_path(base_path, group_key)
            ),
        )
        for group_key in group_keys
    )


@lru_cache(maxsize=8192)
def _cached_analysis_results_dir_for(image_dir: str) -> str:
    """Return cached analysis-results sibling path for one image directory."""
    path = Path(image_dir)
    return str(path.parent / f"{path.name}_results")
