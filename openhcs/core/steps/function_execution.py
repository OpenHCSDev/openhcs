"""Compiled-plan orchestration for FunctionStep."""

from __future__ import annotations

import logging
import time
import traceback
from collections.abc import Callable, Mapping, Sequence
from itertools import zip_longest
from typing import TYPE_CHECKING

from openhcs.constants import MULTIPROCESSING_AXIS
from openhcs.constants.constants import (
    LOADABLE_IMAGE_EXTENSIONS,
    Backend,
)
from openhcs.core.component_set import ComponentSet
from openhcs.core.component_group_scope import (
    ComponentGroupScope,
    RuntimeExecutionAxisScope,
)
from openhcs.core.runtime_stores import RuntimeArtifactInput
from openhcs.core.runtime_profile import RuntimeProfileLogger, RuntimeProfileFieldValue
from openhcs.core.callable_contract import ImagePayloadConsumption
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.function_patterns import (
    CompiledFunctionGroup,
    FunctionGroupKey,
    GroupedPatternMap,
    InvocationArtifactInputEdgePlan,
    RuntimeInvocationDomain,
)
from openhcs.core.progress import ProgressPhase, ProgressStatus, emit
from openhcs.core.runtime_pattern_cache import RuntimePatternDiscoveryCacheKey
from openhcs.core.source_binding_selection import (
    SourceBoundAnchorPatternPolicy,
    SourceCandidatePath,
    SourcePatternResolutionContext,
)
from openhcs.core.source_bindings import CompiledSourceBindingPlan
from openhcs.core.step_dependencies import StepInputDependencyKind
from openhcs.core.steps.function_io import (
    generate_materialized_paths,
    get_all_image_paths,
    save_materialized_data,
    update_metadata_for_zarr_conversion,
)
from openhcs.core.steps.function_output_manifest import (
    NoStepOutputManifestMatch,
    step_output_manifest,
)
from openhcs.core.steps.abstract import StepExecutionObservation
from openhcs.core.steps.function_outputs import finalize_function_step_outputs
from openhcs.core.steps.function_runtime import (
    ArtifactPatternGroupExecutionRequest,
    PatternGroupExecutionRequest,
    _process_single_pattern_group,
)
from openhcs.formats.pattern.pattern_discovery import PatternDiscoveryEngine

if TYPE_CHECKING:
    from openhcs.microscopes.microscope_interfaces import FilenameParser


logger = logging.getLogger(__name__)
RuntimeProfileExtraFields = Mapping[str, RuntimeProfileFieldValue] | None
DiscoveredPatternCollection = (
    Sequence[SourceCandidatePath]
    | Mapping[FunctionGroupKey, Sequence[SourceCandidatePath]]
)
AnchorPatternSelector = Callable[
    [FunctionGroupKey, tuple[SourceCandidatePath, ...]],
    Sequence[SourceCandidatePath],
]


def _single_execution_group_patterns(
    patterns: DiscoveredPatternCollection,
) -> Sequence[SourceCandidatePath]:
    """Flatten discovered source groups when the planner chose no execution axis."""
    if not isinstance(patterns, dict):
        return patterns
    return tuple(
        pattern for pattern_list in patterns.values() for pattern in pattern_list
    )


def _filter_patterns_by_component(
    patterns: DiscoveredPatternCollection,
    component: str,
    target_value: str,
    parser: FilenameParser,
) -> DiscoveredPatternCollection:
    """Filter pattern strings by a fixed parsed component value."""

    def filter_pattern_list(
        pattern_list: Sequence[SourceCandidatePath],
    ) -> list[SourceCandidatePath]:
        filtered: list[SourceCandidatePath] = []
        component_declaration = parser.component_for_name(component)
        for pattern in pattern_list:
            metadata = parser.parse_filename(str(pattern))
            if metadata and str(metadata.value_for(component_declaration)) == str(
                target_value
            ):
                filtered.append(pattern)
        return filtered

    if isinstance(patterns, dict):
        filtered_by_group = {}
        for group_key, pattern_list in patterns.items():
            filtered_list = filter_pattern_list(pattern_list)
            if filtered_list:
                filtered_by_group[group_key] = filtered_list
        return filtered_by_group

    return filter_pattern_list(patterns)


class FunctionStepExecutor:
    """Run one compiled FunctionStep plan for one multiprocessing axis."""

    def __init__(self, context: ProcessingContext, step_index: int) -> None:
        self.context = context
        compiled_plan = context.step_plans[step_index]
        if not isinstance(compiled_plan, CompiledStepPlan):
            raise TypeError(
                f"FunctionStep {step_index} requires CompiledStepPlan, got "
                f"{type(compiled_plan).__name__}."
            )
        self.plan = compiled_plan.require_function_execution_ready()

    def _execution_requests(
        self,
        grouped_patterns: GroupedPatternMap,
    ) -> tuple[PatternGroupExecutionRequest, ...]:
        """Admit source anchors to their complete compiled execution coordinates."""

        plan = self.plan
        requests = []
        for component_index, (component_value, patterns) in enumerate(
            grouped_patterns.items()
        ):
            compiled_group = plan.compiled_function_pattern.group_for_component(
                component_value
            )
            if compiled_group is None:
                raise ValueError(
                    f"No compiled function group for component {component_value!r}."
                )
            requests.extend(
                PatternGroupExecutionRequest(
                    context=self.context,
                    execution_plan=plan,
                    pattern_group_info=pattern,
                    compiled_group=compiled_group,
                    component_value=component_value,
                    component_index=component_index,
                    component_count=len(grouped_patterns),
                )
                for pattern in patterns
            )
        return tuple(requests)

    def _filter_anchor_patterns(
        self, grouped_patterns: GroupedPatternMap
    ) -> GroupedPatternMap:
        grouped_patterns = self.source_bound_anchor_patterns(grouped_patterns)
        grouped_patterns = self.producer_anchor_patterns(grouped_patterns)
        grouped_patterns = self.execution_group_anchor_patterns(grouped_patterns)
        grouped_patterns = self.plan.compiled_function_pattern.prepare_grouped_patterns(
            grouped_patterns,
            default_component=self.plan.execution_group_value,
        )
        return self.artifact_driven_anchor_patterns(grouped_patterns)

    def execution_group_anchor_patterns(
        self,
        grouped_patterns: GroupedPatternMap,
    ) -> GroupedPatternMap:
        """Map validated lifecycle anchors onto compiler-owned execution groups."""

        pattern = self.plan.compiled_function_pattern
        source_owns_groups = (
            pattern.runtime_domain is RuntimeInvocationDomain.SOURCE_ANCHORED
        )
        if not grouped_patterns:
            return grouped_patterns

        if source_owns_groups:
            producer_groups = step_output_manifest(
                self.context
            ).producer_patterns_by_execution_group(
                self.plan,
                tuple(
                    pattern
                    for patterns in grouped_patterns.values()
                    for pattern in patterns
                ),
                self.context.microscope_handler.parser,
            )
            if producer_groups is not None:
                return {
                    key: tuple(patterns) for key, patterns in producer_groups.items()
                }
            execution_scope = self.plan.execution_group_scope
            return {
                group_key: pattern_list
                for group_key, pattern_list in grouped_patterns.items()
                if execution_scope.contains_runtime_key(group_key)
            }

        execution_group_keys = self.plan.execution_group_scope.runtime_keys(
            grouped_patterns
        )
        canonical_anchors = next(
            (
                pattern_list
                for pattern_list in grouped_patterns.values()
                if pattern_list
            ),
            (),
        )
        return {
            group_key: grouped_patterns.get(group_key) or canonical_anchors
            for group_key in execution_group_keys
        }

    def source_bound_anchor_patterns(
        self,
        grouped_patterns: GroupedPatternMap,
    ) -> GroupedPatternMap:
        """Restrict source-bound step anchors to compatible declared sources."""

        if not self.plan.main_input_dependency.uses_pipeline_start_anchors():
            return grouped_patterns
        if not self.plan.source_binding_plan.has_primary_content:
            return grouped_patterns

        policy = SourceBoundAnchorPatternPolicy.for_plan(self.plan.source_binding_plan)
        source_context = self.source_pattern_context()
        compiled_pattern = self.plan.compiled_function_pattern

        declared_source_refs = frozenset(
            binding.input_spec().ref()
            for binding in self.plan.source_binding_plan.binding_declarations
        )
        compiled_outputs = (
            tuple(
                output_plan
                for invocation in compiled_pattern.default_group.invocations
                for output_plan in invocation.artifact_output_plans
            )
            if not compiled_pattern.is_grouped
            else ()
        )
        shared_source_set_output = (
            len(declared_source_refs) > 1
            and bool(compiled_outputs)
            and all(
                invocation.contract.image_payload_consumption
                is ImagePayloadConsumption.COMPOSED
                for invocation in compiled_pattern.default_group.invocations
            )
            and all(
                frozenset(output_plan.group_scope_sources()) == declared_source_refs
                for output_plan in compiled_outputs
            )
        )

        if not compiled_pattern.is_grouped and shared_source_set_output:
            candidate_occurrence_groups = tuple(
                tuple((component_value, pattern) for pattern in pattern_list)
                for component_value, pattern_list in grouped_patterns.items()
                if self.plan.execution_group_scope.contains_runtime_key(component_value)
            )
            candidate_occurrences = tuple(
                occurrence
                for source_set_occurrences in zip_longest(
                    *candidate_occurrence_groups,
                    fillvalue=None,
                )
                for occurrence in source_set_occurrences
                if occurrence is not None
            )
            selected_patterns = iter(
                policy.select(
                    tuple(
                        pattern for _component_value, pattern in candidate_occurrences
                    ),
                    bindings=self.plan.source_binding_plan.binding_declarations,
                    source_context=source_context,
                )
            )
            exhausted = object()
            selected_pattern = next(selected_patterns, exhausted)
            retained_by_group: dict[
                FunctionGroupKey,
                GroupedPatternMap,
                list[SourceCandidatePath],
            ] = {component_value: [] for component_value in grouped_patterns}
            for component_value, pattern in candidate_occurrences:
                if selected_pattern is exhausted:
                    break
                if pattern != selected_pattern:
                    continue
                retained_by_group[component_value].append(pattern)
                selected_pattern = next(selected_patterns, exhausted)
            if selected_pattern is not exhausted:
                raise ValueError(
                    "Source-bound anchor policy selected patterns outside the exact "
                    "candidate collection order."
                )

            def retain_selected(
                component_value: FunctionGroupKey,
                pattern_list: tuple[SourceCandidatePath, ...],
            ) -> Sequence[SourceCandidatePath]:
                del pattern_list
                return retained_by_group[component_value]

            return self.apply(
                "step_filter_source_anchors",
                grouped_patterns,
                retain_selected,
            )

        if not compiled_pattern.is_grouped:
            return self.default_source_bound_anchor_patterns(
                grouped_patterns,
                policy=policy,
                source_context=source_context,
            )

        def select_compatible(
            component_value: FunctionGroupKey,
            pattern_list: tuple[SourceCandidatePath, ...],
        ) -> Sequence[SourceCandidatePath]:
            if not self.plan.execution_group_scope.contains_runtime_key(
                component_value
            ):
                return ()
            compiled_group = self.plan.compiled_function_pattern.group_for_component(
                component_value
            )
            if compiled_group is None:
                return pattern_list
            bindings = self.source_anchor_bindings(
                compiled_group,
                component_value=component_value,
            )
            if bindings is None:
                return ()
            return policy.select(
                pattern_list,
                bindings=bindings.binding_declarations,
                source_context=source_context,
            )

        return self.apply(
            "step_filter_source_anchors",
            grouped_patterns,
            select_compatible,
        )

    def default_source_bound_anchor_patterns(
        self,
        grouped_patterns: GroupedPatternMap,
        *,
        policy: SourceBoundAnchorPatternPolicy,
        source_context: SourcePatternResolutionContext,
    ) -> GroupedPatternMap:
        """Project raw source anchors onto compiler-owned semantic groups."""

        execution_scope = self.plan.execution_group_scope
        target_keys = execution_scope.runtime_keys(grouped_patterns)
        all_candidates = tuple(
            pattern
            for pattern_list in grouped_patterns.values()
            for pattern in pattern_list
        )
        selected_groups: dict[
            FunctionGroupKey,
            GroupedPatternMap,
            Sequence[SourceCandidatePath],
        ] = {}
        for target_key in target_keys:
            bindings = self.source_anchor_bindings(
                self.plan.compiled_function_pattern.default_group,
                component_value=target_key,
            )
            local_candidates = grouped_patterns.get(target_key)
            requires_cross_group_resolution = (
                execution_scope.component is not None
                and target_key is not None
                and bindings is not None
                and bindings.requires_cross_group_candidate_resolution(
                    execution_scope.component,
                    str(target_key),
                )
            )
            candidates = (
                all_candidates
                if local_candidates is None or requires_cross_group_resolution
                else local_candidates
            )
            selected_groups[target_key] = (
                ()
                if bindings is None
                else tuple(
                    policy.select(
                        candidates,
                        bindings=bindings.binding_declarations,
                        source_context=source_context,
                    )
                )
            )

        filtered = selected_groups
        before_count = sum(map(len, grouped_patterns.values()))
        after_count = sum(map(len, filtered.values()))
        if before_count != after_count:
            self.record_runtime_profile(
                "step_filter_source_anchors",
                0.0,
                extra_fields={
                    "before": before_count,
                    "after": after_count,
                },
            )
        return filtered

    def source_anchor_bindings(
        self,
        compiled_group: CompiledFunctionGroup,
        *,
        component_value: FunctionGroupKey,
    ) -> CompiledSourceBindingPlan | None:
        """Return component-compatible main-flow declarations, if any."""

        main_flow_refs = compiled_group.main_flow_input_refs_for_component(
            self.plan.execution_group_scope,
            component_value,
        )
        if main_flow_refs == ():
            return None
        component_plan = self.plan.source_binding_plan.for_component_group(
            self.plan.execution_group_scope.component,
            component_value,
        )
        if main_flow_refs is None:
            return component_plan
        declared_main_flow_plan = self.plan.source_binding_plan.for_artifact_refs(
            main_flow_refs,
        )
        if not declared_main_flow_plan.binding_declarations:
            return None
        compatible_plan = component_plan.for_artifact_refs(main_flow_refs)
        return compatible_plan if compatible_plan.binding_declarations else None

    def producer_anchor_patterns(
        self,
        grouped_patterns: GroupedPatternMap,
    ) -> GroupedPatternMap:
        """Restrict previous-step anchors to the declared producer's files."""

        def select_producer_paths(
            component_value: FunctionGroupKey,
            pattern_list: tuple[SourceCandidatePath, ...],
        ) -> Sequence[SourceCandidatePath]:
            try:
                return step_output_manifest(self.context).filter_to_producer_paths(
                    self.plan,
                    tuple(pattern_list),
                    self.context.microscope_handler.parser,
                )
            except NoStepOutputManifestMatch:
                return ()

        return self.apply(
            "step_filter_producer_anchors",
            grouped_patterns,
            select_producer_paths,
        )

    def artifact_driven_anchor_patterns(
        self,
        grouped_patterns: GroupedPatternMap,
    ) -> GroupedPatternMap:
        """Select the lifecycle anchors required by each compiled runtime domain."""

        def select_lifecycle_anchors(
            component_value: FunctionGroupKey,
            pattern_list: tuple[SourceCandidatePath, ...],
        ) -> Sequence[SourceCandidatePath]:
            compiled_group = self.plan.compiled_function_pattern.group_for_component(
                component_value
            )
            if compiled_group is None:
                return pattern_list
            return compiled_group.runtime_domain.select_lifecycle_anchors(pattern_list)

        return self.apply(
            "step_filter_artifact_anchors",
            grouped_patterns,
            select_lifecycle_anchors,
        )

    def apply(
        self,
        label: str,
        grouped_patterns: GroupedPatternMap,
        selector: AnchorPatternSelector,
    ) -> GroupedPatternMap:
        filtered = {
            key: tuple(selector(key, patterns))
            for key, patterns in grouped_patterns.items()
        }
        before_count = sum(map(len, grouped_patterns.values()))
        after_count = sum(map(len, filtered.values()))
        if before_count != after_count:
            self.record_runtime_profile(
                label,
                0.0,
                extra_fields={
                    "before": before_count,
                    "after": after_count,
                },
            )
        return filtered

    def source_pattern_context(self) -> SourcePatternResolutionContext:
        """Return source-path context used to filter source-bound anchors."""

        projection = self.context.runtime_source_workspace_projection_authority.projection_or_empty()
        return self.context.runtime_source_binding_context_cache.source_pattern_context(
            parser=self.context.microscope_handler.parser,
            projection=self.context.runtime_source_workspace_projection_cache.filtered_by_axis(
                projection,
                axis_id=self.plan.axis_id,
            ),
            metadata_rules=self.plan.source_binding_plan.metadata_rules,
        )

    def record_runtime_profile(
        self,
        label: str,
        seconds: float,
        *,
        extra_fields: RuntimeProfileExtraFields = None,
    ) -> None:
        fields: dict[str, RuntimeProfileFieldValue] = {
            "step": self.plan.step_index,
            "step_name": self.plan.step_name,
        }
        if extra_fields is not None:
            fields.update(extra_fields)
        RuntimeProfileLogger.log(logger, label, seconds, **fields)

    @classmethod
    def execute(
        cls,
        context: ProcessingContext,
        step_index: int,
    ) -> StepExecutionObservation:
        step_name = f"step_{step_index}"
        try:
            executor = cls(context, step_index)
            step_name = executor.plan.step_name or step_name
            with context.runtime_step_scope():
                return executor.run()
        except Exception as error:
            full_traceback = traceback.format_exc()
            logger.error(
                "Error in FunctionStep %s (%s): %s",
                step_index,
                step_name,
                error,
                exc_info=True,
            )
            logger.error(
                "Full traceback for FunctionStep %s (%s):\n%s",
                step_index,
                step_name,
                full_traceback,
            )
            raise

    def artifact_execution_requests(
        self,
    ) -> tuple[ArtifactPatternGroupExecutionRequest, ...] | None:
        """Discover complete correlated cohorts from their compiled producers."""

        context = self.context
        plan = self.plan
        pattern = plan.compiled_function_pattern
        scope = plan.execution_group_scope

        def candidate_scopes(
            edge: InvocationArtifactInputEdgePlan,
            execution_scope: ComponentGroupScope,
        ) -> dict[RuntimeExecutionAxisScope, str]:
            return RuntimeArtifactInput(
                edge_plan=edge,
                axis_scope=RuntimeExecutionAxisScope.from_raw(
                    plan.axis_id,
                    component=None,
                    value=None,
                ),
                backend=Backend.MEMORY.value,
                source_binding_plan=plan.source_binding_plan,
            ).candidate_execution_scopes(
                context.runtime_value_store,
                execution_scope,
                variable_components=ComponentSet.coerce(plan.variable_components),
            )

        if scope.is_dynamic:
            discovered_keys = []
            for group in pattern.groups:
                for invocation in group.invocations:
                    group_refs = invocation.contract.group_scope_inputs.ref_set()
                    for edge in invocation.artifact_input_edges:
                        if edge.storage_plan is None or not (
                            edge.main_flow_projection is not None
                            or edge.spec.ref() in group_refs
                        ):
                            continue
                        discovered_keys.extend(
                            candidate.value_text
                            for candidate in candidate_scopes(edge, scope)
                        )
            if not any(key is not None for key in discovered_keys):
                return None
            component_keys = scope.runtime_keys(discovered_keys)
        else:
            component_keys = scope.runtime_keys(())

        selected_groups = []
        for component_key in component_keys:
            group = pattern.group_for_component(component_key)
            if group is None:
                raise ValueError(
                    f"No compiled function group for component {component_key!r}."
                )
            edges = plan.stored_primary_input_edges_for_group(group, component_key)
            if edges is None:
                return None
            selected_groups.append((component_key, group, edges))

        requests = []
        for component_index, (component_key, group, edges) in enumerate(
            selected_groups
        ):
            cohorts = None
            for edge in edges:
                edge_cohorts = candidate_scopes(
                    edge,
                    ComponentGroupScope.from_raw(
                        (component_key,), component=scope.component
                    ),
                )
                if not edge_cohorts:
                    raise ValueError(
                        f"Step {plan.step_index} ({plan.step_name}) has no exact "
                        f"producer cohort for {edge.spec.ref()!r} on axis {plan.axis_id}."
                    )
                cohorts = (
                    edge_cohorts
                    if cohorts is None
                    else {
                        joined: anchor
                        for coordinates, anchor in cohorts.items()
                        for candidate in edge_cohorts
                        if (joined := coordinates.join_execution_cohort(candidate))
                        is not None
                    }
                )
            if not cohorts:
                raise ValueError(
                    f"Step {plan.step_index} ({plan.step_name}) producer inputs "
                    "do not share a complete execution cohort."
                )
            requests.extend(
                ArtifactPatternGroupExecutionRequest(
                    context=context,
                    execution_plan=plan,
                    pattern_group_info=anchor,
                    compiled_group=group,
                    component_value=component_key,
                    fixed_component_values=coordinates.fixed_component_values,
                    component_index=component_index,
                    component_count=len(selected_groups),
                )
                for coordinates, anchor in cohorts.items()
            )
        return tuple(requests)

    def run(self) -> StepExecutionObservation:
        plan = self.plan
        step_started_at = time.perf_counter()
        self._log_execution_start()
        output_manifest = step_output_manifest(self.context)
        output_manifest.begin_step(
            plan,
            output_manifest.producer_records_for(plan) or (),
        )

        phase_started_at = time.perf_counter()
        execution_requests = self.artifact_execution_requests()
        patterns_by_axis = (
            self._detect_patterns() if execution_requests is None else None
        )
        self.record_runtime_profile(
            "step_detect_patterns",
            time.perf_counter() - phase_started_at,
        )
        if patterns_by_axis is not None:
            self._log_discovered_patterns(patterns_by_axis)
        phase_started_at = time.perf_counter()
        self._convert_input_if_needed()
        self.record_runtime_profile(
            "step_convert_input",
            time.perf_counter() - phase_started_at,
        )
        if patterns_by_axis is not None:
            self._require_patterns(patterns_by_axis)
            self._apply_sequential_filter(patterns_by_axis)
            phase_started_at = time.perf_counter()
            grouped_patterns = self._prepare_groups(patterns_by_axis)
            execution_requests = self._execution_requests(grouped_patterns)
            self.record_runtime_profile(
                "step_prepare_groups",
                time.perf_counter() - phase_started_at,
            )
        if not execution_requests:
            raise ValueError(
                f"No execution cohorts found for step {plan.step_index} "
                f"({plan.step_name}) on axis {plan.axis_id}."
            )
        total_groups = len(execution_requests)
        execution_started_at = time.perf_counter()
        self._execute_pattern_groups(
            execution_requests,
            total_groups,
        )
        execution_elapsed = time.perf_counter() - execution_started_at

        logger.info(
            "Completed step '%s' for axis %s in %.3fs.",
            plan.step_name,
            plan.axis_id,
            execution_elapsed,
        )
        finalization_started_at = time.perf_counter()
        step_observation = finalize_function_step_outputs(
            self.context,
            plan,
        )
        finalization_elapsed = time.perf_counter() - finalization_started_at
        logger.info(
            "FunctionStep %s (%s) completed for axis %s in %.3fs "
            "(execute=%.3fs, finalize=%.3fs).",
            plan.step_index,
            plan.step_name,
            plan.axis_id,
            time.perf_counter() - step_started_at,
            execution_elapsed,
            finalization_elapsed,
        )
        return step_observation

    def _log_execution_start(self) -> None:
        plan = self.plan
        same_dir = str(plan.input_dir) == str(plan.output_dir)
        if not plan.requires_gpu:
            logger.debug(
                "Step %s is CPU-only, input_mem=%s, output_mem=%s",
                plan.step_index,
                plan.input_memory_type,
                plan.output_memory_type,
            )
        else:
            logger.debug(
                "Step %s uses framework devices=%s, input_mem=%s, output_mem=%s",
                plan.step_index,
                plan.device_assignment.bindings,
                plan.input_memory_type,
                plan.output_memory_type,
            )
        logger.debug(
            "Step %s backends: read=%s, write=%s",
            plan.step_index,
            plan.read_backend,
            plan.write_backend,
        )
        logger.info(
            "Step %s (%s) I/O: read='%s', write='%s'.",
            plan.step_index,
            plan.step_name,
            plan.read_backend,
            plan.write_backend,
        )
        logger.info(
            "Step %s (%s) Paths: input_dir='%s', output_dir='%s', same_dir=%s",
            plan.step_index,
            plan.step_name,
            plan.input_dir,
            plan.output_dir,
            same_dir,
        )

    def _detect_patterns(self) -> dict[str, DiscoveredPatternCollection]:
        plan = self.plan
        axis_name = MULTIPROCESSING_AXIS.value
        axis_filter = {f"{axis_name}_filter": [plan.axis_id]}
        source_files = step_output_manifest(self.context).producer_paths_for(plan)
        if source_files is None:
            source_projection = self.context.runtime_source_workspace_projection_authority.projection_if_available()
            if (
                plan.main_input_dependency.kind
                is StepInputDependencyKind.PIPELINE_START
                and source_projection is not None
            ):
                source_files = source_projection.pipeline_start_files(
                    axis_id=plan.axis_id
                )
        if source_files is not None:
            if not source_files:
                return {}
            cache_key = RuntimePatternDiscoveryCacheKey.from_source_files(
                axis_id=plan.axis_id,
                source_files=source_files,
                group_by=plan.group_by_value,
                variable_components=plan.variable_component_values,
            )
            cached_patterns = self.context.runtime_pattern_discovery_cache.get(
                cache_key
            )
            if cached_patterns is not None:
                return cached_patterns
            patterns_by_axis = PatternDiscoveryEngine(
                self.context.microscope_handler.parser,
                self.context.filemanager,
                self.context.runtime_pattern_discovery_cache,
            ).auto_detect_patterns_from_axis_files(
                list(source_files),
                axis_id=plan.axis_id,
                variable_components=plan.variable_component_values,
                group_by=plan.group_by,
            )
            self.context.runtime_pattern_discovery_cache.store(
                cache_key, patterns_by_axis
            )
            return patterns_by_axis
        return self.context.microscope_handler.auto_detect_patterns(
            str(plan.input_dir),
            self.context.filemanager,
            plan.read_backend,
            extensions=LOADABLE_IMAGE_EXTENSIONS,
            group_by=plan.group_by,
            variable_components=plan.variable_component_values,
            pattern_cache=self.context.runtime_pattern_discovery_cache,
            **axis_filter,
        )

    def _log_discovered_patterns(
        self,
        patterns_by_axis: Mapping[str, DiscoveredPatternCollection],
    ) -> None:
        plan = self.plan
        if plan.axis_id not in patterns_by_axis:
            logger.warning("No patterns found for axis %s.", plan.axis_id)
            return

        axis_patterns = patterns_by_axis[plan.axis_id]
        if isinstance(axis_patterns, dict):
            for component_value, pattern_list in axis_patterns.items():
                logger.debug(
                    "Component '%s' has %s patterns: %s",
                    component_value,
                    len(pattern_list),
                    pattern_list,
                )
            return

        logger.debug(
            "Found %s ungrouped patterns: %s",
            len(axis_patterns),
            axis_patterns,
        )

    def _convert_input_if_needed(self) -> None:
        plan = self.plan
        input_conversion = plan.input_conversion
        if input_conversion is None:
            return

        logger.info("Converting input data to zarr: %s", input_conversion.output_dir)

        source_paths = get_all_image_paths(
            input_dir=plan.input_dir,
            axis_id=plan.axis_id,
            backend=plan.read_backend,
            filemanager=self.context.filemanager,
            microscope_handler=self.context.microscope_handler,
        )
        memory_data = self.context.filemanager.load_batch(
            source_paths, plan.read_backend
        )
        conversion_paths = generate_materialized_paths(
            source_paths,
            plan.input_dir,
            input_conversion.output_dir,
        )

        save_materialized_data(
            self.context.filemanager,
            memory_data,
            conversion_paths,
            input_conversion.backend,
            plan.zarr_config,
            self.context,
            plan.axis_id,
        )
        logger.info(
            "Converted %s input files to %s",
            len(conversion_paths),
            input_conversion.output_dir,
        )

        conversion_dir = input_conversion.output_dir
        zarr_subdir = None
        if input_conversion.uses_virtual_workspace:
            zarr_subdir = conversion_dir.name
        update_metadata_for_zarr_conversion(
            conversion_dir.parent,
            input_conversion.original_subdir,
            zarr_subdir,
            self.context,
        )

    def _require_patterns(
        self,
        patterns_by_axis: Mapping[str, DiscoveredPatternCollection],
    ) -> None:
        plan = self.plan
        logger.info(
            "Starting step '%s' for axis %s (group_by=%s, variable_components=%s)",
            plan.step_name,
            plan.axis_id,
            plan.group_by.name if plan.group_by else None,
            [component.name for component in plan.variable_components],
        )
        if plan.axis_id not in patterns_by_axis:
            raise ValueError(
                f"No patterns detected for well '{plan.axis_id}' in step "
                f"'{plan.step_name}' (index: {plan.step_index}). "
                f"Check input directory: {plan.input_dir}"
            )
        if not tuple(plan.compiled_function_pattern.iter_invocations()):
            raise ValueError(
                f"Step plan missing compiled function invocations for step: {plan.step_name} "
                f"(index: {plan.step_index})"
            )

    def _apply_sequential_filter(
        self,
        patterns_by_axis: dict[str, DiscoveredPatternCollection],
    ) -> None:
        if not self.plan.sequential_filter_plan.enabled:
            return

        filtered_patterns = patterns_by_axis[self.plan.axis_id]
        for sequential_filter in self.plan.sequential_filter_plan.filters:
            filtered_patterns = _filter_patterns_by_component(
                filtered_patterns,
                sequential_filter.component_name,
                sequential_filter.value,
                self.context.microscope_handler.parser,
            )
        patterns_by_axis[self.plan.axis_id] = filtered_patterns

    def _prepare_groups(
        self,
        patterns_by_axis: Mapping[str, DiscoveredPatternCollection],
    ) -> GroupedPatternMap:
        plan = self.plan
        axis_patterns = patterns_by_axis[plan.axis_id]
        execution_group_value = plan.execution_group_value
        if execution_group_value is None and plan.compiled_function_pattern.is_grouped:
            raise ValueError(
                f"Step '{plan.step_name}' uses a dict function pattern without "
                "a concrete execution group component. Dict keys are dispatch "
                "groups and require group_by to resolve to a real component; "
                "GroupBy.NONE is only valid for non-dict function patterns."
            )
        if (
            plan.execution_group_scope.is_ungrouped
            and not plan.compiled_function_pattern.is_grouped
        ):
            axis_patterns = _single_execution_group_patterns(axis_patterns)

        discovered_groups = (
            axis_patterns
            if isinstance(axis_patterns, Mapping)
            else {execution_group_value: axis_patterns}
        )
        grouped_patterns = {
            key: tuple(str(pattern) for pattern in patterns)
            for key, patterns in discovered_groups.items()
        }
        grouped_patterns = self._filter_anchor_patterns(grouped_patterns)
        if sum(map(len, grouped_patterns.values())) == 0:
            raise ValueError(
                f"No pattern groups found for step {plan.step_index} "
                f"({plan.step_name}) in well {plan.axis_id}"
            )
        return grouped_patterns

    def _execute_pattern_groups(
        self,
        execution_requests: Sequence[PatternGroupExecutionRequest],
        total_groups: int,
    ) -> None:
        for completed_groups, request in enumerate(execution_requests, start=1):
            _process_single_pattern_group(request)
            self._emit_pattern_progress(
                completed_groups,
                total_groups,
                request.component_value,
                request.pattern_group_info,
            )

    def _emit_pattern_progress(
        self,
        completed_groups: int,
        total_groups: int,
        component_value: FunctionGroupKey,
        pattern_item: SourceCandidatePath,
    ) -> None:
        runtime = self.context.execution_runtime
        if runtime is None:
            return
        emit(
            execution_id=runtime.execution_id,
            plate_id=runtime.plate_id,
            axis_id=self.plan.axis_id,
            step_name=self.plan.step_name,
            phase=ProgressPhase.PATTERN_GROUP,
            status=ProgressStatus.RUNNING,
            completed=completed_groups,
            total=total_groups,
            percent=(completed_groups / total_groups) * 100.0,
            component=str(component_value),
            pattern=str(pattern_item),
            worker_slot=runtime.worker_slot,
            owned_wells=list(runtime.owned_wells),
        )
