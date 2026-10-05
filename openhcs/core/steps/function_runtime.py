"""Runtime execution helpers for FunctionStep.

This module owns callable invocation, artifact routing, and pattern-group stack
execution. FunctionStep remains responsible for step-level orchestration.
"""

from functools import singledispatch
import logging
import time
from dataclasses import dataclass, replace
from pathlib import Path
from types import MappingProxyType
from typing import (
    Mapping,
    Sequence,
    TypeVar,
    cast,
)

import numpy as np

from openhcs.constants.constants import AllComponents, Backend
from openhcs.core.artifacts import (
    ArtifactInputPlan,
    ArtifactOutputPlan,
    NoMainFlowOutput,
    ImageArtifactType,
    ArtifactSpecRef,
)
from openhcs.core.callable_contract import (
    ImagePayloadConsumption,
)
from openhcs.core.component_group_scope import (
    ComponentGroupScope,
    RuntimeExecutionAxisScope,
    RuntimeFixedComponentValues,
)
from openhcs.core.component_set import ComponentSet
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.debug import (
    DebugCursor,
    DebugEvent,
    DebugEventSink,
    DebugEventType,
    DebugArtifactRefProjection,
    DebugInvocationParameter,
    debug_event_sink_from_context,
)
from openhcs.core.function_patterns import (
    CompiledFunctionGroup,
    CompiledFunctionInvocation,
    InvocationArtifactInputEdgePlan,
    InvocationArtifactInputProjectionKey,
    MainFlowInputProjection,
    RuntimeComponentValue,
    RuntimeInvocationDomain,
)
from openhcs.core.aligned_image_payload import (
    AlignedImageStack,
    AlignedImageSliceContext,
    ImagePayloadStackComposition,
    ImageOutputBundle,
    unstack_image_payload_context,
)
from openhcs.core.memory import (
    unstack_runtime_slices,
)
from openhcs.core.runtime_stores import (
    RuntimeArtifactInput,
    RuntimeArtifactLocation,
    replace_runtime_artifact_payload,
)
from openhcs.core.runtime_artifact_values import RuntimeValue
from openhcs.core.runtime_output_matching import (
    split_runtime_output,
)
from openhcs.core.runtime_profile import RuntimeProfileLogger
from openhcs.core.runtime_adapters import (
    RuntimeAdapterRequest,
)
from openhcs.core.runtime_slice_alignment import (
    RuntimeSliceAlignedValueSet,
    RuntimeSliceAlignedValues,
)
from openhcs.core.runtime_slice_projection import (
    RuntimeSliceProjection,
    RuntimeSliceProjectionDeclarationError,
)
from openhcs.core.source_image_provenance import (
    SourceImageIdentity,
)
from openhcs.core.source_workspace_projection import (
    VirtualWorkspacePathLookup,
    VirtualWorkspaceSourceProjection,
    VirtualWorkspaceSourceProjectionAuthority,
)
from openhcs.core.source_binding_selection import (
    SourceBindingCandidateMatcher,
    SourceBindingMatchedImageSet,
    SourceFileUniverse,
    SourceUniverseRequest,
    SourcePatternResolutionContext,
)
from openhcs.core.source_matching import (
    source_component_metadata_value,
    source_metadata_value,
    with_source_component_metadata,
)
from openhcs.core.source_bindings import (
    CompiledSourceBindingPlan,
    SOURCE_BINDING_ALIAS_METADATA_FIELD,
    SourceProjectionRole,
)
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    ImagePayloadMetadataCarrier,
    image_payload_data,
    image_payload_mask,
    image_payload_metadata,
    with_image_payload_data,
)
from openhcs.core.runtime_image_loading import ImagePayloadSourceMetadataContext
from openhcs.core.runtime_array_values import RuntimeArrayData
from openhcs.core.runtime_measurements import MeasurementTable
from openhcs.core.runtime_spatial_graph import SpatialGraph
from openhcs.core.runtime_object_labels import (
    ObjectLabelSet,
    ObjectLabelValue,
)
from openhcs.core.runtime_tabular_values import ColumnarRows
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisProjector,
    RuntimePlaneProjection,
)
from openhcs.core.step_dependencies import StepInputDependencyKind
from openhcs.core.steps.function_output_manifest import (
    NoStepOutputManifestMatch,
    ProducedOutputSemantics,
    step_output_manifest,
)
from openhcs.core.steps.function_output_identity import (
    FunctionOutputIdentity,
    FunctionOutputPathRequest,
)
from openhcs.core.compiled_step_plan import CompiledStepPlan

logger = logging.getLogger(__name__)

ArtifactInputPlanKeyT = TypeVar(
    "ArtifactInputPlanKeyT",
    ArtifactSpecRef,
    InvocationArtifactInputProjectionKey,
)
ArtifactInputPlanT = TypeVar(
    "ArtifactInputPlanT",
    ArtifactInputPlan,
    InvocationArtifactInputEdgePlan,
)
ArtifactInputPlans = Mapping[ArtifactInputPlanKeyT, ArtifactInputPlanT]
ArtifactOutputPlans = Mapping[ArtifactSpecRef, ArtifactOutputPlan]
JsonValue = RuntimeComponentValue | Mapping[str, "JsonValue"] | Sequence["JsonValue"]
FunctionOutputContextualizedValue = (
    RuntimeArrayData
    | ObjectLabelValue
    | ColumnarRows
    | MeasurementTable
    | SpatialGraph
    | RuntimeSliceAlignedValueSet
)
ObjectLabelContextualizableOutput = (
    RuntimeArrayData | ObjectLabelValue | RuntimeSliceAlignedValueSet
)
RuntimePayload = FunctionOutputContextualizedValue
RuntimeFunctionOutput = RuntimePayload | NoMainFlowOutput | tuple[RuntimePayload, ...]
RuntimeCallableArgument = JsonValue | RuntimePayload | ProcessingContext
RuntimeCallableKwargs = Mapping[str, RuntimeCallableArgument]
EMPTY_ARTIFACT_PLANS: ArtifactOutputPlans = MappingProxyType({})


@singledispatch
def project_declared_source_identity(
    source_payload: RuntimePayload,
    source_ref: ArtifactSpecRef,
) -> RuntimePayload:
    """Project an image payload to one exact declared source identity."""

    metadata = image_payload_metadata(source_payload)
    return metadata.project_declared_source_image(source_payload, source_ref.name)


@project_declared_source_identity.register(RuntimeSliceAlignedValueSet)
def project_aligned_declared_source_identity(
    source_payload: RuntimeSliceAlignedValueSet,
    source_ref: ArtifactSpecRef,
) -> RuntimeSliceAlignedValues:
    """Project each runtime-aligned image slice to the declared source identity."""

    return RuntimeSliceAlignedValues(
        tuple(
            project_declared_source_identity(
                source_payload.value_for_slice(slice_index),
                source_ref,
            )
            for slice_index in range(source_payload.slice_count)
        )
    )


@project_declared_source_identity.register(ObjectLabelValue)
def project_object_label_declared_source_identity(
    source_payload: ObjectLabelValue,
    source_ref: ArtifactSpecRef,
) -> ObjectLabelValue:
    """Preserve object-label context without applying image-axis projection."""

    if (
        isinstance(source_payload, ObjectLabelSet)
        and source_payload.name != source_ref.name
    ):
        raise ValueError(
            f"Object-label payload {source_payload.name!r} cannot resolve declared "
            f"source {source_ref!r}."
        )
    return source_payload


@dataclass(frozen=True, slots=True, kw_only=True)
class PatternGroupExecutionScope:
    """Shared pattern-group execution coordinates."""

    context: ProcessingContext
    execution_plan: CompiledStepPlan
    compiled_group: CompiledFunctionGroup
    component_value: RuntimeComponentValue = None
    fixed_component_values: RuntimeFixedComponentValues = ()

    @property
    def component_key(self) -> str | None:
        if self.component_value is None:
            return None
        return str(self.component_value)

    @property
    def unscoped_main_flow_source_binding_plan(self) -> CompiledSourceBindingPlan:
        """Return declared bindings that can contribute to main flow."""

        declared_plan = self.execution_plan.source_binding_plan
        main_flow_refs = self.compiled_group.main_flow_input_refs_for_component(
            self.execution_plan.execution_group_scope,
            self.component_key,
        )
        return (
            declared_plan
            if main_flow_refs is None
            else declared_plan.for_artifact_refs(main_flow_refs)
        )

    @property
    def main_flow_source_binding_plan(self) -> CompiledSourceBindingPlan:
        """Return bindings that anchor and load this group's main-flow stack."""

        return self.unscoped_main_flow_source_binding_plan.for_execution_axis_scope(
            self.axis_scope
        )

    def active_main_flow_source_binding_plan(
        self,
        payload: RuntimeArrayData,
    ) -> CompiledSourceBindingPlan:
        """Project main-flow bindings through represented payload aliases."""

        plan = self.unscoped_main_flow_source_binding_plan
        represented_names = frozenset(
            image_payload_metadata(
                payload
            ).source_provenance.represented_source_image_names
        )
        if represented_names:
            variable_components = ComponentSet.coerce(
                self.execution_plan.variable_components or ()
            )
            return plan.for_represented_source_stack(
                represented_names,
                variable_components=variable_components,
            )
        return plan.for_execution_axis_scope(self.axis_scope)

    @property
    def invocation_source_artifact_refs(self) -> tuple[ArtifactSpecRef, ...]:
        """Return exact source artifacts consumed by this invocation group."""

        declared_plan = self.execution_plan.source_binding_plan
        return tuple(
            dict.fromkeys(
                spec.ref()
                for invocation in self.compiled_group.invocations
                for spec in invocation.contract.artifact_inputs
                if declared_plan.binding_for_artifact_ref(spec.ref()) is not None
            )
        )

    @property
    def source_binding_plan(self) -> CompiledSourceBindingPlan:
        """Return all source bindings visible to this invocation group."""

        declared_plan = self.execution_plan.source_binding_plan
        source_refs = self.invocation_source_artifact_refs
        return (
            declared_plan.for_artifact_refs(source_refs)
            if source_refs
            else self.main_flow_source_binding_plan
        )

    @property
    def axis_component(self) -> str | None:
        if self.component_value is None:
            return None
        component = self.execution_plan.execution_group_scope.component
        return None if component is None else component.value

    @property
    def axis_component_value(self) -> str | None:
        return self.component_key

    @property
    def axis_scope(self) -> RuntimeExecutionAxisScope:
        return RuntimeExecutionAxisScope.from_raw(
            self.execution_plan.axis_id,
            component=self.axis_component,
            value=self.axis_component_value,
            fixed_component_values=self.fixed_component_values,
        )

    @staticmethod
    def _select_output_plans_for_component(
        plans: ArtifactOutputPlans,
        execution_scope: ComponentGroupScope,
        component_key: str | None,
    ) -> ArtifactOutputPlans:
        ArtifactOutputPlan.require_exact_map(
            plans,
            boundary="Component artifact output",
        )
        return {
            output_key: projected_plan
            for output_key, output_plan in plans.items()
            if (
                projected_plan := output_plan.for_execution_scope(
                    execution_scope,
                    component_key,
                )
            )
            is not None
        }

    def selected_artifact_output_plans(self) -> ArtifactOutputPlans:
        """Project current compiled output declarations into this group scope."""
        return self._select_output_plans_for_component(
            self.execution_plan.artifact_outputs,
            self.execution_plan.execution_group_scope,
            self.component_key,
        )


@dataclass(frozen=True, slots=True, kw_only=True)
class PatternGroupExecutionRequest(PatternGroupExecutionScope):
    """All runtime data needed to process one pattern group."""

    pattern_group_info: JsonValue
    component_index: int
    component_count: int

    def loaded_plane_count(
        self,
        matching_files: Sequence[str],
        payload: RuntimeArrayData,
    ) -> int:
        """The source path roster declares the initial runtime plane count."""
        return image_payload_metadata(
            payload
        ).source_spatial_domain.intrinsic_plane_count(
            np.shape(image_payload_data(payload)),
            len(matching_files),
        )

    def loaded_fixed_component_values(
        self,
        payload: RuntimeArrayData,
    ) -> RuntimeFixedComponentValues:
        """Capture the source-selected cohort's common fixed coordinates."""
        source_provenance = image_payload_metadata(
            payload
        ).source_provenance.with_common_scalar_identity_from_planes()
        common_source_metadata = source_provenance.source_component_metadata or {}
        variable_components = ComponentSet.coerce(
            self.execution_plan.variable_components or ()
        )
        execution_group_component = self.execution_plan.execution_group_scope.component
        fixed_components = tuple(
            component
            for component in AllComponents
            if not component.is_multiprocessing_axis()
            and component is not execution_group_component
            and component not in variable_components
            and source_component_metadata_value(
                common_source_metadata,
                component,
            )
            is not None
        )
        return source_provenance.require_common_component_values(fixed_components)

    def passthrough_producer_records(
        self,
        matching_files: Sequence[str],
    ) -> tuple[ProducedOutputSemantics, ...] | None:
        """Resolve the physical source paths selected by this request."""
        return step_output_manifest(self.context).producer_output_records_for_paths(
            self.execution_plan,
            matching_files,
            self.context.microscope_handler.parser,
        )

    @property
    def pattern_repr(self) -> str:
        return str(self.pattern_group_info)[:100]

    def source_workspace_projection_authority(
        self,
    ) -> VirtualWorkspaceSourceProjectionAuthority:
        return self.context.runtime_source_workspace_projection_authority

    @staticmethod
    def _is_relative_to(path: Path, root: Path) -> bool:
        try:
            path.relative_to(root)
        except ValueError:
            return False
        return True

    @classmethod
    def _input_memory_path(cls, input_dir: Path, matched_path: str) -> str:
        """Return the VFS memory path for one matched source path."""
        path = Path(matched_path)
        if path.is_absolute() or cls._is_relative_to(path, input_dir):
            return str(path)
        return str(input_dir / path)

    @classmethod
    def _input_relative_path(cls, input_dir: Path, matched_path: str) -> Path:
        """Return matched path identity relative to the step input root."""
        path = Path(matched_path)
        if cls._is_relative_to(path, input_dir):
            return path.relative_to(input_dir)
        if path.is_absolute():
            return Path(path.name)
        return path

    def run(self) -> None:
        start_time = time.time() if logger.isEnabledFor(logging.DEBUG) else None
        plan = self.execution_plan
        logger.debug("Processing pattern %s for axis %s", self.pattern_repr, plan.axis_id)

        try:
            load_started_at = time.perf_counter()
            matching_files, main_data_stack = self.load_input_stack()
        except NoStepOutputManifestMatch:
            logger.debug(
                "Skipping stale pattern group %s for step %s (%s); no files "
                "belong to producer manifest.",
                self.pattern_repr,
                plan.step_index,
                plan.step_name,
            )
            return
        try:
            RuntimeProfileLogger.log(
                logger,
                "pattern_load_stack",
                time.perf_counter() - load_started_at,
                step=plan.step_index,
                step_name=plan.step_name,
                pattern=self.pattern_repr,
            )
            execute_started_at = time.perf_counter()
            loaded = PatternGroupData.from_loaded_group(
                self,
                matching_files,
                main_data_stack,
            )
            processed_stack = loaded.execute_chain()
            RuntimeProfileLogger.log(
                logger,
                "pattern_execute_chain",
                time.perf_counter() - execute_started_at,
                step=plan.step_index,
                step_name=plan.step_name,
                pattern=self.pattern_repr,
            )
            if isinstance(processed_stack, NoMainFlowOutput):
                self._record_main_flow_passthrough(loaded.matching_files)
                RuntimeProfileLogger.log(
                    logger,
                    "pattern_no_main_flow_output",
                    0.0,
                    step=plan.step_index,
                    step_name=plan.step_name,
                    pattern=self.pattern_repr,
                )
                logger.debug(
                    "Pattern group %s for step %s recorded artifacts without "
                    "publishing main-flow output.",
                    self.pattern_repr,
                    plan.step_name,
                )
                return
            if not plan.requires_main_flow_checkpoint(self.context.step_plans):
                return
            output_records = self._save_outputs(processed_stack, loaded.matching_files)
            output_paths = [record.output_path for record in output_records]
            cleanup_started_at = time.perf_counter()
            self._cleanup_collapsed_domains(
                output_records,
                loaded.matching_files,
                output_paths,
            )
            step_output_manifest(self.context).record_outputs(
                plan,
                output_records,
                collapsed_input_domain=(
                    len(output_records) < len(loaded.matching_files)
                ),
            )
            RuntimeProfileLogger.log(
                logger,
                "pattern_cleanup",
                time.perf_counter() - cleanup_started_at,
                step=plan.step_index,
                step_name=plan.step_name,
                pattern=self.pattern_repr,
            )
            if start_time is not None and logger.isEnabledFor(logging.DEBUG):
                logger.debug(
                    "Finished pattern group %s in %.2fs.",
                    self.pattern_repr,
                    time.time() - start_time,
                )
        except Exception as e:
            logger.error(
                "Error processing pattern group %s: %s", self.pattern_repr, e,
                exc_info=True,
            )
            raise ValueError(
                f"Failed to process pattern group {self.pattern_repr}: {e}"
            ) from e

    def _record_main_flow_passthrough(self, matching_files: Sequence[str]) -> None:
        """Record existing main-flow anchors for artifact-only step outputs."""
        if not matching_files:
            return
        plan = self.execution_plan
        if not plan.requires_main_flow_checkpoint(self.context.step_plans):
            return
        parser = self.context.microscope_handler.parser
        manifest = step_output_manifest(self.context)
        producer_records = self.passthrough_producer_records(matching_files)
        if producer_records is None:
            records = tuple(
                ProducedOutputSemantics.from_existing_main_flow_path(
                    plan,
                    self._input_memory_path(plan.input_dir, matching_file),
                    parser,
                )
                for matching_file in matching_files
            )
        else:
            records = tuple(record.passed_through(plan) for record in producer_records)
        manifest.record_outputs(plan, records)

    def _producer_output_contexts(
        self,
        matching_files: Sequence[str],
    ) -> tuple[AlignedImageSliceContext, ...]:
        """Resolve exact producer contexts for the loaded main-flow paths."""

        return step_output_manifest(self.context).producer_output_contexts_for_paths(
            self.execution_plan,
            matching_files,
            self.context.microscope_handler.parser,
        )

    def load_input_stack(
        self,
    ) -> tuple[list[str], RuntimeArrayData]:
        context = self.context
        plan = self.execution_plan
        request = self
        if not context.microscope_handler:
            raise RuntimeError("MicroscopeHandler not available in context.")

        output_manifest = step_output_manifest(context)
        producer_index = output_manifest.producer_record_index_for(
            plan,
            context.microscope_handler.parser,
        )
        producer_records = (
            None
            if producer_index is None
            else producer_index.matching_records(str(request.pattern_group_info))
        )
        producer_matching_files = (
            ()
            if producer_records is None
            else tuple(record.output_path for record in producer_records)
        )
        matching_files = list(producer_matching_files)
        source_projection = (
            self.source_workspace_projection_authority().projection_if_available()
        )
        if not matching_files:
            matching_files = context.microscope_handler.path_list_from_pattern(
                str(plan.input_dir),
                request.pattern_group_info,
                context.filemanager,
                plan.read_backend,
                (
                    [component.value for component in plan.variable_components]
                    if plan.variable_components
                    else None
                ),
                pattern_cache=context.runtime_pattern_discovery_cache,
            )
        if producer_index is not None and not producer_matching_files:
            selected_paths = [
                path for path in matching_files if producer_index.contains(path)
            ]
            if matching_files and not selected_paths:
                raise NoStepOutputManifestMatch
            matching_files = selected_paths

        if not matching_files:
            raise ValueError(
                f"No matching files found for pattern group {self.pattern_repr} "
                f"in {plan.input_dir}. "
                f"This indicates either: (1) no image files exist in the directory, "
                f"(2) files don't match the pattern, or (3) pattern parsing failed. "
                f"Check that input files exist and match the expected naming convention."
            )

        matching_files = self._filter_matching_files_for_group(matching_files)

        if logger.isEnabledFor(logging.DEBUG):
            logger.debug(
                "Pattern %s matched %d files: %s",
                self.pattern_repr,
                len(matching_files),
                [Path(f).name for f in matching_files],
            )

        if not producer_matching_files:
            matching_files.sort()
        logger.debug(
            f"Pattern {self.pattern_repr} sorted files: {[Path(f).name for f in matching_files]}"
        )
        matching_files = self._filter_matching_files_for_source_bindings(matching_files)

        full_file_paths = [
            self._input_memory_path(plan.input_dir, file_path)
            for file_path in matching_files
        ]
        workspace_path_lookups = tuple(
            VirtualWorkspacePathLookup.from_paths(
                virtual_path,
                full_virtual_path,
            )
            for virtual_path, full_virtual_path in zip(
                matching_files,
                full_file_paths,
                strict=True,
            )
        )
        workspace_source_lookups = (
            self._workspace_source_binding_lookups(
                source_projection,
                workspace_path_lookups,
            )
            if source_projection is not None
            else ()
        )
        if producer_index is not None:
            if producer_matching_files:
                producer_index.validate_input_records(producer_records)
            else:
                producer_records = producer_index.records_for_paths(matching_files)
        ImagePayloadStackComposition.validate_main_flow_cohort(producer_records)
        cached_stack = context.runtime_image_stack_cache.get(
            tuple(full_file_paths),
            memory_type=plan.input_memory_type,
        )
        RuntimeProfileLogger.log(
            logger,
            "runtime_stack_cache_get",
            0.0,
            step=plan.step_index,
            step_name=plan.step_name,
            hit=cached_stack is not None,
            paths=len(full_file_paths),
            memory_type=plan.input_memory_type,
        )
        if cached_stack is None:
            raw_slices = SourceFileUniverse(
                tuple(full_file_paths),
                (
                    Backend.MEMORY
                    if plan.main_input_dependency.kind
                    is StepInputDependencyKind.STEP_OUTPUT
                    else Backend(plan.read_backend)
                ),
            ).load_images(context.filemanager, zarr_config=plan.zarr_config)
            if source_projection is not None or not producer_matching_files:
                raw_slices = self._apply_source_image_loading_semantics(
                    raw_slices,
                    workspace_path_lookups,
                    workspace_source_lookups,
                    source_projection,
                )

            if not raw_slices:
                raise ValueError(
                    f"No valid images loaded for pattern group {self.pattern_repr} "
                    f"in {plan.input_dir}. "
                    f"Found {len(matching_files)} matching files but failed to load any valid images. "
                    f"This indicates corrupted image files, unsupported formats, or I/O errors. "
                    f"Check file integrity and format compatibility."
                )

            main_data_stack = ImagePayloadStackComposition.from_loaded_images(
                raw_slices,
                producer_records=producer_records,
                execution_plan=plan,
                source_projection=source_projection,
                workspace_source_lookups=workspace_source_lookups,
            )
            if not producer_records:
                metadata = image_payload_metadata(main_data_stack)
                domain = request.source_binding_plan.source_spatial_domain.admit_source_cohort(
                    metadata.source_spatial_domain,
                    depth=len(matching_files),
                )
                main_data_stack = metadata.replace_fields(
                    source_spatial_domain=domain,
                ).attach_to(main_data_stack)
        else:
            main_data_stack = cached_stack

        return matching_files, main_data_stack

    def _workspace_source_binding_lookups(
        self,
        source_projection: VirtualWorkspaceSourceProjection,
        lookups: Sequence[VirtualWorkspacePathLookup],
    ) -> tuple[VirtualWorkspacePathLookup, ...]:
        """Return workspace paths owned by this step's exact source bindings."""

        bindings = self.source_binding_plan.binding_declarations
        return tuple(
            lookup
            for lookup in lookups
            for projection in (source_projection.source_projection_for(lookup),)
            if projection is not None
            and any(projection.matches_binding(binding) for binding in bindings)
        )

    def _filter_matching_files_for_group(
        self,
        matching_files: list[str],
    ) -> list[str]:
        """Constrain grouped executions to files from the current component."""
        if (
            self.execution_plan.main_input_dependency.kind
            is StepInputDependencyKind.STEP_OUTPUT
            or self.compiled_group.runtime_domain
            is RuntimeInvocationDomain.ARTIFACT_MANAGED
        ):
            return matching_files
        if self.main_flow_source_binding_plan.has_primary_content:
            return matching_files

        group_component = self.execution_plan.execution_group_value
        component_value = self.component_value
        if group_component is None or component_value is None:
            return matching_files

        parser = self.context.microscope_handler.parser
        filtered = self.context.runtime_pattern_discovery_cache.files_for_component(
            parser,
            matching_files,
            parser.component_for_name(group_component),
            component_value,
        )
        if not filtered:
            raise ValueError(
                f"Pattern group {self.pattern_repr} for {group_component}="
                f"{component_value!r} matched files, but none carried the "
                f"expected grouped component. Matched files: {matching_files}"
            )
        return filtered

    def _filter_matching_files_for_source_bindings(
        self,
        matching_files: list[str],
    ) -> list[str]:
        """Constrain the loaded main stack to declared image source bindings."""

        if (
            self.execution_plan.main_input_dependency.kind
            is StepInputDependencyKind.STEP_OUTPUT
        ):
            return matching_files

        source_binding_plan = self.main_flow_source_binding_plan
        if not source_binding_plan.has_primary_content:
            return matching_files
        bindings = tuple(
            binding
            for binding in source_binding_plan.bindings
            if binding.projection_role is SourceProjectionRole.PRIMARY_PLANE
        )
        if not bindings:
            return matching_files
        selector_bindings = SourceBindingCandidateMatcher.selector_bindings(bindings)

        source_context = self._source_binding_candidate_context()
        if (
            not selector_bindings
            and not source_context.source_projections_by_virtual_path
        ):
            return matching_files
        compatible = list(
            SourceBindingMatchedImageSet.from_plan(
                bindings=bindings,
                match_plan=source_binding_plan.match_plan,
                source_context=source_context,
                identity_policy=(self.context.source_image_set_identity_policy),
            ).expand(
                matching_files,
                source_universe=self._source_binding_load_universe(),
            )
        )
        if compatible:
            return compatible

        raise ValueError(
            f"Source-bound step {self.execution_plan.step_name!r} resolved no files for "
            f"image bindings {[binding.alias for binding in bindings]!r} in pattern "
            f"{self.pattern_repr}. Matched files before source filtering: "
            f"{matching_files!r}."
        )

    def _source_binding_load_universe(self) -> tuple[str, ...]:
        """Return loadable files available for source image-set expansion."""
        source_projection = (
            self.source_workspace_projection_authority().projection_if_available()
        )
        request = SourceUniverseRequest.from_context(
            context=self.context,
            plan=self.execution_plan,
            matching_files=(),
            source_projection=source_projection,
        )
        return request.runtime_universe_state().require_load_universe().files

    def _source_binding_candidate_context(self) -> SourcePatternResolutionContext:
        projection = self.source_workspace_projection_authority().projection_or_empty()
        return self.context.runtime_source_binding_context_cache.source_pattern_context(
            parser=self.context.microscope_handler.parser,
            projection=self.context.runtime_source_workspace_projection_cache.filtered_by_axis(
                projection,
                axis_id=self.execution_plan.axis_id,
            ),
            metadata_rules=self.source_binding_plan.metadata_rules,
        )

    def _apply_source_image_loading_semantics(
        self,
        raw_slices: Sequence[RuntimeArrayData],
        workspace_path_lookups: Sequence[VirtualWorkspacePathLookup],
        workspace_source_lookups: Sequence[VirtualWorkspacePathLookup],
        source_projection: VirtualWorkspaceSourceProjection | None,
    ) -> list[RuntimeArrayData]:
        if source_projection is not None:
            source_lookups = frozenset(workspace_source_lookups)
            return [
                (
                    self._apply_workspace_source_binding_payload(
                        payload,
                        source_projection=source_projection,
                        lookup=lookup,
                    )
                    if lookup in source_lookups
                    else self._apply_workspace_source_payload(
                        payload,
                        source_projection=source_projection,
                        lookup=lookup,
                    )
                )
                for payload, lookup in zip(
                    raw_slices,
                    workspace_path_lookups,
                    strict=True,
                )
            ]

        universe_state = SourceUniverseRequest.from_context(
            context=self.context,
            plan=self.execution_plan,
            matching_files=tuple(
                lookup.virtual_path for lookup in workspace_path_lookups
            ),
            source_projection=None,
        ).runtime_universe_state()
        cache = self.context.runtime_source_binding_context_cache
        source_metadata = cache.normalized_source_metadata(
            universe_state.source_metadata_by_path
        )
        source_context = SourcePatternResolutionContext.from_sources(
            parser=self.context.microscope_handler.parser,
            source_paths_by_virtual_path={},
            source_metadata_by_path=source_metadata,
            metadata_rules=self.source_binding_plan.metadata_rules,
        )
        return [
            self._apply_source_binding_payload(
                payload,
                source_metadata=source_context.merged_metadata_for_paths(
                    (
                        lookup.virtual_path,
                        lookup.full_virtual_path,
                    )
                ),
                source_path=source_context.source_path_for(lookup.full_virtual_path),
                read_backend=self.execution_plan.read_backend,
            )
            for payload, lookup in zip(
                raw_slices,
                workspace_path_lookups,
                strict=True,
            )
        ]

    def _apply_workspace_source_payload(
        self,
        payload: RuntimeArrayData,
        *,
        source_projection: VirtualWorkspaceSourceProjection,
        lookup: VirtualWorkspacePathLookup,
    ) -> RuntimeArrayData:
        """Attach workspace-owned source identity without requiring a binding."""

        source_ref = source_projection.source_ref_for(lookup)
        if source_ref is None:
            return payload
        source_context = ImagePayloadSourceMetadataContext(
            SourceImageIdentity(
                lookup.full_virtual_path,
                source_projection.source_metadata_for(lookup),
            ),
            source_ref.backend,
            self.context.filemanager,
            source_ref.backend_address,
        )
        metadata = source_context.metadata(payload)
        return source_projection.project_unbound_payload(
            lookup,
            metadata.payload_with(
                image_payload_data(payload),
                image_payload_mask(payload),
            ),
        )

    def _apply_workspace_source_binding_payload(
        self,
        payload: RuntimeArrayData,
        *,
        source_projection: VirtualWorkspaceSourceProjection,
        lookup: VirtualWorkspacePathLookup,
    ) -> RuntimeArrayData:
        projection = source_projection.require_source_projection_for(lookup)
        payload = source_projection.project_payload(lookup, payload)
        return self._apply_source_binding_payload(
            payload,
            source_metadata=source_projection.source_metadata_for(lookup),
            source_path=lookup.full_virtual_path,
            source_address=projection.ref.backend_address,
            read_backend=projection.ref.backend,
        )

    def _apply_source_binding_payload(
        self,
        payload: RuntimeArrayData,
        *,
        source_metadata: Mapping[str, object] | None,
        source_path: str,
        source_address: str | None = None,
        read_backend: str | None,
    ) -> RuntimeArrayData:
        source_context = ImagePayloadSourceMetadataContext(
            SourceImageIdentity(source_path, source_metadata),
            read_backend,
            self.context.filemanager,
            source_address,
        )
        source_bindings = self.source_binding_plan
        if not source_bindings.binding_declarations:
            metadata = source_context.metadata(payload)
            return metadata.payload_with(
                image_payload_data(payload),
                image_payload_mask(payload),
            )
        alias = (
            None
            if source_metadata is None
            else source_metadata_value(
                source_metadata,
                SOURCE_BINDING_ALIAS_METADATA_FIELD,
            )
        )
        if alias is None:
            raise ValueError(
                f"Source-bound payload {source_path!r} has no declared source alias."
            )
        binding = source_bindings.binding_for_alias(alias)
        if binding is None:
            raise ValueError(
                f"Source-bound payload {source_path!r} declares unknown alias "
                f"{alias!r}."
            )
        return binding.apply_loaded_payload(payload, source_context)

    def _project_output_slices(
        self,
        processed_stack: RuntimeArrayData,
        matching_files: Sequence[str],
    ) -> tuple[tuple[RuntimeArrayData, AlignedImageSliceContext | None], ...]:
        """Project the original output through its nominal image topology."""
        if isinstance(processed_stack, ImagePayloadMetadataCarrier) and (
            processed_stack.metadata.plane_axis is None
            or processed_stack.metadata.persists_whole_image()
        ):
            output_context = self._unwrapped_main_flow_output_context()
            contexts = (
                (output_context,)
                if output_context is not None
                else (
                    self._producer_output_contexts(matching_files)
                    if len(matching_files) == 1
                    else ()
                )
            )
            context = (
                contexts[0]
                if contexts
                else AlignedImageSliceContext.anonymous_main_flow()
            )
            return ((processed_stack, context),)
        if isinstance(processed_stack, AlignedImageStack):
            return tuple(processed_stack.projected_output_slices())
        output_context = self._unwrapped_main_flow_output_context()
        output_projection = RuntimeSliceProjection.preserved_context_for_value(
            processed_stack
        )
        if output_projection is not None:
            unstack_started_at = time.perf_counter()
            output_slices = list(
                RuntimeSliceProjection.value_for_slice(
                    processed_stack,
                    output_projection.selected_plane(slice_index),
                )
                for slice_index in range(output_projection.axis_size)
            )
            RuntimeProfileLogger.log(
                logger,
                "pattern_source_unstack",
                time.perf_counter() - unstack_started_at,
                step=self.execution_plan.step_index,
                step_name=self.execution_plan.step_name,
                slices=len(output_slices),
            )
            output_payloads = output_slices
        else:
            processed_data = image_payload_data(processed_stack)
            try:
                unstack_started_at = time.perf_counter()
                output_slices = list(
                    unstack_runtime_slices(
                        processed_data,
                        self.execution_plan.output_memory_type,
                        self.execution_plan.device_id_for(
                            self.execution_plan.output_memory_type
                        ),
                        expected_count=len(matching_files),
                    )
                )
                RuntimeProfileLogger.log(
                    logger,
                    "pattern_source_unstack",
                    time.perf_counter() - unstack_started_at,
                    step=self.execution_plan.step_index,
                    step_name=self.execution_plan.step_name,
                    slices=len(output_slices),
                )
            except ValueError as exc:
                output_shape = np.shape(processed_data)
                output_ndim = np.ndim(processed_data)
                logger.error("Function output is not an OpenHCS image stack.")
                logger.error("Output type: %s", type(processed_stack))
                logger.error("Output shape: %s", output_shape)
                logger.error("Output ndim: %s", output_ndim)
                raise ValueError(
                    "Main processing must result in an image stack shaped "
                    f"(N, H, W) or (N, H, W, C), got "
                    f"{output_shape}"
                ) from exc

            context_started_at = time.perf_counter()
            output_payloads = unstack_image_payload_context(
                processed_stack,
                output_slices,
                default_plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
            )
            RuntimeProfileLogger.log(
                logger,
                "pattern_payload_context_unstack",
                time.perf_counter() - context_started_at,
                step=self.execution_plan.step_index,
                step_name=self.execution_plan.step_name,
                slices=len(output_payloads),
            )
        slice_contexts = (
            (output_context,) * len(output_payloads)
            if output_context is not None
            else ()
        )
        if not slice_contexts and len(output_payloads) == len(matching_files):
            slice_contexts = self._producer_output_contexts(matching_files)
        if not slice_contexts:
            slice_contexts = tuple(
                AlignedImageSliceContext.anonymous_main_flow()
                for _payload in output_payloads
            )
        return tuple(zip(output_payloads, slice_contexts, strict=True))

    def _unwrapped_main_flow_output_context(
        self,
    ) -> AlignedImageSliceContext | None:
        ArtifactInputPlan.require_exact_map(
            self.execution_plan.artifact_inputs,
            boundary="Component artifact input",
        )
        return self.compiled_group.unwrapped_main_flow_output_context(
            self.selected_artifact_output_plans()
        )

    def _save_outputs(
        self,
        processed_stack: RuntimeArrayData,
        matching_files: list[str],
    ) -> list[ProducedOutputSemantics]:
        context = self.context
        unstack_started_at = time.perf_counter()
        projected_outputs = self._project_output_slices(processed_stack, matching_files)
        plan = self.execution_plan
        explicit_output_surfaces = isinstance(processed_stack, AlignedImageStack)
        if explicit_output_surfaces:
            stack_payload = processed_stack.copy_projected_output_stack(
                projected_outputs,
                memory_type=plan.output_memory_type,
                device_id=plan.device_id_for(plan.output_memory_type),
            )
        elif isinstance(processed_stack, ImagePayloadMetadataCarrier) and (
            processed_stack.metadata.plane_axis is None
            or processed_stack.metadata.persists_whole_image()
        ):
            stack_payload = ImagePayloadStackComposition.copy_whole_image(
                processed_stack,
                memory_type=plan.output_memory_type,
                device_id=plan.device_id_for(plan.output_memory_type),
            )
        else:
            stack_payload = processed_stack
        RuntimeProfileLogger.log(
            logger,
            "pattern_validate_unstack",
            time.perf_counter() - unstack_started_at,
            step=plan.step_index,
            step_name=plan.step_name,
            pattern=self.pattern_repr,
        )
        output_contexts = tuple(
            (
                context
                if context is not None
                else AlignedImageSliceContext.anonymous_main_flow()
            )
            for _payload, context in projected_outputs
        )
        save_started_at = time.perf_counter()

        def plane_axis_for_output(
            context: AlignedImageSliceContext,
        ) -> RuntimePlaneAxis | None:
            if isinstance(processed_stack, AlignedImageStack):
                return processed_stack.plane_axis_for_output_context(context)
            if isinstance(processed_stack, ImagePayloadMetadataCarrier):
                return image_payload_metadata(processed_stack).plane_axis
            return RuntimePlaneAxis.RUNTIME_SLICE

        output_slices = tuple(payload for payload, _context in projected_outputs)
        num_outputs = len(output_slices)
        num_inputs = len(matching_files)

        if num_outputs < num_inputs:
            logger.debug(
                "Function returned %d images from %d inputs - likely "
                "flattening operation",
                num_outputs,
                num_inputs,
            )
        elif num_outputs > num_inputs:
            logger.debug(
                "Function returned %s output slices from %s positional input "
                "files; extra slices must carry payload component identity.",
                num_outputs,
                num_inputs,
            )

        output_payloads = []
        output_payload_metadata = []
        output_paths_batch = []
        output_records = []

        overwritten_output_paths: list[str] = []
        output_directory_exists = context.filemanager.exists(
            str(self.execution_plan.output_dir),
            Backend.MEMORY.value,
        )
        for i, img_slice in enumerate(output_slices):
            input_filename = None
            if i < len(matching_files):
                input_filename = matching_files[i]
            output_path_request = FunctionOutputPathRequest(
                parser=context.microscope_handler.parser,
                output_dir=self.execution_plan.output_dir,
                output_payload=img_slice,
                input_path=input_filename,
                variable_components=self.execution_plan.variable_components,
                input_aligned_output=num_outputs == num_inputs,
                identity_cache=context.runtime_function_output_identity_cache,
            )
            try:
                output_identity = FunctionOutputIdentity.from_request(
                    output_path_request
                )
            except ValueError as exc:
                if input_filename is None:
                    raise ValueError(
                        f"Function returned {num_outputs} output slices but only "
                        f"{num_inputs} input files were available, and output slice "
                        f"{i} does not carry payload component identity."
                    ) from exc
                raise
            output_context = output_contexts[i]
            # Only explicit aligned output surfaces own filename qualifiers.
            # An unwrapped canonical artifact still owns its typed source
            # context, while its ordinary main-flow checkpoint keeps the
            # source filename independently of named artifact materialization.
            if explicit_output_surfaces and not output_context.is_anonymous_main_flow:
                output_identity = output_identity.with_filename_qualifier(
                    output_context.output_key
                )
            output_path = output_identity.path_for_request(output_path_request)
            output_path_text = str(output_path)
            img_slice = output_context.contextualize_image_payload(img_slice)
            output_metadata = image_payload_metadata(img_slice)
            output_component_metadata = output_identity.component_metadata(
                output_metadata.source_component_metadata,
            )
            if output_metadata.source_component_metadata != output_component_metadata:
                output_metadata = output_metadata.with_source_component_metadata(
                    output_component_metadata
                )
                img_slice = output_metadata.attach_to(img_slice)
            output_record = ProducedOutputSemantics.from_output(
                self.execution_plan,
                output_path_text,
                output_identity,
                output_context=output_context,
                image_metadata=output_metadata,
                main_flow_plane_axis=plane_axis_for_output(output_context),
            )

            if output_directory_exists and context.filemanager.exists(
                output_path_text,
                Backend.MEMORY.value,
            ):
                overwritten_output_paths.append(output_path_text)

            output_payloads.append(img_slice)
            output_payload_metadata.append(output_metadata)
            output_paths_batch.append(output_path_text)
            output_records.append(output_record)

        FunctionOutputIdentity.validate_output_paths(
            output_paths_batch,
            input_paths=matching_files,
            step_name=self.execution_plan.step_name,
            pattern_repr=self.pattern_repr,
            identities=output_records,
        )

        if overwritten_output_paths:
            for output_path_text in overwritten_output_paths:
                context.filemanager.delete(output_path_text, Backend.MEMORY.value)
            context.runtime_image_stack_cache.discard_paths(
                tuple(overwritten_output_paths)
            )

        context.filemanager.ensure_directory(
            str(self.execution_plan.output_dir),
            Backend.MEMORY.value,
        )
        context.filemanager.save_batch(
            output_payloads,
            output_paths_batch,
            Backend.MEMORY.value,
        )
        if stack_payload is not None:
            stack_payload = ImagePayloadStackComposition.with_saved_output_context(
                stack_payload,
                output_payloads,
                output_payload_metadata,
                single_output_plane_axis=(
                    plane_axis_for_output(output_contexts[0])
                    if len(output_payloads) == 1
                    else None
                ),
            )
            context.runtime_image_stack_cache.store(
                tuple(output_paths_batch),
                memory_type=self.execution_plan.output_memory_type,
                stack=stack_payload,
            )
            RuntimeProfileLogger.log(
                logger,
                "runtime_stack_cache_store",
                0.0,
                step=self.execution_plan.step_index,
                step_name=self.execution_plan.step_name,
                paths=len(output_paths_batch),
                memory_type=self.execution_plan.output_memory_type,
            )
        RuntimeProfileLogger.log(
            logger,
            "pattern_save_outputs",
            time.perf_counter() - save_started_at,
            step=plan.step_index,
            step_name=plan.step_name,
            pattern=self.pattern_repr,
        )
        return output_records

    def _cleanup_collapsed_domains(
        self,
        output_records: Sequence[ProducedOutputSemantics],
        matching_files: list[str],
        output_paths: Sequence[str],
    ) -> None:
        context = self.context
        num_outputs = len(output_records)
        num_inputs = len(matching_files)

        if num_outputs >= num_inputs:
            return

        if self.execution_plan.input_dir == self.execution_plan.output_dir:
            return

        retained_paths = {Path(path).as_posix() for path in output_paths}
        retained_paths.update(
            Path(record.output_path).as_posix()
            for record in step_output_manifest(context).produced_records_for(
                self.execution_plan
            )
        )
        for j in range(num_outputs, num_inputs):
            unused_filename = matching_files[j]
            unused_relative_path = self._input_relative_path(
                self.execution_plan.input_dir,
                unused_filename,
            )
            unused_path = self.execution_plan.output_dir / unused_relative_path
            if unused_path.as_posix() in retained_paths:
                continue
            if context.filemanager.exists(
                str(unused_path),
                Backend.MEMORY.value,
            ):
                context.runtime_image_stack_cache.discard_paths((str(unused_path),))
                context.filemanager.delete(
                    str(unused_path),
                    Backend.MEMORY.value,
                )
                logger.debug(
                    "Deleted unused collapsed-domain file after reduced "
                    "output cardinality: %s",
                    unused_path,
                )


@dataclass(frozen=True, slots=True, kw_only=True)
class ArtifactPatternGroupExecutionRequest(PatternGroupExecutionRequest):
    """Admit exact canonical producer values into an independent cohort."""

    def load_input_stack(
        self,
    ) -> tuple[list[str], RuntimeArrayData]:
        edges = self.execution_plan.stored_primary_input_edges_for_group(
            self.compiled_group,
            self.component_key,
        )
        if not edges:
            raise ValueError("Artifact cohort requires complete stored primary inputs.")
        payloads = []
        matching_files = []
        for edge in edges:
            artifact_input = RuntimeArtifactInput(
                edge_plan=edge,
                axis_scope=self.axis_scope,
                backend=Backend.MEMORY.value,
                source_binding_plan=self.source_binding_plan,
            )
            records = artifact_input.records(self.context.runtime_value_store)
            source_payload = (
                edge.spec.artifact_type.source_image_payload_from_runtime_value(
                    artifact_input.composed_value(records),
                )
            )
            if source_payload is None:
                raise ValueError(
                    f"Artifact cohort source {edge.spec.ref()!r} has no image context."
                )
            payloads.append(
                ImagePayloadStackComposition.copy_whole_image(
                    source_payload,
                    memory_type=self.execution_plan.input_memory_type,
                    device_id=self.execution_plan.device_id_for(
                        self.execution_plan.input_memory_type,
                    ),
                )
            )
            matching_files.extend(record.location.path for record in records)
        main_data_stack = ImagePayloadConsumption.NATURAL.compose_image_payload(
            self.execution_plan.step_name,
            tuple(payloads),
        ).payload
        return matching_files, main_data_stack

    def loaded_plane_count(
        self,
        matching_files: Sequence[str],
        payload: RuntimeArrayData,
    ) -> int:
        """Canonical payloads declare their runtime axis independently of paths."""
        count = RuntimeSliceProjection.slice_count_from_values((payload,))
        return 1 if count is None else count

    def loaded_fixed_component_values(
        self,
        payload: RuntimeArrayData,
    ) -> RuntimeFixedComponentValues:
        """Retain exact producer coordinates admitted by typed discovery."""
        return self.fixed_component_values

    def passthrough_producer_records(
        self,
        matching_files: Sequence[str],
    ) -> tuple[ProducedOutputSemantics, ...]:
        """Preserve input transport independently of artifact context admission."""
        records = step_output_manifest(self.context).producer_records_for(
            self.execution_plan,
        )
        if records is None:
            raise ValueError("Artifact input passthrough requires producer lineage.")
        return records


@dataclass(frozen=True, slots=True, kw_only=True)
class PatternGroupData(PatternGroupExecutionScope):
    """Complete loaded cohort and its original execution coordinates."""

    artifact_inputs: Mapping[ArtifactSpecRef, ArtifactInputPlan]
    artifact_outputs: ArtifactOutputPlans
    runtime_plane_index: int
    runtime_plane_count: int
    matching_files: list[str]
    main_data_stack: RuntimeArrayData

    @classmethod
    def from_loaded_group(
        cls,
        request: "PatternGroupExecutionRequest",
        matching_files: list[str],
        main_data_stack: RuntimeArrayData,
    ) -> "PatternGroupData":
        ArtifactInputPlan.require_exact_map(
            request.execution_plan.artifact_inputs,
            boundary="Component artifact input",
        )
        artifact_inputs = dict(request.execution_plan.artifact_inputs)
        artifact_outputs = request.selected_artifact_output_plans()
        logger.debug(
            "Selected artifact outputs for component %s: %s",
            request.component_key,
            artifact_outputs,
        )
        return cls(
            matching_files=matching_files,
            main_data_stack=main_data_stack,
            context=request.context,
            execution_plan=request.execution_plan,
            compiled_group=request.compiled_group,
            artifact_inputs=artifact_inputs,
            artifact_outputs=artifact_outputs,
            runtime_plane_index=request.component_index,
            runtime_plane_count=request.loaded_plane_count(
                matching_files,
                main_data_stack,
            ),
            component_value=request.component_value,
            fixed_component_values=request.loaded_fixed_component_values(
                main_data_stack
            ),
        )

    def require_invocations(self) -> None:
        if self.compiled_group.invocations:
            return
        raise ValueError(
            f"Compiled function group {self.compiled_group.group_key} has no invocations."
        )

    def execute_chain(self) -> RuntimeArrayData | NoMainFlowOutput:
        self.require_invocations()
        current_stack: RuntimeArrayData | NoMainFlowOutput = self.main_data_stack
        current_memory_type = self.execution_plan.input_memory_type
        debug_sink = debug_event_sink_from_context(self.context)
        declared_source_bindings = self.execution_plan.source_binding_plan
        for invocation in self.compiled_group.invocations:
            executor = FunctionCoreExecutor.from_group_invocation(
                self,
                invocation,
                main_data_arg=current_stack,
                source_memory_type=current_memory_type,
                declared_source_bindings=declared_source_bindings,
            )
            if executor is None:
                continue
            captures_debug = debug_sink.captures_invocation_events()
            if captures_debug and debug_sink.should_skip_invocation(
                executor.debug_cursor()
            ):
                continue

            invocation_started_at = time.perf_counter()
            try:
                current_stack = executor.execute(
                    debug_sink=debug_sink if captures_debug else None,
                )
            except Exception as exc:
                if captures_debug:
                    debug_sink.record(
                        executor.debug_event(
                            DebugEventType.EXCEPTION,
                            exception=exc,
                        )
                    )
                raise
            invocation_seconds = time.perf_counter() - invocation_started_at
            if captures_debug:
                after_event = executor.debug_event(
                    DebugEventType.AFTER_INVOCATION,
                    timing_seconds=invocation_seconds,
                )
                debug_sink.record(after_event)
                if debug_sink.should_stop_after_invocation(after_event):
                    break
            RuntimeProfileLogger.log(
                logger,
                "invocation_total",
                invocation_seconds,
                function=invocation.key.function_name,
                group=invocation.key.group_key,
                position=invocation.key.position,
            )
            if isinstance(current_stack, NoMainFlowOutput):
                return current_stack
            current_memory_type = executor.invocation.contract.output_memory_type
        if self.compiled_group.preserves_input_main_flow() and all(
            invocation.contract.artifact_output_policy.records_outputs
            for invocation in self.compiled_group.invocations
        ):
            return NoMainFlowOutput()
        return current_stack


def _save_artifact_value(
    context: ProcessingContext,
    output_plan: ArtifactOutputPlan,
    value: RuntimePayload,
    source_payload: RuntimePayload,
    *,
    execution_scope: RuntimeExecutionAxisScope,
    group_key: str | None,
    plane_projector: RuntimePlaneAxisProjector | None,
    materialization_source_metadata: ImagePayloadMetadata | None = None,
) -> RuntimePayload:
    """Validate and save one planned artifact value to the memory VFS."""
    resolved_output_plan = output_plan.for_invocation_group(group_key)
    vfs_path = resolved_output_plan.path
    runtime_value = RuntimeValue.normalize_output_from_projector(
        resolved_output_plan,
        value,
        source_payload=source_payload,
        plane_projector=plane_projector,
        execution_scope=execution_scope,
        materialization_source_metadata=materialization_source_metadata,
    )

    location = RuntimeArtifactLocation(
        path=vfs_path,
        backend=Backend.MEMORY.value,
    )
    runtime_value_store = context.runtime_value_store
    runtime_value_store.replace(
        runtime_value,
        path=location.path,
        backend=location.backend,
    )
    replace_runtime_artifact_payload(
        context.filemanager,
        runtime_value.data,
        location,
    )
    return runtime_value.data






@dataclass(frozen=True, slots=True)
class FunctionCoreExecutor:
    """Execute one scoped callable invocation and route declared artifact I/O."""

    group_data: PatternGroupData
    invocation: CompiledFunctionInvocation
    artifact_inputs: Mapping[
        InvocationArtifactInputProjectionKey, InvocationArtifactInputEdgePlan
    ]
    artifact_outputs: ArtifactOutputPlans
    group_key: str | None
    plane_projection: RuntimePlaneProjection
    main_data_arg: RuntimeArrayData
    source_memory_type: str

    @classmethod
    def from_group_invocation(
        cls,
        group_data: PatternGroupData,
        invocation: CompiledFunctionInvocation,
        *,
        main_data_arg: RuntimeArrayData,
        source_memory_type: str,
        declared_source_bindings: CompiledSourceBindingPlan,
    ) -> "FunctionCoreExecutor | None":
        """Admit the selected compiled edges and outputs for this live invocation."""
        group_key = invocation.key.runtime_group_key(group_data.component_value)
        active_source_bindings = group_data.active_main_flow_source_binding_plan(
            main_data_arg
        )
        active_outputs = invocation.output_plans_for_component(
            group_data.execution_plan.execution_group_scope,
            group_data.component_key,
        )
        if active_outputs is None:
            return None
        inputs = {}
        for edge_key, edge in invocation.select_inputs(
            group_data.artifact_inputs,
            active_output_plans=active_outputs,
        ).items():
            if (
                edge.main_flow_projection is not None
                and declared_source_bindings.declares_artifact_ref(edge.spec.ref())
                and not active_source_bindings.declares_artifact_ref(edge.spec.ref())
            ):
                if not invocation.adapter_manages_artifact_inputs:
                    continue
                if edge.storage_plan is not None:
                    raise ValueError(
                        f"Stored primary input {edge.spec.ref()!r} is not represented "
                        "by this main-flow payload; its producer cannot substitute "
                        "for the current payload epoch."
                    )
                edge = replace(edge, main_flow_projection=None)
            inputs[edge_key] = edge
        return cls(
            group_data=group_data,
            invocation=invocation,
            artifact_inputs=inputs,
            artifact_outputs=invocation.select_outputs(
                group_data.artifact_outputs,
                compiled_output_plans=active_outputs,
            ),
            group_key=group_key,
            plane_projection=RuntimePlaneProjection.stack(
                group_data.runtime_plane_count
            ),
            main_data_arg=main_data_arg,
            source_memory_type=source_memory_type,
        )

    def runtime_adapter_request(
        self,
        source_payload: RuntimePayload,
    ) -> RuntimeAdapterRequest:
        return RuntimeAdapterRequest(
            context=self.group_data.context,
            callable_contract=self.invocation.contract,
            artifact_inputs=self.artifact_inputs,
            artifact_outputs=self.artifact_outputs,
            group_key=self.group_key,
            plane_projection=self.plane_projection,
            source_payload=source_payload,
            source_binding_plan=self.group_data.source_binding_plan,
            axis_scope=self.group_data.axis_scope,
            variable_components=tuple(
                self.group_data.execution_plan.variable_components
            ),
            source_load_plan=self.group_data.execution_plan.source_load_plan,
        )

    def declared_source_payload(
        self,
        source_ref: ArtifactSpecRef,
        primary_source_payload: RuntimePayload,
        *,
        loaded_artifact_payloads: Mapping[ArtifactSpecRef, RuntimePayload],
    ) -> RuntimePayload:
        input_spec = self.invocation.contract.artifact_inputs.by_ref(source_ref)
        if input_spec is None:
            raise ValueError(
                f"Invocation {self.invocation.key!r} does not declare source artifact "
                f"{source_ref!r}."
            )
        stored_payload = loaded_artifact_payloads.get(source_ref)
        source_binding = self.group_data.source_binding_plan.binding_for_artifact_ref(
            source_ref
        )
        main_flow_edges = tuple(
            edge
            for edge in self.artifact_inputs.values()
            if edge.spec.ref() == source_ref and edge.main_flow_projection is not None
        )
        uses_main_flow = bool(
            stored_payload is None and source_binding is None and main_flow_edges
        )
        resolved_origins = sum(
            (
                stored_payload is not None,
                source_binding is not None,
                uses_main_flow,
            )
        )
        if resolved_origins != 1:
            raise ValueError(
                f"Invocation {self.invocation.key!r} source artifact {source_ref!r} "
                "must resolve to exactly one compiled producer, source binding, or "
                f"main-flow input; resolved {resolved_origins}."
            )
        if stored_payload is not None:
            return stored_payload
        if source_binding is not None:
            return cast(
                RuntimePayload,
                self.runtime_adapter_request(
                    primary_source_payload
                ).source_artifact_payload(source_ref),
            )
        if len(main_flow_edges) != 1:
            raise ValueError(
                f"Invocation {self.invocation.key!r} source artifact {source_ref!r} "
                "must resolve through exactly one selected main-flow input edge; "
                f"resolved {len(main_flow_edges)}."
            )
        main_flow_projection = main_flow_edges[0].main_flow_projection
        if main_flow_projection is MainFlowInputProjection.COMPLETE_PAYLOAD:
            return primary_source_payload
        if main_flow_projection is not MainFlowInputProjection.DECLARED_SOURCE_IMAGE:
            raise ValueError(
                f"Invocation {self.invocation.key!r} source artifact {source_ref!r} "
                "consumes main flow without a compiled projection."
            )
        return project_declared_source_identity(primary_source_payload, source_ref)

    def load_artifact_inputs(
        self,
        final_kwargs: dict[str, RuntimeCallableArgument],
        source_payload: RuntimePayload,
    ) -> dict[ArtifactSpecRef, RuntimePayload]:
        if not self.should_load_artifact_inputs():
            return {}
        logger.info(
            f"Artifact inputs for {self.invocation.contract.function_name}: {self.artifact_inputs}"
        )
        loaded_artifact_payloads: dict[ArtifactSpecRef, RuntimePayload] = {}
        parameter_values: dict[str, list[RuntimeValue]] = {}
        for input_plan in self.artifact_inputs.values():
            parameter_name = input_plan.spec.parameter_name
            if not input_plan.requires_callable_binding():
                continue
            if parameter_name is None:
                raise ValueError(
                    f"Compiled invocation {self.invocation.key!r} runtime-loaded input "
                    f"edge {input_plan.key!r} has no callable parameter."
                )
            artifact_ref = input_plan.spec.ref()
            projected_values = (
                self.load_artifact_input(input_plan.spec.name, input_plan)
                if input_plan.uses_runtime_storage()
                and input_plan.main_flow_projection is None
                else (
                    RuntimeValue.from_spec(
                        input_plan.spec,
                        input_plan.resolve_unstored_payload(self, source_payload),
                        execution_scope=self.group_data.axis_scope,
                    ),
                )
            )
            loaded_value = RuntimeValue.compose(projected_values)
            loaded_artifact_payloads[artifact_ref] = loaded_value
            parameter_values.setdefault(parameter_name, []).extend(projected_values)
        for parameter_name, projected_values in parameter_values.items():
            final_kwargs[parameter_name] = RuntimeValue.compose(tuple(projected_values))
        return loaded_artifact_payloads

    def should_load_artifact_inputs(self) -> bool:
        return bool(
            any(
                edge.requires_callable_binding()
                for edge in self.artifact_inputs.values()
            )
            and not self.invocation.adapter_manages_artifact_inputs
        )

    def load_artifact_input(
        self,
        arg_name: str,
        edge_plan: InvocationArtifactInputEdgePlan,
    ) -> tuple[RuntimeValue, ...]:
        storage_plan = edge_plan.storage_plan
        if storage_plan is None:
            raise ValueError("Artifact input loading requires a storage-backed edge.")
        logger.info(
            "Loading artifact input '%s' from path '%s' (memory backend)",
            arg_name,
            storage_plan.path,
        )
        load_started_at = time.perf_counter()
        try:
            loaded_values = RuntimeArtifactInput(
                edge_plan=edge_plan,
                axis_scope=self.group_data.axis_scope,
                backend=Backend.MEMORY.value,
                source_binding_plan=self.group_data.source_binding_plan,
            ).projected_values(self.group_data.context.runtime_value_store)
        except Exception as exc:
            logger.error(
                "Failed to load artifact input '%s' from '%s': %s",
                arg_name,
                storage_plan.path,
                exc,
                exc_info=True,
            )
            raise
        RuntimeProfileLogger.log(
            logger,
            "artifact_input_load",
            time.perf_counter() - load_started_at,
            function=self.invocation.contract.function_name,
            artifact=arg_name,
            artifact_type=storage_plan.artifact_type.value,
        )
        return loaded_values

    def debug_cursor(self) -> DebugCursor:
        return DebugCursor.from_invocation(
            step_index=self.group_data.execution_plan.step_index,
            step_scope_id=self.group_data.execution_plan.step_scope_id,
            invocation=self.invocation,
            pattern_group_identity=str(self.group_data.runtime_plane_index),
        )

    def debug_artifacts(
        self,
        artifact_plans: ArtifactInputPlans | ArtifactOutputPlans,
        artifact_values: Mapping[ArtifactSpecRef, object] | None = None,
    ) -> DebugArtifactRefProjection:
        return DebugArtifactRefProjection.from_artifact_plans(
            artifact_plans=artifact_plans,
            cursor=self.debug_cursor(),
            artifact_values=artifact_values,
        )

    def debug_event(
        self,
        event_type: DebugEventType,
        *,
        exception: Exception | None = None,
        timing_seconds: float | None = None,
        invocation_parameters: tuple[DebugInvocationParameter, ...] = (),
        input_artifact_values: Mapping[ArtifactSpecRef, object] | None = None,
    ) -> DebugEvent:
        return DebugEvent.for_invocation(
            event_type=event_type,
            cursor=self.debug_cursor(),
            step_name=self.group_data.execution_plan.step_name,
            callable_name=self.invocation.key.function_name,
            axis_id=self.group_data.execution_plan.axis_id,
            input_artifacts=self.debug_artifacts(
                {
                    edge.storage_plan.ref(): edge.storage_plan
                    for edge in self.artifact_inputs.values()
                    if edge.storage_plan is not None
                },
                input_artifact_values,
            ),
            output_artifacts=self.debug_artifacts(self.artifact_outputs),
            exception=exception,
            timing_seconds=timing_seconds,
            invocation_parameters=invocation_parameters,
        )

    def execute(
        self,
        *,
        debug_sink: DebugEventSink | None = None,
    ) -> RuntimePayload | NoMainFlowOutput:
        converted_data = self.invocation.convert_input(
            image_payload_data(self.main_data_arg),
            self.source_memory_type,
        )
        source_payload = with_image_payload_data(self.main_data_arg, converted_data)
        main_data_arg = self.invocation.main_flow_call_argument(source_payload)
        final_kwargs = dict(self.invocation.runtime_kwargs)
        loads_artifact_inputs = self.should_load_artifact_inputs()
        loaded_artifact_payloads: dict[ArtifactSpecRef, RuntimePayload] = {}
        if loads_artifact_inputs:
            loaded_artifact_payloads = self.load_artifact_inputs(
                final_kwargs,
                source_payload,
            )
        self.bind_runtime_owned_parameters(final_kwargs)
        self.bind_runtime_adapter(final_kwargs, source_payload)
        raw_output = self.invoke(
            main_data_arg,
            final_kwargs,
            loaded_artifact_payloads=loaded_artifact_payloads,
            debug_sink=debug_sink,
        )
        return self.save_artifact_outputs(
            raw_output,
            source_payload,
            loaded_artifact_payloads=loaded_artifact_payloads,
        )

    def execution_group_source_payload(
        self,
        source_payload: RuntimePayload,
    ) -> RuntimePayload:
        """Return source payload metadata carrying the current grouped identity."""
        component = self.group_data.execution_plan.execution_group_scope.component
        if component is None or self.group_key is None:
            return source_payload
        metadata = image_payload_metadata(source_payload)
        component_metadata = metadata.source_component_metadata or {}
        component_metadata = with_source_component_metadata(
            component_metadata,
            component,
            self.group_key,
        )
        return metadata.with_source_component_metadata(component_metadata).attach_to(
            source_payload
        )

    def bind_runtime_owned_parameters(
        self,
        final_kwargs: dict[str, RuntimeCallableArgument],
    ) -> None:
        context_parameter_name = self.invocation.contract.runtime_context_parameter
        if context_parameter_name is not None:
            final_kwargs[context_parameter_name] = self.group_data.context

    def bind_runtime_adapter(
        self,
        final_kwargs: dict[str, RuntimeCallableArgument],
        source_payload: RuntimePayload,
    ) -> None:
        runtime_adapter = self.invocation.contract.runtime_adapter
        if runtime_adapter is None:
            return
        adapter_parameter = self.invocation.adapter_parameter_name
        adapter_started_at = time.perf_counter()
        final_kwargs[adapter_parameter] = runtime_adapter.factory(
            self.runtime_adapter_request(source_payload)
        )
        RuntimeProfileLogger.log(
            logger,
            "runtime_adapter_factory",
            time.perf_counter() - adapter_started_at,
            function=self.invocation.contract.function_name,
            adapter=adapter_parameter,
        )

    def invoke(
        self,
        main_data_arg: RuntimeCallableArgument,
        final_kwargs: dict[str, RuntimeCallableArgument],
        *,
        loaded_artifact_payloads: Mapping[ArtifactSpecRef, RuntimePayload],
        debug_sink: DebugEventSink | None,
    ) -> RuntimeFunctionOutput:
        logger.info("Executing function: %s", self.invocation.contract.function_name)
        func_callable = self.invocation.runtime_callable
        contract = self.invocation.contract
        primary_parameter = self.invocation.primary_input_parameter_name
        plane_projector: RuntimePlaneAxisProjector = self.plane_projection
        runtime_adapter = self.invocation.contract.runtime_adapter
        if runtime_adapter is not None:
            adapter_parameter = self.invocation.adapter_parameter_name
            adapter_value = final_kwargs[adapter_parameter]
            if isinstance(adapter_value, RuntimePlaneAxisProjector):
                plane_projector = adapter_value
        if debug_sink is not None:
            if primary_parameter is None:
                raise TypeError(
                    f"Callable {self.invocation.contract.function_name!r} has no declared primary input "
                    "parameter for runtime invocation diagnostics."
                )
            bound_parameters = dict(final_kwargs)
            bound_parameters[primary_parameter] = main_data_arg
            debug_sink.record(
                self.debug_event(
                    DebugEventType.BEFORE_INVOCATION,
                    invocation_parameters=DebugInvocationParameter.from_kwargs(
                        bound_parameters,
                        plane_projector=plane_projector,
                    ),
                    input_artifact_values=loaded_artifact_payloads,
                )
            )
        call_started_at = time.perf_counter()
        try:
            with self.invocation.execution_device_scope():
                raw_output = func_callable(
                    main_data_arg,
                    **final_kwargs,
                )
        except RuntimeSliceProjectionDeclarationError as exc:
            bound_parameters = dict(final_kwargs)
            if primary_parameter is not None:
                bound_parameters[primary_parameter] = main_data_arg
            cursor = self.debug_cursor()
            invocation_parameters = DebugInvocationParameter.from_kwargs(
                bound_parameters,
                plane_projector=plane_projector,
            )
            selected_plane = plane_projector.runtime_slice_plane_index()
            selected_plane_status = (
                "preserved_stack" if selected_plane is None else str(selected_plane)
            )
            artifact_refs = (
                *(edge.spec.ref() for edge in tuple(self.artifact_inputs.values())),
                *self.artifact_outputs,
            )
            raise type(exc)(
                f"{exc} Invocation boundary: step_index={cursor.step_index}; "
                f"step_name={self.group_data.execution_plan.step_name!r}; "
                f"function_invocation_key={self.invocation.key!r}; "
                f"module={contract.module_name!r}; "
                f"callable={contract.function_name!r}; "
                f"artifact_spec_refs={artifact_refs!r}; "
                f"kwarg_names={tuple(sorted(final_kwargs))!r}; "
                f"nominal_values={tuple((parameter.name, parameter.value_repr) for parameter in invocation_parameters)!r}; "
                f"selected_runtime_plane={selected_plane_status}; "
                "execution_axis_cardinality="
                f"{plane_projector.runtime_slice_axis_size()!r}; "
                "image_payload_execution_mode="
                f"{contract.runtime_image_execution_mode}; "
                f"processing_contract={contract.processing_contract}."
            ) from exc
        RuntimeProfileLogger.log(
            logger,
            "function_call",
            time.perf_counter() - call_started_at,
            function=self.invocation.contract.function_name,
        )
        return raw_output

    def save_artifact_outputs(
        self,
        raw_output: RuntimeFunctionOutput,
        source_payload: RuntimePayload,
        *,
        loaded_artifact_payloads: Mapping[ArtifactSpecRef, RuntimePayload],
    ) -> RuntimePayload | NoMainFlowOutput:
        """Save declared outputs and qualify unsaved canonical returns afterward."""
        if self.invocation.adapter_records_artifact_outputs:
            return self.save_module_recorded_output(raw_output)
        output_plans = tuple(self.artifact_outputs.values())
        declared_specs = self.invocation.contract.artifact_outputs
        if not declared_specs:
            if isinstance(raw_output, tuple):
                raise TypeError(
                    "Tuple returns require declared special-output slots; multiple "
                    "main-flow images must be packed as AlignedImageStack."
                )
            main_output = raw_output
        else:
            _returned_values, matched_outputs = (
                self.invocation.contract.resolve_returned_plan_values(
                    raw_output,
                    output_plans,
                )
            )
            saved_values = {
                output_plan.ref(): self.save_artifact_output(
                    output_plan.name,
                    output_plan,
                    output_value,
                    source_payload,
                    loaded_artifact_payloads=loaded_artifact_payloads,
                )
                for output_plan, _output_spec, output_value in matched_outputs
            }
            canonical_refs = self.invocation.contract.canonical_return_output_refs
            main_outputs = tuple(
                (output_plan, output_spec, saved_values[output_plan.ref()])
                for output_plan, output_spec, _output_value in matched_outputs
                if output_plan.ref() in canonical_refs
            )
            if main_outputs:
                # These values already own their declared source transformation.
                # Reapplying the input context would restore consumed planes.
                output_values = tuple(
                    output_value
                    for _output_plan, _output_spec, output_value in main_outputs
                )
                if len(output_values) == 1:
                    return output_values[0]
                return ImageOutputBundle(
                    output_values,
                    AlignedImageSliceContext.main_flow_for_output_plans(
                        tuple(
                            output_plan
                            for output_plan, _output_spec, _output_value in main_outputs
                        )
                    ),
                )
            main_output = split_runtime_output(raw_output)[0]
        if isinstance(main_output, NoMainFlowOutput):
            return main_output
        output_source_payload = self.invocation.main_flow_output_source_payload(
            self.execution_group_source_payload(source_payload)
        )
        return ImageArtifactType.contextualize_output_from_projector(
            output_source_payload,
            main_output,
            None,
            self.plane_projection,
        )

    def save_module_recorded_output(
        self,
        raw_output: RuntimeFunctionOutput,
    ) -> RuntimePayload | NoMainFlowOutput:
        """Return the main-flow value from a module that records outputs internally."""
        if isinstance(raw_output, NoMainFlowOutput):
            return raw_output
        if isinstance(raw_output, tuple):
            raise TypeError(
                "Module artifact contracts with runtime adapters record declared "
                "outputs internally; they must return one main-flow payload, not a "
                "tuple of artifact values."
            )
        return raw_output

    def save_artifact_output(
        self,
        output_key: str,
        output_plan: ArtifactOutputPlan,
        value: RuntimePayload,
        source_payload: RuntimePayload,
        *,
        loaded_artifact_payloads: Mapping[ArtifactSpecRef, RuntimePayload],
    ) -> RuntimePayload:
        logger.info(
            "Saving artifact output '%s' to VFS path '%s' (memory backend)",
            output_key,
            output_plan.path,
        )
        save_started_at = time.perf_counter()
        artifact_source_payload = self.artifact_output_source_payload(
            output_plan,
            source_payload,
            loaded_artifact_payloads=loaded_artifact_payloads,
        )
        output_source_payload = self.invocation.main_flow_output_source_payload(
            self.execution_group_source_payload(artifact_source_payload)
        )
        materialization_source_metadata = None
        materialization_source_ref = output_plan.materialization_source()
        if (
            materialization_source_ref is not None
            and materialization_source_ref != output_plan.source_context_source()
        ):
            materialization_source_payload = self.declared_source_payload(
                materialization_source_ref,
                source_payload,
                loaded_artifact_payloads=loaded_artifact_payloads,
            )
            materialization_source_metadata = image_payload_metadata(
                materialization_source_payload
            )
        saved_value = _save_artifact_value(
            self.group_data.context,
            output_plan,
            value,
            output_source_payload,
            execution_scope=self.group_data.axis_scope,
            group_key=self.group_key,
            materialization_source_metadata=materialization_source_metadata,
            plane_projector=self.plane_projection,
        )
        RuntimeProfileLogger.log(
            logger,
            "artifact_output_save",
            time.perf_counter() - save_started_at,
            function=self.invocation.contract.function_name,
            artifact=output_key,
            artifact_type=output_plan.artifact_type.value,
        )
        return saved_value

    def artifact_output_source_payload(
        self,
        output_plan: ArtifactOutputPlan,
        primary_source_payload: RuntimePayload,
        *,
        loaded_artifact_payloads: Mapping[ArtifactSpecRef, RuntimePayload],
    ) -> RuntimePayload:
        source_ref = output_plan.source_context_source()
        if source_ref is None:
            return primary_source_payload
        return self.declared_source_payload(
            source_ref,
            primary_source_payload,
            loaded_artifact_payloads=loaded_artifact_payloads,
        )


def _process_single_pattern_group(request: PatternGroupExecutionRequest) -> None:
    """Process one image pattern group through its assigned callable pattern."""
    request.run()
