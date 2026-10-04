"""Axis-scoped compiler session for pipeline compilation stages."""

from __future__ import annotations

from dataclasses import dataclass, field, fields, is_dataclass, replace
from pathlib import Path
from typing import TYPE_CHECKING, Any, Mapping, MutableMapping, Sequence, get_type_hints

from objectstate import DataclassFieldAccess

from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.source_metadata import SourceMetadataMapping
from openhcs.core.source_workspace_projection import VirtualWorkspaceSourceProjection
from openhcs.core.steps.abstract import AbstractStep
from openhcs.core.steps.function_step import FunctionStep
from openhcs.core.function_patterns import (
    normalize_function_pattern,
    NormalizedFunctionItem,
    strip_disabled_functions,
)
from openhcs.core.invocation_artifacts import (
    InvocationContractProvider,
    InvocationContractPlan,
    ArtifactDeclarationStepContext,
    InvocationArtifactDeclarationProviderLike,
    callable_contract_artifact_declarations,
    PipelineInvocationContractProviderAuthority,
)
from openhcs.core.vfs_protocol import (
    FileManagerLike,
    PlatePathDeclaration,
)

if TYPE_CHECKING:
    from openhcs.core.config import GlobalPipelineConfig
    from openhcs.core.pipeline.artifact_planning import ArtifactGraph
    from openhcs.core.artifacts import ArtifactSpecRef
    from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator


@dataclass(frozen=True, slots=True)
class CompilationPlateScope:
    """Plate-root identity used for compiler ObjectState scopes and paths."""

    path: Path

    def __post_init__(self) -> None:
        if not self.path.is_absolute():
            raise ValueError(
                f"Compilation plate scope must be absolute, got {self.path}."
            )

    @classmethod
    def from_context(cls, context: ProcessingContext) -> "CompilationPlateScope":
        if context.plate_path is None:
            raise ValueError("Compilation plate scope requires context.plate_path.")
        return cls(Path(context.plate_path))

    @classmethod
    def from_path(cls, plate_path: Path | str | None) -> "CompilationPlateScope":
        if plate_path is None:
            raise ValueError("Compilation plate scope requires a plate path.")
        return cls(Path(plate_path))

    @property
    def object_state_scope_id(self) -> str:
        return str(self.path)

    def resolve_address(
        self,
        value: str | Path,
        *,
        filemanager: FileManagerLike,
        backend: str,
    ) -> Path:
        """Resolve one address through VFS with this exact plate base."""

        resolved = Path(
            filemanager.resolve_address(
                value,
                backend,
                base_path=self.path,
            )
        )
        if not resolved.is_absolute():
            raise ValueError(
                "VFS path resolution must return an absolute address: "
                f"{value!r} -> {resolved}."
            )
        return resolved


@dataclass(frozen=True, slots=True)
class CompilationPathResolver:
    """Resolve declaration-owned paths for one compilation plate."""

    plate_scope: CompilationPlateScope
    filemanager: FileManagerLike
    backend: str

    def resolve(
        self,
        value: str | Path,
        declaration: PlatePathDeclaration,
        *,
        owner: str,
    ) -> Path:
        try:
            target = self.plate_scope.resolve_address(
                value,
                filemanager=self.filemanager,
                backend=self.backend,
            )
            declaration.validate_target(
                target,
                filemanager=self.filemanager,
                backend=self.backend,
            )
            return target
        except Exception as error:
            error.add_note(
                f"While resolving {owner}: authored={value!r}, "
                f"plate_root={self.plate_scope.path}, backend={self.backend!r}."
            )
            raise


def resolve_declared_dataclass_paths(
    value: Any,
    resolver: CompilationPathResolver,
    *,
    owner: str,
) -> Any:
    """Return an immutable dataclass copy with declared paths resolved."""

    if not is_dataclass(value) or isinstance(value, type):
        return value
    annotations = get_type_hints(type(value), include_extras=True)
    replacements: dict[str, object] = {}
    for dataclass_field in fields(value):
        field_value = DataclassFieldAccess.raw_value(value, dataclass_field.name)
        declaration = PlatePathDeclaration.from_annotation(
            annotations.get(dataclass_field.name)
        )
        if declaration is not None and field_value is not None:
            if not isinstance(field_value, (str, Path)):
                raise TypeError(
                    f"{owner}.{dataclass_field.name} declares a plate path but "
                    f"contains {type(field_value).__name__}."
                )
            resolved_value = resolver.resolve(
                field_value,
                declaration,
                owner=f"{owner}.{dataclass_field.name}",
            )
        else:
            resolved_value = resolve_declared_dataclass_paths(
                field_value,
                resolver,
                owner=f"{owner}.{dataclass_field.name}",
            )
        if resolved_value is not field_value:
            replacements[dataclass_field.name] = resolved_value
    return replace(value, **replacements) if replacements else value


@dataclass(frozen=True, slots=True)
class ResolvedPipelineDefinition(InvocationContractProvider):
    """Capture enabled saved declarations and their scope/provenance facts.

    Axis sessions derive metadata kwargs from this view and share its provider;
    authored FunctionSteps keep their public function-pattern syntax.
    """

    steps: Sequence[AbstractStep]
    step_scope_ids: Mapping[int, str]
    step_provenance: Mapping[int, Mapping[str, tuple[str | None, type | None]]]
    declaration_provider: InvocationArtifactDeclarationProviderLike = field(
        default=callable_contract_artifact_declarations, repr=False, compare=False
    )
    _artifact_graphs: tuple[ArtifactGraph, ...] | None = field(
        default=None, init=False, repr=False, compare=False
    )
    _artifact_contexts: tuple[ArtifactDeclarationStepContext, ...] = field(
        default=(), init=False, repr=False, compare=False
    )
    _future_artifact_inputs: tuple[frozenset[ArtifactSpecRef], ...] = field(
        default=(), init=False, repr=False, compare=False
    )

    def _admit_artifact_graphs(self) -> None:
        """Admit fixed contracts and forward topology once, before axis fanout."""
        if self._artifact_graphs is not None:
            return
        from openhcs.constants import GroupBy
        from openhcs.core.pipeline.artifact_planning import (
            ArtifactGraph,
            extract_artifact_declarations,
        )
        from openhcs.core.pipeline.funcstep_contract_validator import (
            FuncStepContractValidator,
        )

        provider = PipelineInvocationContractProviderAuthority.provider_for_pipeline(
            self
        )
        graphs: list[ArtifactGraph] = []
        contexts: list[ArtifactDeclarationStepContext] = []
        context = ArtifactDeclarationStepContext.empty()
        for index, step in enumerate(self.steps):
            group_by = (
                FuncStepContractValidator.normalized_group_by(
                    step.processing_config.group_by,
                    step.processing_config.variable_components,
                    step.name,
                    step.func,
                )
                if isinstance(step, FunctionStep)
                else GroupBy.NONE
            )
            context = replace(
                context, step_name=step.name, step_index=index
            ).with_source_binding_scope(
                source_bindings=step.source_bindings,
                group_by=group_by,
                input_source=step.processing_config.input_source,
                source_groups=(None,),
            )
            contexts.append(context)
            graph = (
                extract_artifact_declarations(
                    step.func,
                    declaration_provider=self.declaration_provider,
                    invocation_contract_provider=provider,
                    step_context=context,
                )
                if isinstance(step, FunctionStep)
                else ArtifactGraph.empty()
            )
            for item in () if graph.pattern is None else graph.pattern.iter_items():
                item.contract.validate_artifact_input_parameter_bindings()
                graph.invocation_declarations[
                    item.key
                ].validate_artifact_output_declarations()
            graph.config_parameters_for_step(step.name)
            graph.input_lineage_order
            graphs.append(graph)
            context = graph.advance_declaration_context(context)
        future_inputs: set[ArtifactSpecRef] = set()
        future: list[frozenset[ArtifactSpecRef]] = []
        for graph in reversed(graphs):
            future.append(frozenset(future_inputs))
            future_inputs.update(
                consumer.spec.ref()
                for consumer in (
                    *graph.consumers,
                    *graph.non_plan_consumers,
                )
            )
        # Publish all admitted state together; no factory/provider can observe a
        # partially admitted graph through the pipeline's public provider view.
        object.__setattr__(self, "_artifact_contexts", tuple(contexts))
        object.__setattr__(self, "_future_artifact_inputs", tuple(reversed(future)))
        object.__setattr__(self, "_artifact_graphs", tuple(graphs))

    @property
    def artifact_graphs(self) -> tuple[ArtifactGraph, ...]:
        self._admit_artifact_graphs()
        return self._artifact_graphs

    @property
    def artifact_contexts(self) -> tuple[ArtifactDeclarationStepContext, ...]:
        self._admit_artifact_graphs()
        return self._artifact_contexts

    @property
    def future_artifact_inputs(self) -> tuple[frozenset[ArtifactSpecRef], ...]:
        self._admit_artifact_graphs()
        return self._future_artifact_inputs

    @property
    def invocation_contract_provider(self) -> InvocationContractProvider:
        """Use admitted occurrence plans; temporary provider factories are released."""
        self._admit_artifact_graphs()
        return self

    def __call__(
        self,
        invocation: NormalizedFunctionItem,
        step_context: ArtifactDeclarationStepContext,
    ) -> InvocationContractPlan | None:
        self._admit_artifact_graphs()
        return self._artifact_graphs[step_context.step_index].invocation_contract_plans[
            invocation.key
        ]

    def __post_init__(self) -> None:
        missing_scopes = [
            index
            for index in range(len(self.steps))
            if index not in self.step_scope_ids or index not in self.step_provenance
        ]
        if missing_scopes:
            raise ValueError(
                f"Resolved pipeline missing scope/provenance facts for steps {missing_scopes}."
            )
        object.__setattr__(
            self,
            "step_provenance",
            {
                index: dict(self.step_provenance[index])
                for index in range(len(self.steps))
            },
        )
        object.__setattr__(
            self,
            "step_scope_ids",
            dict(self.step_scope_ids),
        )
        object.__setattr__(
            self,
            "steps",
            tuple(
                (
                    step.with_function_spec(
                        normalize_function_pattern(
                            strip_disabled_functions(step.func) or []
                        )
                    )
                    if isinstance(step, FunctionStep)
                    else step
                )
                for step in self.steps
            ),
        )


@dataclass(slots=True)
class CompilationSession:
    """Compiler boundary for one ProcessingContext.

    The session is not a dict wrapper. It owns the invariants tying together the
    resolved pipeline declaration, context, and mutable
    compiled-plan map for one axis or sequential-combination context.
    """

    context: ProcessingContext
    pipeline: ResolvedPipelineDefinition
    orchestrator: "PipelineOrchestrator"
    global_config: "GlobalPipelineConfig"
    plans: MutableMapping[int, CompiledStepPlan]
    source_workspace_projection: VirtualWorkspaceSourceProjection
    path_resolver: CompilationPathResolver | None = None
    metadata_writer: bool = False
    plate_scope: CompilationPlateScope | None = None
    is_zmq_execution: bool = False

    @classmethod
    def from_context(
        cls,
        *,
        context: ProcessingContext,
        pipeline: ResolvedPipelineDefinition,
        orchestrator: "PipelineOrchestrator",
        global_config: "GlobalPipelineConfig",
        source_workspace_projection: VirtualWorkspaceSourceProjection | None = None,
        path_resolver: CompilationPathResolver | None = None,
        metadata_writer: bool = False,
        plate_path: Path | None = None,
        is_zmq_execution: bool = False,
    ) -> "CompilationSession":
        if context.step_plans is None:
            raise ValueError("CompilationSession requires context.step_plans.")
        return cls(
            context=context,
            pipeline=pipeline,
            orchestrator=orchestrator,
            global_config=global_config,
            plans=context.step_plans,
            source_workspace_projection=(
                VirtualWorkspaceSourceProjection.empty(context.plate_path)
                if source_workspace_projection is None
                else source_workspace_projection
            ),
            path_resolver=path_resolver,
            metadata_writer=metadata_writer,
            plate_scope=(
                CompilationPlateScope.from_path(plate_path)
                if plate_path is not None
                else None
            ),
            is_zmq_execution=is_zmq_execution,
        )

    def __post_init__(self) -> None:
        if self.plate_scope is None and self.context.plate_path is not None:
            self.plate_scope = CompilationPlateScope.from_context(self.context)

    @property
    def axis_id(self) -> str:
        return self.context.axis_id

    @property
    def plate_path(self) -> Path | None:
        if self.plate_scope is None:
            return None
        return self.plate_scope.path

    @property
    def realized_source_metadata(
        self,
    ) -> tuple[SourceMetadataMapping, ...] | None:
        """Return the axis-scoped source metadata realized for this compilation."""

        metadata = tuple(
            self.source_workspace_projection.source_metadata_by_path.values()
        )
        return metadata or None

    @property
    def step_count(self) -> int:
        return len(self.pipeline.steps)

    def plan(self, index: int) -> CompiledStepPlan:
        try:
            return self.plans[index]
        except KeyError as exc:
            raise ValueError(
                f"Missing compiled plan for step {index} ({self.pipeline.steps[index].name})."
            ) from exc

    def main_flow_plan_ancestry(
        self,
        index: int,
    ) -> tuple[CompiledStepPlan, ...]:
        """Return one compiled plan and its main-flow producer ancestry."""

        ancestry: list[CompiledStepPlan] = []
        visited: set[int] = set()
        current_index = index
        while True:
            if current_index in visited:
                raise ValueError(
                    f"Compiled main-flow dependency cycle includes step {current_index}."
                )
            visited.add(current_index)
            current = self.plan(current_index)
            ancestry.append(current)
            source_step_index = current.main_input_dependency.predecessor_step_index()
            if source_step_index is None:
                return tuple(ancestry)
            current_index = source_step_index
