"""Axis-scoped compiler session for pipeline compilation stages."""

from __future__ import annotations

from dataclasses import dataclass, field, fields, is_dataclass, replace
from pathlib import Path
from typing import TYPE_CHECKING, Any, Mapping, MutableMapping, Sequence, get_type_hints

from objectstate import DataclassFieldAccess

from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.context.processing_context import CompiledContext, CompilingContext
from openhcs.core.source_metadata import SourceMetadataFields, SourceMetadataMapping
from openhcs.core.source_workspace_projection import VirtualWorkspaceSourceProjection
from openhcs.core.steps.abstract import AbstractStep
from openhcs.core.steps.function_step import FunctionStep
from openhcs.core.function_patterns import (
    normalize_prepared_function_pattern,
    NormalizedFunctionItem,
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
    DatasetPathDeclaration,
    DeclaredFile,
    DeclaredFileLinkError,
    SeveralWritersOfDeclaredFileError,
    FileManagerLike,
    LinkedInputFile,
    OutputFileOf,
    PathRoots,
    ProducedFileLookup,
)
from openhcs.core.axes import AxisFamily, Ungrouped

if TYPE_CHECKING:
    from openhcs.core.config import GlobalPipelineConfig
    from openhcs.core.pipeline.artifact_planning import ArtifactGraph
    from openhcs.core.artifacts.plans import ArtifactSpecRef
    from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator


@dataclass(frozen=True, slots=True)
class CompilationDatasetScope:
    """Plate-root identity used for compiler ObjectState scopes and paths."""

    path: Path

    def __post_init__(self) -> None:
        if not self.path.is_absolute():
            raise ValueError(
                f"Compilation plate scope must be absolute, got {self.path}."
            )

    @classmethod
    def from_context(cls, context: CompilingContext) -> "CompilationDatasetScope":
        if context.dataset_root is None:
            raise ValueError("Compilation plate scope requires context.dataset_root.")
        return cls(Path(context.dataset_root))

    @classmethod
    def from_path(cls, dataset_root: Path | str | None) -> "CompilationDatasetScope":
        if dataset_root is None:
            raise ValueError("Compilation plate scope requires a plate path.")
        return cls(Path(dataset_root))

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
class OutputFileParameter:
    """An output-file parameter of one callable of one step that has no value."""

    step_index: int
    step_name: str
    function_name: str
    parameter: str

    def linked_input_file(
        self,
        parameter: str,
        link: OutputFileOf,
        declaration: DatasetPathDeclaration,
        *,
        owner: str,
    ) -> LinkedInputFile:
        """Return the record of a consumer parameter that reads this file."""

        del parameter, declaration
        raise DeclaredFileLinkError(
            f"{owner} reads {link!r}, but step {self.step_name!r} callable "
            f"{self.function_name!r} has no value for output file "
            f"{self.parameter!r} (it is None), so it writes no file."
        )


@dataclass(frozen=True, slots=True)
class ProducedFile(OutputFileParameter):
    """A file one callable of one step writes, at its resolved path."""

    file: DeclaredFile

    def linked_input_file(
        self,
        parameter: str,
        link: OutputFileOf,
        declaration: DatasetPathDeclaration,
        *,
        owner: str,
    ) -> LinkedInputFile:
        del link, owner
        return LinkedInputFile(
            parameter=parameter,
            path=self.file.path,
            backend=self.file.backend,
            declaration=declaration,
            producer_step_index=self.step_index,
            producer_step_name=self.step_name,
            producer_parameter=self.parameter,
        )


@dataclass(frozen=True, slots=True)
class ProducedFiles(ProducedFileLookup):
    """Every output-file parameter the steps of one pipeline declare.

    Built once per pipeline from each step's function pattern; a consumer's
    ``OutputFileOf`` argument resolves through it to the producer's path.
    """

    step_names: tuple[str, ...] = ()
    parameters: tuple[OutputFileParameter, ...] = ()

    @classmethod
    def from_pipeline(
        cls,
        pipeline: "ResolvedPipelineDefinition",
        resolver: "CompilationPathResolver",
    ) -> "ProducedFiles":
        """Collect the output files of every step, then check every link."""

        parameters: list[OutputFileParameter] = []
        step_items = tuple(
            (index, f"step {step.name!r} (index {index})", graph.invocation_items())
            for index, (step, graph) in enumerate(
                zip(pipeline.steps, pipeline.artifact_graphs)
            )
        )
        for (index, step_label, items), step in zip(step_items, pipeline.steps):
            for item in items:
                contract = item.contract
                values = contract.declared_path_values(item.kwargs_dict)
                written_file_parameters = tuple(
                    name
                    for name, declaration in contract.declared_path_parameters.items()
                    if declaration.writes_file
                )
                for name in written_file_parameters:
                    identity = (index, step.name, contract.function_name, name)
                    parameters.append(
                        ProducedFile(
                            *identity,
                            file=resolver.declared_file(
                                name,
                                values[name][1],
                                values[name][0],
                                owner=f"{step_label} callable "
                                f"{contract.function_name}.{name}",
                            ),
                        )
                        if name in values
                        else OutputFileParameter(*identity)
                    )
        produced = cls(
            step_names=tuple(step.name for step in pipeline.steps),
            parameters=tuple(parameters),
        )
        linking = replace(resolver, produced_files=produced)
        for index, step_label, items in step_items:
            for item in items:
                owner = f"{step_label} callable {item.contract.function_name}"
                for declared in item.contract.declared_files(
                    item.kwargs_dict, linking, owner=owner
                ):
                    declared.require_produced_before(
                        index, owner=f"{owner}.{declared.parameter}"
                    )
        return produced

    def linked_input_file(
        self,
        parameter: str,
        link: OutputFileOf,
        declaration: DatasetPathDeclaration,
        *,
        owner: str,
    ) -> LinkedInputFile:
        step_indexes = tuple(
            index for index, name in enumerate(self.step_names) if name == link.step
        )
        if not step_indexes:
            raise DeclaredFileLinkError(
                f"{owner} reads {link!r}, but the pipeline has no step named "
                f"{link.step!r}; steps: {sorted(set(self.step_names))}."
            )
        if len(step_indexes) > 1:
            raise DeclaredFileLinkError(
                f"{owner} reads {link!r}, but step name {link.step!r} is shared by "
                f"the steps at indexes {list(step_indexes)}; rename one so the "
                "link names a single step."
            )
        (step_index,) = step_indexes
        of_step = tuple(
            written for written in self.parameters if written.step_index == step_index
        )
        matches = tuple(
            written for written in of_step if written.parameter == link.parameter
        )
        if not matches:
            raise DeclaredFileLinkError(
                f"{owner} reads {link!r}, but parameter {link.parameter!r} is not a "
                f"declared output file of step {link.step!r}; its output file "
                f"parameters: {sorted({written.parameter for written in of_step})}."
            )
        if len(matches) > 1:
            raise DeclaredFileLinkError(
                f"{owner} reads {link!r}, but {len(matches)} callables of step "
                f"{link.step!r} declare output file {link.parameter!r}: "
                f"{[written.function_name for written in matches]}."
            )
        (written,) = matches
        return written.linked_input_file(parameter, link, declaration, owner=owner)


@dataclass(frozen=True, slots=True)
class InputDatasetPathResolver(PathRoots):
    """Resolve declared paths while only the input plate is known.

    The path planning config names the folder output datasets are created in,
    so its declared paths resolve before an output dataset root exists.
    """

    input_dataset: CompilationDatasetScope
    filemanager: FileManagerLike
    backend: str

    def input_dataset_root(self) -> Path:
        return self.input_dataset.path

    def output_dataset_root(self) -> Path:
        raise TypeError(
            "The output dataset root is not known while resolving the config "
            "that defines it."
        )

    def resolve(
        self,
        value: str | Path,
        declaration: DatasetPathDeclaration,
        *,
        owner: str,
    ) -> Path:
        try:
            root = declaration.root(self)
        except Exception as error:
            error.add_note(f"While resolving {owner}: authored={value!r}.")
            raise
        try:
            target = CompilationDatasetScope(root).resolve_address(
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
                f"{type(declaration).__name__} root={root}, "
                f"backend={self.backend!r}."
            )
            raise


@dataclass(frozen=True, slots=True)
class CompilationPathResolver(InputDatasetPathResolver):
    """Resolve declared paths and links between steps for one compilation plate."""

    output_dataset: CompilationDatasetScope
    produced_files: ProducedFileLookup = field(default_factory=ProducedFiles)

    def output_dataset_root(self) -> Path:
        return self.output_dataset.path

    @classmethod
    def for_dataset(
        cls,
        dataset_root: Path | str | None,
        global_config: "GlobalPipelineConfig",
        *,
        filemanager: FileManagerLike,
        backend: str,
    ) -> tuple["CompilationPathResolver", "GlobalPipelineConfig"]:
        """Return the resolver of one dataset and the config with paths resolved.

        The path planning config defines the output dataset root, so its
        declared paths resolve first, against the input dataset.
        """
        from openhcs.core.pipeline.path_planner import PathPlannerPathAuthority

        input_dataset = CompilationDatasetScope.from_path(dataset_root)
        path_planning_config = resolve_declared_dataclass_paths(
            global_config.path_planning_config,
            InputDatasetPathResolver(
                input_dataset=input_dataset, filemanager=filemanager, backend=backend
            ),
            owner="PipelineConfig.path_planning_config",
        )
        resolver = cls(
            input_dataset=input_dataset,
            filemanager=filemanager,
            backend=backend,
            output_dataset=CompilationDatasetScope.from_path(
                PathPlannerPathAuthority.build_output_dataset_root(
                    input_dataset.path, path_planning_config
                )
            ),
        )
        return resolver, resolve_declared_dataclass_paths(
            replace(global_config, path_planning_config=path_planning_config),
            resolver,
            owner="PipelineConfig",
        )

    def reading_files_of(
        self, pipeline: "ResolvedPipelineDefinition"
    ) -> "CompilationPathResolver":
        """Return this resolver with the pipeline's table of produced files."""

        return replace(
            self, produced_files=ProducedFiles.from_pipeline(pipeline, self)
        )

    def declared_file(
        self,
        parameter: str,
        value: object,
        declaration: DatasetPathDeclaration,
        *,
        owner: str,
    ) -> DeclaredFile:
        """Resolve one authored argument of a declared path parameter."""

        if isinstance(value, OutputFileOf):
            return declaration.linked_file(
                parameter, value, self.produced_files, owner=owner
            )
        if not isinstance(value, (str, Path)):
            raise TypeError(
                f"{owner} requires str, Path or OutputFileOf, got "
                f"{type(value).__name__}."
            )
        return DeclaredFile(
            parameter=parameter,
            path=self.resolve(value, declaration, owner=owner),
            backend=self.backend,
            declaration=declaration,
        )


@dataclass(frozen=True, slots=True)
class DeclaredFileWriter:
    """One compiled invocation that writes a declared output file."""

    step_index: int
    step_name: str
    function_name: str
    parameter: str
    axis_id: str
    group_key: str

    def __str__(self) -> str:
        return (
            f"step {self.step_name!r} (index {self.step_index}) callable "
            f"{self.function_name!r} parameter {self.parameter!r}, axis "
            f"{self.axis_id!r}, group {self.group_key!r}"
        )


def require_one_writer_per_declared_file(
    compiled_contexts: Mapping[str, "CompiledContext"],
) -> None:
    """Reject a plate whose compiled invocations share a declared output file.

    A step that runs once for the plate has a plan in every context; only the
    context that owns its outputs runs it, so only that plan counts.
    """

    writers_by_path: dict[Path, list[DeclaredFileWriter]] = {}
    running_plans = (
        plan
        for context in compiled_contexts.values()
        for plan in context.step_plans.values()
        if plan.owns_runtime_outputs
    )
    for plan in running_plans:
        for invocation in plan.compiled_function_pattern.iter_invocations():
            for declared in invocation.declared_files:
                if declared.declaration.writes_file:
                    writers_by_path.setdefault(declared.path, []).append(
                        DeclaredFileWriter(
                            step_index=plan.step_index,
                            step_name=plan.step_name,
                            function_name=invocation.key.function_name,
                            parameter=declared.parameter,
                            axis_id=plan.axis_id,
                            group_key=invocation.key.group_key,
                        )
                    )
    for path, writers in writers_by_path.items():
        if len(writers) > 1:
            first, second, *others = writers
            raise SeveralWritersOfDeclaredFileError(
                f"Declared output file {path} has {len(writers)} writers: {first}; "
                f"and {second}"
                + (f"; and {len(others)} more" if others else "")
                + ". A declared output file has one writer; run the step once "
                "for the plate, or give each invocation its own file."
            )


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
        declaration = DatasetPathDeclaration.from_annotation(
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
        from openhcs.core.callable_contract import FunctionStepExecutionScope
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
                else Ungrouped
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
            graph.validate_invocation_declarations()
            previous = graphs[-1] if graphs else None
            previous_pattern = None if previous is None else previous.pattern
            dependency = graph.resolve_main_input_dependency(
                step,
                index,
                execution_scope=FunctionStepExecutionScope.require_uniform(
                    item.contract for item in graph.invocation_items()
                ),
                source_bindings=step.source_bindings,
                context=context,
                declared={},
                step_scope_ids=self.step_scope_ids,
                previous_dependency=(
                    None if previous is None else previous.main_input_dependency
                ),
                previous_preserves_input_main_flow=(
                    bool(previous_pattern)
                    and all(
                        bool(group.items)
                        and all(
                            item.contract.preserves_input_main_flow()
                            for item in group.items
                        )
                        for group in previous_pattern.groups
                    )
                ),
            )
            graph = graph.with_source_binding_plan(
                step.source_bindings, dependency, context
            )
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

    def validate_source_group_domains(
        self,
        orchestrator: PipelineOrchestrator,
        global_config: GlobalPipelineConfig,
    ) -> None:
        """Validate declaration-owned group keys once against the whole plate."""
        from openhcs.core.callable_contract import FunctionStepExecutionScope
        from openhcs.core.components.validation import GenericValidator

        validator = GenericValidator(AxisFamily.active())

        for index, (graph, context) in enumerate(
            zip(self.artifact_graphs, self.artifact_contexts)
        ):
            pattern = graph.pattern
            if (
                pattern is None
                or not pattern.is_grouped
                or context.group_by is Ungrouped
            ):
                continue
            if FunctionStepExecutionScope.require_uniform(
                item.contract for item in pattern.iter_items()
            ) is FunctionStepExecutionScope.PLATE:
                continue
            result = validator.validate_dict_pattern_keys(
                pattern,
                context.group_by,
                context.step_name,
                orchestrator,
                resolved_config=global_config,
            )
            if not result.is_valid:
                raise ValueError(
                    f"FunctionStep {context.step_name!r} (index: {index}) failed "
                    f"compile-time contract validation: {result.error_message}"
                )

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
                    step.with_function_spec(normalize_prepared_function_pattern(step.func or []))
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

    context: CompilingContext
    pipeline: ResolvedPipelineDefinition
    orchestrator: "PipelineOrchestrator"
    global_config: "GlobalPipelineConfig"
    plans: MutableMapping[int, CompiledStepPlan]
    source_workspace_projection: VirtualWorkspaceSourceProjection
    path_resolver: CompilationPathResolver | None = None
    metadata_writer: bool = False
    dataset_scope: CompilationDatasetScope | None = None
    is_zmq_execution: bool = False

    _source_literal_field_types: Mapping[str, type[object] | None] | None = field(
        default=None, init=False, repr=False
    )

    @classmethod
    def from_context(
        cls,
        *,
        context: CompilingContext,
        pipeline: ResolvedPipelineDefinition,
        orchestrator: "PipelineOrchestrator",
        global_config: "GlobalPipelineConfig",
        source_workspace_projection: VirtualWorkspaceSourceProjection | None = None,
        path_resolver: CompilationPathResolver | None = None,
        metadata_writer: bool = False,
        dataset_root: Path | None = None,
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
                VirtualWorkspaceSourceProjection.empty(context.dataset_root)
                if source_workspace_projection is None
                else source_workspace_projection
            ),
            path_resolver=path_resolver,
            metadata_writer=metadata_writer,
            dataset_scope=(
                CompilationDatasetScope.from_path(dataset_root)
                if dataset_root is not None
                else None
            ),
            is_zmq_execution=is_zmq_execution,
        )

    def __post_init__(self) -> None:
        if self.dataset_scope is None and self.context.dataset_root is not None:
            self.dataset_scope = CompilationDatasetScope.from_context(self.context)

    @property
    def axis_id(self) -> str:
        return self.context.axis_id

    @property
    def dataset_root(self) -> Path | None:
        if self.dataset_scope is None:
            return None
        return self.dataset_scope.path

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
    def source_literal_field_types(self) -> Mapping[str, type[object] | None]:
        """Admit literal types once from this session's captured source projection."""
        if self._source_literal_field_types is None:
            self._source_literal_field_types = SourceMetadataFields.literal_field_types(
                self.realized_source_metadata or ()
            )
        return self._source_literal_field_types

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
