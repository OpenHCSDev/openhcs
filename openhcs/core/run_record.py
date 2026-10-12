"""The record of what produced an output dataset.

Three stages, each with one owner:

* ``RunDeclaration``: what only the compiler holds (the stored documents and
  the resolved configuration with the source of every value). It travels on
  the ``CompiledExecutionBundle``.
* ``RunRecord.at_run_start``: the parent process combines the declaration with
  the compiled step plans and asks the storage layer what each declared input
  file holds.
* ``ProducedFiles`` and ``RunRecord`` are written into the output dataset's
  ``openhcs_metadata.json`` by its one writer and read back from there.

Two read kinds are kept apart on purpose. ``pipeline_code`` and
``global_config_code`` are stored documents: executing them rebuilds the
run. ``configuration``, ``steps[].configuration`` and ``parameters`` are the
resolved values, each with the declaration that supplied it.

The stored form is the JSON ``python_introspect.to_jsonable`` writes for these
dataclasses and ``python_introspect.dataclass_from_mapping`` reads back; there
is no other encoder or decoder. A class of a registered family (a parameter's
or a configuration value's source) is stored as its registry key. A member of
a registered family that carries data (a function identity, a file's content)
is stored as ``{registry key: fields}``, so the stored form names its class.
"""

from __future__ import annotations

import hashlib
import inspect
import json
from abc import ABC, abstractmethod
from collections.abc import Iterable, Iterator, Mapping, Sequence
from dataclasses import dataclass, field, fields, is_dataclass, replace
from pathlib import Path
from types import MappingProxyType
from typing import TYPE_CHECKING, ClassVar

import pycodify
from metaclass_registry import AutoRegisterMeta
from polystore.file_content import FileContent
from polystore.streaming.identity import StreamProducerIdentity
from python_introspect import JsonObject, JsonValue, dataclass_from_mapping, to_jsonable

from openhcs.core.function_identity import FunctionIdentity

from openhcs.core.vfs_protocol import FileManagerLike

if TYPE_CHECKING:
    from openhcs.core.compiled_execution import CompiledExecutionBundle
    from openhcs.core.compiled_step_plan import CompiledStepPlan
    from openhcs.core.config import GlobalPipelineConfig
    from openhcs.core.function_patterns import CompiledFunctionInvocation
    from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
    from openhcs.core.steps.abstract import AbstractStep
    from openhcs.core.pipeline.compilation_session import ResolvedPipelineDefinition
    from pycodify.documents import PipelineDocument



def python_expression(value: object) -> str:
    """Write a value the way generated pipeline code writes it."""
    import openhcs.serialization.pycodify_formatters  # noqa: F401 (registers formatters)

    return pycodify.to_source(value, pycodify.FormatContext(clean_mode=False)).code


class ParameterSource(ABC, metaclass=AutoRegisterMeta):
    """Which declaration supplied the value a function parameter ran with.

    Each source is a subclass; ``name`` is its spelling in the stored record.
    """

    __registry_key__ = "name"
    __skip_if_no_key__ = True

    name: ClassVar[str | None] = None

    @classmethod
    @abstractmethod
    def value_expression(
        cls, parameter: inspect.Parameter, written: Mapping[str, object]
    ) -> str | None:
        """The value as a Python expression, or None when no declaration states it."""


class WrittenInPipeline(ParameterSource):
    """The pipeline document states the value."""

    name = "pipeline"

    @classmethod
    def value_expression(
        cls, parameter: inspect.Parameter, written: Mapping[str, object]
    ) -> str | None:
        return python_expression(written[parameter.name])


class FunctionDefault(ParameterSource):
    """The pipeline leaves the parameter out; the signature of the recorded function supplies it.

    The function and its version are the identity of the function record the
    parameter belongs to.
    """

    name = "function_default"

    @classmethod
    def value_expression(
        cls, parameter: inspect.Parameter, written: Mapping[str, object]
    ) -> str | None:
        return python_expression(parameter.default)


class SuppliedAtRunTime(ParameterSource):
    """The platform passes the value when it calls the function; no declaration states it."""

    name = "run_time"

    @classmethod
    def value_expression(
        cls, parameter: inspect.Parameter, written: Mapping[str, object]
    ) -> str | None:
        return None


@dataclass(frozen=True, slots=True)
class RecordedParameter:
    """One parameter of a function, the value it ran with and where the value came from."""

    name: str
    value: str | None
    source: type[ParameterSource]


class ConfigValueSource(ABC, metaclass=AutoRegisterMeta):
    """How a configured object came by a value: it holds it, or ObjectState resolved it."""

    __registry_key__ = "name"
    __skip_if_no_key__ = True

    name: ClassVar[str | None] = None


class SetOnObject(ConfigValueSource):
    """The configured object itself holds the value."""

    name = "set_here"


class InheritedFrom(ConfigValueSource):
    """ObjectState resolved the value from another scope or class."""

    name = "inherited"


def _type_name(owner: type | None) -> str | None:
    return None if owner is None else f"{owner.__module__}.{owner.__qualname__}"


@dataclass(frozen=True, slots=True)
class ConfigValueOwner:
    """The scope and class that supplied configuration values, and how."""

    source: type[ConfigValueSource]
    scope_id: str | None
    type_name: str | None


@dataclass(frozen=True, slots=True)
class ConfigValuesFromOwner:
    """The resolved values one owner supplied, by field path, as Python expressions."""

    owner: ConfigValueOwner
    values: Mapping[str, str]


ObjectStateProvenance = Mapping[str, tuple[str | None, type | None]]


def _field_values(configured: object) -> dict[str, object]:
    return {item.name: getattr(configured, item.name) for item in fields(configured)}


def _values_with_owner(
    values: Mapping[str, object],
    provenance: ObjectStateProvenance,
    *,
    holder: ConfigValueOwner,
    prefix: str = "",
) -> Iterator[tuple[ConfigValueOwner, str, str]]:
    for name, value in values.items():
        path = f"{prefix}{name}"
        if path in provenance:
            scope_id, source_type = provenance[path]
            yield (
                ConfigValueOwner(InheritedFrom, scope_id, _type_name(source_type)),
                path,
                python_expression(value),
            )
        elif is_dataclass(value) and not isinstance(value, type):
            yield from _values_with_owner(
                _field_values(value),
                provenance,
                holder=holder,
                prefix=f"{path}.",
            )
        else:
            yield holder, path, python_expression(value)


def resolved_values(
    values: Mapping[str, object],
    provenance: ObjectStateProvenance,
    *,
    scope_id: str | None,
    holder_type: type,
) -> tuple[ConfigValuesFromOwner, ...]:
    """Every leaf value of a resolved object, grouped by the owner that supplied it.

    ObjectState lists the paths it inherited; a path it does not list is held
    by the object itself. A nested config the object leaves unset is inherited
    whole and listed as one path, so the inherited check comes before descent.
    Each owner is written once, with all the values it supplied.
    """
    by_owner: dict[ConfigValueOwner, dict[str, str]] = {}
    for owner, path, expression in _values_with_owner(
        values,
        provenance,
        holder=ConfigValueOwner(SetOnObject, scope_id, _type_name(holder_type)),
    ):
        by_owner.setdefault(owner, {})[path] = expression
    return tuple(
        ConfigValuesFromOwner(owner, MappingProxyType(owned))
        for owner, owned in by_owner.items()
    )


@dataclass(frozen=True, slots=True)
class RunDeclaration:
    """What the compiler alone knows about a run: documents and resolved configuration."""

    pipeline_code: str
    global_config_code: str
    configuration: tuple[ConfigValuesFromOwner, ...]
    step_configurations: tuple[tuple[ConfigValuesFromOwner, ...], ...] = ()
    """Resolved values of each enabled step, by compiled step index."""

    @classmethod
    def before_step_resolution(
        cls,
        orchestrator: "PipelineOrchestrator",
        pipeline_definition: Sequence["AbstractStep"],
    ) -> "RunDeclaration":
        """Render the documents as submitted, before the compiler resolves the steps in place."""
        from objectstate import ObjectState, ObjectStateRegistry
        from objectstate.global_config import get_saved_global_config

        from openhcs.core.config import GlobalPipelineConfig
        from openhcs.core.config_document import ConfigDocumentCodec
        from openhcs.core.pipeline_document import PipelineDocumentCodec

        # With no saved global config set, ObjectState resolves against the
        # declared defaults: the document a default-constructed config states.
        saved_global_config = (
            get_saved_global_config(GlobalPipelineConfig) or GlobalPipelineConfig()
        )
        effective_config, provenance = ObjectState.resolve_saved_object(
            orchestrator.pipeline_config,
            ancestor_objects_with_scopes=(
                ObjectStateRegistry.get_ancestor_objects_with_scopes(None, use_saved=True)
            ),
        )
        return cls(
            pipeline_code=PipelineDocumentCodec.render_with_every_parameter(
                PipelineDocumentCodec.from_values(
                    pipeline_config=orchestrator.pipeline_config,
                    pipeline_steps=pipeline_definition,
                )
            ),
            global_config_code=ConfigDocumentCodec.render(
                saved_global_config,
                expected_config_type=GlobalPipelineConfig,
                clean_mode=False,
            ),
            configuration=resolved_values(
                _field_values(effective_config),
                provenance,
                scope_id=str(orchestrator.dataset_root),
                holder_type=type(orchestrator.pipeline_config),
            ),
        )

    def with_resolved_steps(
        self, pipeline: "ResolvedPipelineDefinition"
    ) -> "RunDeclaration":
        """Add each enabled step's resolved values from the compiler's one resolution."""
        return replace(
            self,
            step_configurations=tuple(
                resolved_values(
                    step.configuration_parameters(),
                    pipeline.step_provenance[index],
                    scope_id=pipeline.step_scope_ids[index],
                    holder_type=type(step),
                )
                for index, step in enumerate(pipeline.steps)
            ),
        )


@dataclass(frozen=True, slots=True)
class DeclaredFile:
    """One declared path parameter and what the storage layer says the file holds."""

    parameter: str
    declared_as: str
    path: str
    content: FileContent


@dataclass(frozen=True, slots=True)
class FunctionRecord:
    """One function call of a step: which function, with which values and files."""

    identity: FunctionIdentity
    group: str
    position: int
    input_memory_type: str | None
    output_memory_type: str | None
    parameters: tuple[RecordedParameter, ...]
    declared_files: tuple[DeclaredFile, ...]

    @classmethod
    def of_invocation(
        cls,
        invocation: "CompiledFunctionInvocation",
        *,
        filemanager: FileManagerLike,
        backend: str,
    ) -> "FunctionRecord":
        contract = invocation.contract
        return cls(
            identity=contract.func.identity(),
            group=python_expression(invocation.key.group_key),
            position=invocation.key.position,
            input_memory_type=invocation.input_memory_type,
            output_memory_type=invocation.output_memory_type,
            parameters=_parameters(invocation),
            declared_files=tuple(
                DeclaredFile(
                    parameter=parameter_name,
                    declared_as=declaration.plain_name,
                    path=str(path),
                    content=declaration.content_at_run_start(
                        Path(path), filemanager=filemanager, backend=backend
                    ),
                )
                for parameter_name, (declaration, path) in (
                    contract.declared_path_values(invocation.kwargs_dict).items()
                )
            ),
        )


def _parameters(invocation: "CompiledFunctionInvocation") -> tuple[RecordedParameter, ...]:
    """Every parameter of the function's signature with its effective value and source."""
    contract = invocation.contract
    written = invocation.kwargs_dict
    signature = contract.canonical_signature.parameters
    supplied_at_run_time = {
        *contract.runtime_owned_parameter_names,
        invocation.primary_input_parameter_name,
    }
    sources: dict[str, type[ParameterSource]] = {}
    for name, parameter in signature.items():
        if name in written:
            sources[name] = WrittenInPipeline
        elif name in supplied_at_run_time or parameter.default is inspect.Parameter.empty:
            sources[name] = SuppliedAtRunTime
        else:
            sources[name] = FunctionDefault
    keyword_only = inspect.Parameter.KEYWORD_ONLY
    return tuple(
        RecordedParameter(
            name,
            source.value_expression(
                signature.get(name, inspect.Parameter(name, keyword_only)), written
            ),
            source,
        )
        for name, source in {
            **sources,
            **{name: WrittenInPipeline for name in written if name not in signature},
        }.items()
    )


@dataclass(frozen=True, slots=True)
class GpuDevice:
    """The GPU device assigned to one framework's arrays."""

    memory_type: str
    device_id: int


@dataclass(frozen=True, slots=True)
class StepCalls:
    """What one step ran: its identity in the pipeline, its devices and its function calls."""

    name: str
    pipeline_position: int | None
    step_scope_id: str | None
    input_memory_type: str | None
    output_memory_type: str | None
    assigned_gpu_devices: tuple[GpuDevice, ...]
    functions: tuple[FunctionRecord, ...]

    @classmethod
    def of_plan(
        cls,
        plan: "CompiledStepPlan",
        *,
        filemanager: FileManagerLike,
        backend: str,
    ) -> "StepCalls":
        return cls(
            name=plan.step_name,
            pipeline_position=plan.pipeline_position,
            step_scope_id=plan.step_scope_id,
            input_memory_type=plan.input_memory_type,
            output_memory_type=plan.output_memory_type,
            assigned_gpu_devices=tuple(
                GpuDevice(binding.memory_type.value, binding.device_id)
                for binding in plan.device_assignment.bindings
            ),
            functions=tuple(
                FunctionRecord.of_invocation(
                    invocation, filemanager=filemanager, backend=backend
                )
                for invocation in plan.compiled_function_pattern.iter_invocations()
            ),
        )

    def is_named_by(self, producer: StreamProducerIdentity) -> bool:
        """A producer identity names a step by the two fields it carries."""
        return (
            self.step_scope_id == producer.step_scope_id
            and self.pipeline_position == producer.pipeline_position
        )


@dataclass(frozen=True, slots=True)
class StepRecord:
    """One step of the run: what it ran, and its resolved configuration by owner."""

    calls: StepCalls
    configuration: tuple[ConfigValuesFromOwner, ...]


@dataclass(frozen=True, slots=True)
class SoftwareEnvironment:
    """The interpreter and the installed distributions the run executed in."""

    openhcs: str
    python: str
    python_implementation: str
    platform: str
    machine: str
    installed_distributions: Mapping[str, str]
    """Version by distribution name."""

    @classmethod
    def current(cls) -> "SoftwareEnvironment":
        import openhcs
        from openhcs.runtime.environment_provenance import RuntimeEnvironmentSnapshot

        environment = RuntimeEnvironmentSnapshot.current()
        return cls(
            openhcs=openhcs.__version__,
            python=environment.python_version,
            python_implementation=environment.python_implementation,
            platform=environment.sys_platform,
            machine=environment.machine,
            installed_distributions=MappingProxyType(
                {item.name: item.version for item in environment.installed_distributions}
            ),
        )


class UnrecordedOutputFile(LookupError):
    """The dataset's metadata does not say which step produced this file."""


@dataclass(frozen=True, slots=True)
class RunRecord:
    """What produced an output dataset. Its id is the sha256 of its stored JSON."""

    software: SoftwareEnvironment
    pipeline_code: str
    global_config_code: str
    configuration: tuple[ConfigValuesFromOwner, ...]
    steps: tuple[StepRecord, ...]
    custom_sources: Mapping[str, str]
    """Source text of each custom function, by the sha256 its identity states."""

    def to_json(self) -> JsonObject:
        """The stored form: the one encoder, ``python_introspect.to_jsonable``."""
        return to_jsonable(self)

    @classmethod
    def from_json(cls, stored: JsonObject) -> "RunRecord":
        """Read the stored form: the one decoder, ``python_introspect.dataclass_from_mapping``."""
        return dataclass_from_mapping(cls, stored)

    @property
    def record_id(self) -> str:
        return hashlib.sha256(
            json.dumps(self.to_json(), sort_keys=True, separators=(",", ":")).encode("utf-8")
        ).hexdigest()

    @classmethod
    def at_run_start(
        cls,
        bundle: "CompiledExecutionBundle",
        *,
        filemanager: FileManagerLike,
        backend: str,
    ) -> "RunRecord":
        """Combine the compiler's declaration with the step plans and the declared files' content.

        Called once per run in the parent process before any worker starts, so
        a declared input file is hashed once and the hash is of the bytes the
        run reads.
        """
        declaration = bundle.run_declaration
        steps: dict[int, StepRecord] = {}
        for axis_id in bundle.axis_ids:
            context = next(
                context
                for context in bundle.runtime_contexts.values()
                if context.require_axis_id() == axis_id
            )
            for index, plan in context.step_plans.items():
                if index not in steps:
                    steps[index] = StepRecord(
                        StepCalls.of_plan(plan, filemanager=filemanager, backend=backend),
                        declaration.step_configurations[index],
                    )
        custom_sources: dict[str, str] = {}
        for step in steps.values():
            for function in step.calls.functions:
                custom_sources.update(function.identity.source_texts())
        return cls(
            software=SoftwareEnvironment.current(),
            pipeline_code=declaration.pipeline_code,
            global_config_code=declaration.global_config_code,
            configuration=declaration.configuration,
            steps=tuple(steps[index] for index in sorted(steps)),
            custom_sources=MappingProxyType(custom_sources),
        )

    def step_for(self, producer: StreamProducerIdentity) -> StepCalls:
        """The step a producer identity names."""
        matches = [
            step.calls for step in self.steps if step.calls.is_named_by(producer)
        ]
        if len(matches) != 1:
            raise LookupError(
                f"Run record {self.record_id} has {len(matches)} steps for producer "
                f"{producer.step_name!r} at position {producer.pipeline_position}."
            )
        return matches[0]

    @classmethod
    def for_dataset(cls, dataset_root: str | Path) -> Mapping[str, "RunRecord"]:
        """Every record the dataset's metadata document holds, by record id."""
        return DatasetRunRecords.of_dataset(Path(dataset_root)).run_records

    @classmethod
    def for_output_file(cls, output_file: str | Path) -> "ProducedFile":
        """The record and producing step of one output file.

        The answer comes only from what the writer stored for this path; a file
        the dataset does not list raises instead of being guessed from its name.
        """
        path = Path(output_file).resolve()
        dataset_root = _dataset_root_of(path)
        stored = DatasetRunRecords.of_dataset(dataset_root)
        entry = stored.produced_files.get(path.relative_to(dataset_root).as_posix())
        if entry is None:
            raise UnrecordedOutputFile(
                f"{path} is not recorded as a step output in "
                f"{_metadata_path(dataset_root)}."
            )
        return ProducedFile(
            record=stored.run_records[entry.run_record], producer=entry.producer
        )

    def rebuild(self) -> tuple["PipelineDocument", "GlobalPipelineConfig"]:
        """Rebuild the pipeline document and global config this record was run with.

        Custom functions are registered from the recorded source text (not
        persisted), after checking that each text still has its recorded hash.
        """
        from openhcs.core.config import GlobalPipelineConfig
        from openhcs.core.config_document import ConfigDocumentCodec
        from openhcs.core.pipeline_document import PipelineDocumentCodec
        from openhcs.processing.custom_functions import CustomFunctionManager
        from openhcs.processing.custom_functions.runtime_registry import (
            CustomFunctionRuntimeRegistry,
        )
        from openhcs.processing.custom_functions.source_namespace import (
            CustomFunctionSource,
        )

        function_name_by_source = {
            source_sha256: function.identity.name
            for step in self.steps
            for function in step.calls.functions
            for source_sha256 in function.identity.recorded_source_hashes()
        }
        for recorded_sha256, source_text in self.custom_sources.items():
            if CustomFunctionSource.content_digest(source_text.encode("utf-8")) != (
                recorded_sha256
            ):
                raise ValueError(
                    f"Run record {self.record_id}: custom source {recorded_sha256} does "
                    "not match its recorded hash."
                )
            source = CustomFunctionSource(
                function_name_by_source[recorded_sha256], recorded_sha256
            )
            if CustomFunctionRuntimeRegistry.declaration_for_source(source) is None:
                CustomFunctionManager().register_from_code(
                    source_text, persist=False, emit_signal=False
                )
        return (
            PipelineDocumentCodec.from_source(self.pipeline_code),
            ConfigDocumentCodec.from_source(
                self.global_config_code,
                expected_config_type=GlobalPipelineConfig,
            ),
        )


@dataclass(frozen=True, slots=True)
class StoredProducedFile:
    """What the metadata document stores for one saved file."""

    run_record: str
    producer: StreamProducerIdentity


@dataclass(frozen=True, slots=True)
class ProducedFile:
    """One output file, the step that wrote it and the record of the run."""

    record: RunRecord
    producer: StreamProducerIdentity

    @property
    def step(self) -> StepCalls:
        return self.record.step_for(self.producer)


@dataclass(frozen=True, slots=True)
class DatasetRunRecords:
    """The part of a dataset's metadata document that says what produced its files.

    The document stores each field of this class under the field's name.
    """

    run_records: Mapping[str, RunRecord] = field(default_factory=dict)
    produced_files: Mapping[str, StoredProducedFile] = field(default_factory=dict)
    """By path relative to the dataset root."""

    @classmethod
    def in_document(cls, document: JsonObject) -> "DatasetRunRecords":
        return dataclass_from_mapping(
            cls,
            {
                item.name: document[item.name]
                for item in fields(cls)
                if item.name in document
            },
        )

    @classmethod
    def of_dataset(cls, dataset_root: Path) -> "DatasetRunRecords":
        return cls.in_document(
            json.loads(_metadata_path(dataset_root).read_text(encoding="utf-8"))
        )

    def with_run(
        self, record: RunRecord, produced: Mapping[str, StreamProducerIdentity]
    ) -> "DatasetRunRecords":
        """Add one run's files; keep only the records some file still refers to."""
        record_id = record.record_id
        produced_files = {
            **self.produced_files,
            **{
                path: StoredProducedFile(record_id, producer)
                for path, producer in produced.items()
            },
        }
        referenced = {entry.run_record for entry in produced_files.values()}
        return DatasetRunRecords(
            run_records={
                stored_id: stored
                for stored_id, stored in {**self.run_records, record_id: record}.items()
                if stored_id in referenced
            },
            produced_files=produced_files,
        )


def _metadata_path(dataset_root: Path) -> Path:
    from openhcs.core.virtual_workspace_metadata import get_metadata_path

    return Path(get_metadata_path(dataset_root))


def _dataset_root_of(output_file: Path) -> Path:
    for directory in output_file.parents:
        if _metadata_path(directory).is_file():
            return directory
    raise UnrecordedOutputFile(
        f"No directory above {output_file} holds an OpenHCS metadata document."
    )


@dataclass(frozen=True, slots=True)
class ProducedFiles:
    """The saved paths of one run, each with the producer identity its writer stated."""

    producer_by_path: Mapping[Path, StreamProducerIdentity]

    def by_dataset_root(
        self, dataset_roots: Iterable[Path]
    ) -> Mapping[Path, "ProducedFiles"]:
        """Split the files by the declared output dataset root each one lies under.

        The roots are the ones the compiled plans declare. Where one declared
        root contains another, a file belongs to the nearest.
        """
        nearest_first = sorted(set(dataset_roots), key=lambda root: -len(root.parts))
        by_root: dict[Path, dict[Path, StreamProducerIdentity]] = {}
        for path, producer in self.producer_by_path.items():
            root = next(
                (root for root in nearest_first if path.is_relative_to(root)), None
            )
            if root is None:
                raise ValueError(
                    f"Saved file {path} lies under no declared output dataset root "
                    f"({', '.join(map(str, nearest_first))})."
                )
            by_root.setdefault(root, {})[path] = producer
        return MappingProxyType(
            {root: ProducedFiles(MappingProxyType(files)) for root, files in by_root.items()}
        )

    def write_into(
        self,
        document: dict[str, JsonValue],
        *,
        dataset_root: Path,
        record: RunRecord,
    ) -> None:
        """Store the record with the files this run saved under this dataset root.

        A document the run saved nothing under is left as it is. A record no
        file refers to any more is dropped.
        """
        if not self.producer_by_path:
            return
        document.update(
            to_jsonable(
                DatasetRunRecords.in_document(document).with_run(
                    record,
                    {
                        path.relative_to(dataset_root).as_posix(): producer
                        for path, producer in self.producer_by_path.items()
                    },
                )
            )
        )
