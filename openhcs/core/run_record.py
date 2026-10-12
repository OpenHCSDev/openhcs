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
"""

from __future__ import annotations

import hashlib
import inspect
import json
from abc import ABC, abstractmethod
from collections.abc import Iterable, Iterator, Mapping, Sequence
from dataclasses import dataclass, fields, is_dataclass, replace
from pathlib import Path
from types import MappingProxyType
from typing import TYPE_CHECKING, Any, ClassVar

import pycodify
from polystore.streaming.identity import StreamProducerIdentity

from openhcs.core.vfs_protocol import DatasetPathDeclaration, FileManagerLike

if TYPE_CHECKING:
    from openhcs.core.compiled_execution import CompiledExecutionBundle
    from openhcs.core.compiled_step_plan import CompiledStepPlan
    from openhcs.core.config import GlobalPipelineConfig
    from openhcs.core.function_patterns import CompiledFunctionInvocation
    from openhcs.core.pipeline.compilation_session import ResolvedPipelineDefinition
    from pycodify.documents import PipelineDocument

RUN_RECORDS_KEY = "run_records"
PRODUCED_FILES_KEY = "produced_files"
JsonRecord = dict[str, Any]


def python_expression(value: object) -> str:
    """Write a value the way generated pipeline code writes it."""
    import openhcs.serialization.pycodify_formatters  # noqa: F401 (registers formatters)

    return pycodify.to_source(value, pycodify.FormatContext(clean_mode=False)).code


class ValueSource(ABC):
    """Which declaration supplied a recorded value."""

    kind: ClassVar[str]

    @abstractmethod
    def details(self) -> JsonRecord:
        """The fields that identify the supplying declaration."""

    def to_record(self) -> JsonRecord:
        return {"kind": self.kind, **self.details()}


@dataclass(frozen=True, slots=True)
class WrittenInPipeline(ValueSource):
    """The pipeline document states the value."""

    kind: ClassVar[str] = "pipeline"

    def details(self) -> JsonRecord:
        return {}


@dataclass(frozen=True, slots=True)
class FunctionDefault(ValueSource):
    """The pipeline leaves the parameter out; the function's signature supplies it."""

    kind: ClassVar[str] = "function_default"
    function_key: str

    def details(self) -> JsonRecord:
        return {"function": self.function_key}


@dataclass(frozen=True, slots=True)
class SuppliedAtRunTime(ValueSource):
    """The platform passes the value when it calls the function."""

    kind: ClassVar[str] = "run_time"

    def details(self) -> JsonRecord:
        return {}


@dataclass(frozen=True, slots=True)
class SetOnObject(ValueSource):
    """The configured object itself holds the value."""

    kind: ClassVar[str] = "set_here"
    scope_id: str | None

    def details(self) -> JsonRecord:
        return {"scope": self.scope_id}


@dataclass(frozen=True, slots=True)
class InheritedFrom(ValueSource):
    """ObjectState resolved the value from this scope and class."""

    kind: ClassVar[str] = "inherited"
    scope_id: str | None
    source_type_name: str | None

    @classmethod
    def reported_by_object_state(
        cls, scope_id: str | None, source_type: type | None
    ) -> "InheritedFrom":
        """Keep the class by name: the declaration is pickled with the compiled bundle."""
        return cls(
            scope_id,
            None
            if source_type is None
            else f"{source_type.__module__}.{source_type.__qualname__}",
        )

    def details(self) -> JsonRecord:
        return {"scope": self.scope_id, "type": self.source_type_name}


@dataclass(frozen=True, slots=True)
class RecordedValue:
    """One resolved value and the declaration that supplied it."""

    name: str
    expression: str
    source: ValueSource

    def to_record(self) -> JsonRecord:
        return {
            "name": self.name,
            "value": self.expression,
            "source": self.source.to_record(),
        }


ObjectStateProvenance = Mapping[str, tuple[str | None, type | None]]


def _field_values(configured: object) -> dict[str, object]:
    return {item.name: getattr(configured, item.name) for item in fields(configured)}


def resolved_values(
    values: Mapping[str, object],
    provenance: ObjectStateProvenance,
    *,
    scope_id: str | None,
    prefix: str = "",
) -> Iterator[RecordedValue]:
    """Every leaf value of a resolved object, with the source ObjectState reported.

    ObjectState lists the paths it inherited; a path it does not list is held
    by the object itself. A nested config the object leaves unset is inherited
    whole and listed as one path, so the inherited check comes before descent.
    """
    for name, value in values.items():
        path = f"{prefix}{name}"
        if path in provenance:
            yield RecordedValue(
                path,
                python_expression(value),
                InheritedFrom.reported_by_object_state(*provenance[path]),
            )
        elif is_dataclass(value) and not isinstance(value, type):
            yield from resolved_values(
                _field_values(value), provenance, scope_id=scope_id, prefix=f"{path}."
            )
        else:
            yield RecordedValue(path, python_expression(value), SetOnObject(scope_id))


@dataclass(frozen=True, slots=True)
class RunDeclaration:
    """What the compiler alone knows about a run: documents and resolved configuration."""

    pipeline_code: str
    global_config_code: str
    configuration: tuple[RecordedValue, ...]
    step_configurations: tuple[tuple[RecordedValue, ...], ...] = ()
    """Resolved values of each enabled step, by compiled step index."""

    @classmethod
    def before_step_resolution(
        cls,
        orchestrator: Any,
        pipeline_definition: Sequence[Any],
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
            pipeline_code=PipelineDocumentCodec.render(
                PipelineDocumentCodec.from_values(
                    pipeline_config=orchestrator.pipeline_config,
                    pipeline_steps=pipeline_definition,
                ),
                clean_mode=False,
            ),
            global_config_code=ConfigDocumentCodec.render(
                saved_global_config,
                expected_config_type=GlobalPipelineConfig,
                clean_mode=False,
            ),
            configuration=tuple(
                resolved_values(
                    _field_values(effective_config),
                    provenance,
                    scope_id=str(orchestrator.dataset_root),
                )
            ),
        )

    def with_resolved_steps(
        self, pipeline: "ResolvedPipelineDefinition"
    ) -> "RunDeclaration":
        """Add each enabled step's resolved values from the compiler's one resolution."""
        return replace(
            self,
            step_configurations=tuple(
                tuple(
                    resolved_values(
                        step.configuration_parameters(),
                        pipeline.step_provenance[index],
                        scope_id=pipeline.step_scope_ids[index],
                    )
                )
                for index, step in enumerate(pipeline.steps)
            ),
        )


def _parameters(invocation: "CompiledFunctionInvocation", function_key: str) -> list[JsonRecord]:
    """Every parameter of the function's signature with its effective value and source."""
    contract = invocation.contract
    written = invocation.kwargs_dict
    supplied_at_run_time = {
        *contract.runtime_owned_parameter_names,
        invocation.primary_input_parameter_name,
    }
    recorded: list[RecordedValue] = []
    for name, parameter in contract.canonical_signature.parameters.items():
        if name in written:
            recorded.append(
                RecordedValue(name, python_expression(written[name]), WrittenInPipeline())
            )
        elif name in supplied_at_run_time or parameter.default is inspect.Parameter.empty:
            recorded.append(
                RecordedValue(name, "<supplied when the function is called>", SuppliedAtRunTime())
            )
        else:
            recorded.append(
                RecordedValue(
                    name,
                    python_expression(parameter.default),
                    FunctionDefault(function_key),
                )
            )
    recorded.extend(
        RecordedValue(name, python_expression(value), WrittenInPipeline())
        for name, value in written.items()
        if name not in contract.canonical_signature.parameters
    )
    return [value.to_record() for value in recorded]


def _declared_files(
    invocation: "CompiledFunctionInvocation",
    *,
    filemanager: FileManagerLike,
    backend: str,
) -> list[JsonRecord]:
    """Each declared path parameter, with what the storage layer says the file holds."""
    declared: Mapping[str, tuple[DatasetPathDeclaration, object]] = (
        invocation.contract.declared_path_values(invocation.kwargs_dict)
    )
    return [
        {
            "parameter": parameter_name,
            "declared_as": declaration.plain_name,
            "path": str(path),
            "content": declaration.content_at_run_start(
                Path(path), filemanager=filemanager, backend=backend
            ).to_record(),
        }
        for parameter_name, (declaration, path) in declared.items()
    ]


def _step_record(
    plan: "CompiledStepPlan",
    configuration: Iterable[RecordedValue],
    *,
    filemanager: FileManagerLike,
    backend: str,
) -> tuple[JsonRecord, dict[str, str]]:
    custom_sources: dict[str, str] = {}
    functions = []
    for invocation in plan.compiled_function_pattern.iter_invocations():
        identity = invocation.contract.func.identity()
        custom_sources.update(identity.custom_sources())
        functions.append(
            {
                "identity": identity.to_record(),
                "group": python_expression(invocation.key.group_key),
                "position": invocation.key.position,
                "input_memory_type": invocation.input_memory_type,
                "output_memory_type": invocation.output_memory_type,
                "parameters": _parameters(invocation, identity.key),
                "declared_files": _declared_files(
                    invocation, filemanager=filemanager, backend=backend
                ),
            }
        )
    return (
        {
            "name": plan.step_name,
            "pipeline_position": plan.pipeline_position,
            "step_scope_id": plan.step_scope_id,
            "input_memory_type": plan.input_memory_type,
            "output_memory_type": plan.output_memory_type,
            "assigned_gpu_devices": [
                {"memory_type": binding.memory_type.value, "device_id": binding.device_id}
                for binding in plan.device_assignment.bindings
            ],
            "functions": functions,
            "configuration": [value.to_record() for value in configuration],
        },
        custom_sources,
    )


@dataclass(frozen=True, slots=True)
class ProducedFile:
    """One output file, the step that wrote it and the record of the run."""

    record: "RunRecord"
    producer: StreamProducerIdentity

    @property
    def step(self) -> JsonRecord:
        return self.record.step_for(self.producer)


class UnrecordedOutputFile(LookupError):
    """The dataset's metadata does not say which step produced this file."""


@dataclass(frozen=True, slots=True)
class RunRecord:
    """What produced an output dataset, as stored: JSON-native, addressed by its content."""

    content: Mapping[str, Any]

    @property
    def record_id(self) -> str:
        return hashlib.sha256(
            json.dumps(self.content, sort_keys=True, separators=(",", ":")).encode("utf-8")
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
        import openhcs
        from openhcs.runtime.environment_provenance import RuntimeEnvironmentSnapshot

        declaration = bundle.run_declaration
        steps: dict[int, JsonRecord] = {}
        custom_sources: dict[str, str] = {}
        for axis_id in bundle.axis_ids:
            context = next(
                context
                for context in bundle.runtime_contexts.values()
                if context.require_axis_id() == axis_id
            )
            for index, plan in context.step_plans.items():
                if index in steps:
                    continue
                steps[index], sources = _step_record(
                    plan,
                    declaration.step_configurations[index],
                    filemanager=filemanager,
                    backend=backend,
                )
                custom_sources.update(sources)
        environment = RuntimeEnvironmentSnapshot.current()
        return cls(
            {
                "software": {
                    "openhcs": openhcs.__version__,
                    "python": environment.python_version,
                    "python_implementation": environment.python_implementation,
                    "platform": environment.sys_platform,
                    "machine": environment.machine,
                    "installed_distributions": {
                        item.name: item.version
                        for item in environment.installed_distributions
                    },
                },
                "pipeline_code": declaration.pipeline_code,
                "global_config_code": declaration.global_config_code,
                "configuration": [value.to_record() for value in declaration.configuration],
                "steps": [steps[index] for index in sorted(steps)],
                "custom_sources": custom_sources,
            }
        )

    @property
    def steps(self) -> Sequence[JsonRecord]:
        return self.content["steps"]

    def step_for(self, producer: StreamProducerIdentity) -> JsonRecord:
        """The step a producer identity names, matched on the two fields it carries."""
        matches = [
            step
            for step in self.steps
            if step["step_scope_id"] == producer.step_scope_id
            and step["pipeline_position"] == producer.pipeline_position
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
        return MappingProxyType(
            {
                record_id: cls(content)
                for record_id, content in _metadata_document(Path(dataset_root))
                .get(RUN_RECORDS_KEY, {})
                .items()
            }
        )

    @classmethod
    def for_output_file(cls, output_file: str | Path) -> ProducedFile:
        """The record and producing step of one output file.

        The answer comes only from what the writer stored for this path; a file
        the dataset does not list raises instead of being guessed from its name.
        """
        path = Path(output_file).resolve()
        dataset_root = _dataset_root_of(path)
        document = _metadata_document(dataset_root)
        entry = document.get(PRODUCED_FILES_KEY, {}).get(
            path.relative_to(dataset_root).as_posix()
        )
        if entry is None:
            raise UnrecordedOutputFile(
                f"{path} is not recorded as a step output in "
                f"{_metadata_path(dataset_root)}."
            )
        return ProducedFile(
            record=cls(document[RUN_RECORDS_KEY][entry["run_record"]]),
            producer=StreamProducerIdentity.from_payload(entry["producer"]),
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
            function["identity"]["custom_source_sha256"]: function["identity"]["name"]
            for step in self.steps
            for function in step["functions"]
            if "custom_source_sha256" in function["identity"]
        }
        for recorded_sha256, source_text in self.content["custom_sources"].items():
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
            PipelineDocumentCodec.from_source(self.content["pipeline_code"]),
            ConfigDocumentCodec.from_source(
                self.content["global_config_code"],
                expected_config_type=GlobalPipelineConfig,
            ),
        )


def _metadata_path(dataset_root: Path) -> Path:
    from openhcs.core.virtual_workspace_metadata import get_metadata_path

    return Path(get_metadata_path(dataset_root))


def _metadata_document(dataset_root: Path) -> Mapping[str, Any]:
    return json.loads(_metadata_path(dataset_root).read_text(encoding="utf-8"))


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
        document: dict[str, Any],
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
        records = document.setdefault(RUN_RECORDS_KEY, {})
        produced = document.setdefault(PRODUCED_FILES_KEY, {})
        record_id = record.record_id
        records[record_id] = dict(record.content)
        for path, producer in self.producer_by_path.items():
            produced[path.relative_to(dataset_root).as_posix()] = {
                "run_record": record_id,
                "producer": dict(producer.to_payload()),
            }
        referenced = {entry["run_record"] for entry in produced.values()}
        for stale in set(records) - referenced:
            del records[stale]
