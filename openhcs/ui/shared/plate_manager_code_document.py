"""Canonical PlateManager Python document shared by every UI frontend."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass, fields, is_dataclass
from functools import cache
from pathlib import Path
from typing import Any, Self, get_args, get_origin, get_type_hints

from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
from openhcs.core.function_step_transport import FunctionStepTransportAuthority
from openhcs.core.steps.function_step import FunctionStep
from openhcs.core.dataset_sources.dataset_scopes import DatasetScope


class PlateManagerCodeNamespace(dict):
    """Nominal execution namespace for PlateManager documents."""


@dataclass(frozen=True, slots=True)
class PlateManagerDocumentAssignments:
    """The public assignments of a PlateManager code document, one field each.

    The field names are the assigned names; nothing else may be assigned.
    """

    plate_paths: object
    global_config: object
    per_plate_configs: object
    pipeline_data: object

    @classmethod
    def names(cls) -> tuple[str, ...]:
        return tuple(declared.name for declared in fields(cls))

    @classmethod
    def from_namespace(cls, namespace: Mapping[str, object]) -> Self:
        for name in cls.names():
            if name not in namespace:
                raise ValueError(f"PlateManager code document must define {name!r}.")
        return cls(**{name: namespace[name] for name in cls.names()})

    def to_namespace(self) -> PlateManagerCodeNamespace:
        return PlateManagerCodeNamespace(
            {name: getattr(self, name) for name in self.names()}
        )


@dataclass(frozen=True, slots=True)
class PlateManagerOrchestratorCodePayload:
    """Validated semantic contents of one PlateManager code document."""

    plate_paths: tuple[str, ...]
    global_pipeline_config: GlobalPipelineConfig
    per_plate_configs: dict[str, PipelineConfig]
    pipeline_data: dict[str, list[FunctionStep]]


class PlateManagerCodeDocumentAuthority:
    """Normalize, render, and parse the canonical PlateManager document."""

    HEADER = "# Edit this orchestrator configuration and save to apply changes"

    @classmethod
    def declared_external_value_types(cls) -> frozenset[type[object]]:
        """Return external value types reachable from the document config roots.

        The document renderer emits the defining import for enum and dataclass
        values. Derive those trusted external types from the same config classes
        accepted by :meth:`from_namespace`, so UI source validation cannot drift
        into a separately maintained dependency allowlist.
        """

        return _declared_external_value_types()

    @classmethod
    def from_values(
        cls,
        *,
        plate_paths: Sequence[str | Path],
        global_pipeline_config: GlobalPipelineConfig,
        per_plate_configs: Mapping[str | Path, PipelineConfig],
        pipeline_data: Mapping[str | Path, Sequence[FunctionStep]],
    ) -> PlateManagerOrchestratorCodePayload:
        return cls._payload(
            PlateManagerDocumentAssignments(
                plate_paths=list(plate_paths),
                global_config=global_pipeline_config,
                per_plate_configs=dict(per_plate_configs),
                pipeline_data={path: list(steps) for path, steps in pipeline_data.items()},
            )
        )

    @classmethod
    def from_namespace(
        cls,
        namespace: Mapping[str, object],
    ) -> PlateManagerOrchestratorCodePayload:
        return cls._payload(PlateManagerDocumentAssignments.from_namespace(namespace))

    @classmethod
    def _payload(
        cls, assignments: PlateManagerDocumentAssignments
    ) -> PlateManagerOrchestratorCodePayload:
        plate_paths_value = assignments.plate_paths
        global_config_value = assignments.global_config
        per_plate_configs_value = assignments.per_plate_configs
        pipeline_data_value = assignments.pipeline_data

        if not isinstance(plate_paths_value, list):
            raise TypeError("plate_paths must be a list of strings or Paths.")
        plate_paths = tuple(
            cls._scope_id(path, field_name="plate_paths") for path in plate_paths_value
        )
        if len(set(plate_paths)) != len(plate_paths):
            raise ValueError("plate_paths must not contain duplicate plate scopes.")

        if not isinstance(global_config_value, GlobalPipelineConfig):
            raise TypeError("global_config must be a GlobalPipelineConfig.")

        if not isinstance(per_plate_configs_value, dict):
            raise TypeError(
                "per_plate_configs must be a dict of PipelineConfig values."
            )
        per_plate_configs: dict[str, PipelineConfig] = {}
        for path, pipeline_config in per_plate_configs_value.items():
            scope_id = cls._scope_id(path, field_name="per_plate_configs key")
            if not isinstance(pipeline_config, PipelineConfig):
                raise TypeError(
                    "per_plate_configs values must be PipelineConfig instances."
                )
            per_plate_configs[scope_id] = pipeline_config

        if not isinstance(pipeline_data_value, dict):
            raise TypeError(
                "pipeline_data must be a dict of plate paths to FunctionStep lists."
            )
        pipeline_data: dict[str, list[FunctionStep]] = {}
        for path, steps in pipeline_data_value.items():
            scope_id = cls._scope_id(path, field_name="pipeline_data key")
            if not isinstance(steps, list):
                raise TypeError("pipeline_data values must be FunctionStep lists.")
            pipeline_data[scope_id] = FunctionStepTransportAuthority.normalize_pipeline(
                steps
            )

        plate_scope_ids = frozenset(plate_paths)
        if frozenset(per_plate_configs) != plate_scope_ids:
            raise ValueError("per_plate_configs keys must exactly match plate_paths.")
        if frozenset(pipeline_data) != plate_scope_ids:
            raise ValueError("pipeline_data keys must exactly match plate_paths.")

        return PlateManagerOrchestratorCodePayload(
            plate_paths=plate_paths,
            global_pipeline_config=global_config_value,
            per_plate_configs=per_plate_configs,
            pipeline_data=pipeline_data,
        )

    @classmethod
    def from_source(cls, source: str) -> PlateManagerOrchestratorCodePayload:
        namespace = PlateManagerCodeNamespace()
        exec(compile(source, "<openhcs-plate-manager-document>", "exec"), namespace)
        return cls.from_namespace(namespace)

    @classmethod
    def to_namespace(
        cls,
        payload: PlateManagerOrchestratorCodePayload,
    ) -> PlateManagerCodeNamespace:
        normalized = cls.from_values(
            plate_paths=payload.plate_paths,
            global_pipeline_config=payload.global_pipeline_config,
            per_plate_configs=payload.per_plate_configs,
            pipeline_data=payload.pipeline_data,
        )
        return PlateManagerDocumentAssignments(
            plate_paths=list(normalized.plate_paths),
            global_config=normalized.global_pipeline_config,
            per_plate_configs=dict(normalized.per_plate_configs),
            pipeline_data={
                path: list(steps) for path, steps in normalized.pipeline_data.items()
            },
        ).to_namespace()

    @classmethod
    def render(
        cls,
        payload: PlateManagerOrchestratorCodePayload,
        *,
        clean_mode: bool = True,
    ) -> str:
        import openhcs.serialization.pycodify_formatters  # noqa: F401
        from pycodify import Assignment, BlankLine, CodeBlock, generate_python_source

        normalized = cls.from_values(
            plate_paths=payload.plate_paths,
            global_pipeline_config=payload.global_pipeline_config,
            per_plate_configs=payload.per_plate_configs,
            pipeline_data=payload.pipeline_data,
        )
        code_value_by_scope = {
            scope_id: DatasetScope.parse(scope_id).code_value()
            for scope_id in normalized.plate_paths
        }
        document = PlateManagerDocumentAssignments(
            plate_paths=[
                code_value_by_scope[scope_id] for scope_id in normalized.plate_paths
            ],
            global_config=normalized.global_pipeline_config,
            per_plate_configs={
                code_value_by_scope[scope_id]: config
                for scope_id, config in normalized.per_plate_configs.items()
            },
            pipeline_data={
                code_value_by_scope[scope_id]: steps
                for scope_id, steps in normalized.pipeline_data.items()
            },
        )
        items = []
        for name in document.names():
            if items:
                items.append(BlankLine())
            items.append(Assignment(name, getattr(document, name)))
        body = CodeBlock.from_items(tuple(items))
        return generate_python_source(
            body,
            header=cls.HEADER,
            clean_mode=clean_mode,
        )

    @staticmethod
    def _scope_id(value: object, *, field_name: str) -> str:
        if not isinstance(value, (str, Path)):
            raise TypeError(f"{field_name} must be a plate path string or Path.")
        return DatasetScope.parse(str(value)).scope_id


@cache
def _declared_external_value_types() -> frozenset[type[object]]:
    declared_types = _reachable_declared_types((GlobalPipelineConfig, PipelineConfig))
    return frozenset(
        declared_type
        for declared_type in declared_types
        if declared_type.__module__.split(".", maxsplit=1)[0]
        not in {"builtins", "openhcs"}
    )


def _reachable_declared_types(
    roots: Sequence[type[object]],
) -> frozenset[type[object]]:
    pending = list(roots)
    visited: set[type[object]] = set()
    while pending:
        declared_type = pending.pop()
        if declared_type in visited:
            continue
        visited.add(declared_type)
        if not is_dataclass(declared_type):
            continue
        annotations = get_type_hints(declared_type, include_extras=True)
        for declared_field in fields(declared_type):
            annotation = annotations.get(declared_field.name, declared_field.type)
            pending.extend(_annotation_types(annotation))
    return frozenset(visited)


def _annotation_types(annotation: object) -> tuple[type[object], ...]:
    if annotation is Any:
        return ()
    if isinstance(annotation, type):
        return (annotation,)
    return (
        tuple(
            nested_type
            for member in get_args(annotation)
            for nested_type in _annotation_types(member)
        )
        if get_origin(annotation) is not None
        else ()
    )
