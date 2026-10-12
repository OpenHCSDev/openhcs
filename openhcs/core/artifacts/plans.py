"""Compiled artifact plans and the identity they share with declarations.

``ArtifactSpecRef`` names one declared artifact independently of scope. A
compiled ``ArtifactPlan`` is where one produced or consumed artifact is stored.
A function output goes to an ``OutputTarget``: a compiled ``ArtifactOutputPlan``
or the invocation's main image flow (``MainFlowTarget``).
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Callable, Mapping
from dataclasses import dataclass, field, replace
from pathlib import Path
from types import MappingProxyType
from typing import TYPE_CHECKING, ClassVar, Self, TypeVar, cast

from metaclass_registry import AutoRegisterMeta

from openhcs.core.artifacts.kinds import ArtifactType, SpecialArtifactType
from openhcs.core.artifacts.payloads import (
    ArtifactMaterializationPayload,
    NamedArtifactPayload,
)
from openhcs.core.artifacts.sidecars import ArtifactSidecarRole
from openhcs.core.artifacts.streaming import AutomaticStreaming, ViewerStreaming
from openhcs.core.axes import Axis
from openhcs.core.component_group_scope import ComponentGroupScope, UngroupedScope
from openhcs.core.component_set import ComponentSet

if TYPE_CHECKING:
    from openhcs.core.artifacts.relations import (
        ArtifactSpecRelation,
        ObjectArtifactSubjectBinding,
    )
    from openhcs.core.runtime_artifact_values import RuntimeValue
    from openhcs.core.runtime_image_values import ImagePayloadMetadata
    from openhcs.core.runtime_measurements import MeasurementSubject

AnswerT = TypeVar("AnswerT")


def require_plan_type(plan_type: type[ArtifactPlan]) -> type[ArtifactPlan]:
    """Return one artifact plan role class, or fail."""
    if isinstance(plan_type, type) and issubclass(plan_type, ArtifactPlan):
        return plan_type
    raise TypeError(
        "Artifact plan type must be an ArtifactPlan class, "
        f"got {type(plan_type).__name__}."
    )


def require_registered_plan_type(
    plan_type: type[ArtifactPlan],
    field_name: str,
) -> type[ArtifactPlan]:
    """Return one registered artifact plan role class for a declaration field."""
    resolved_plan_type = require_plan_type(plan_type)
    if resolved_plan_type not in ArtifactPlan.__registry__.values():
        raise ValueError(
            f"{field_name} is not a registered ArtifactPlan type: "
            f"{resolved_plan_type.__name__}."
        )
    return resolved_plan_type


@dataclass(frozen=True)
class ArtifactSpecRef:
    """Scope-free identity for one declared artifact spec."""

    plan_type: type[ArtifactPlan]
    artifact_type: type[ArtifactType]
    name: str

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "plan_type",
            require_registered_plan_type(self.plan_type, "ArtifactSpecRef.plan_type"),
        )
        object.__setattr__(
            self,
            "artifact_type",
            ArtifactType.require_registered(
                self.artifact_type,
                "ArtifactSpecRef.artifact_type",
            ),
        )
        if not self.name:
            raise ValueError("ArtifactSpecRef.name cannot be empty.")

    def for_plan_type(
        self,
        plan_type: type[ArtifactPlan],
    ) -> ArtifactSpecRef:
        """Return this artifact identity under another compiled plan role."""

        return replace(self, plan_type=require_plan_type(plan_type))


class DeclaredRelations:
    """Answers a declaration or plan derives from its declared relations.

    Members declare ``relations``, ``artifact_type`` and ``ref()``.
    """

    relations: tuple[ArtifactSpecRelation, ...]
    artifact_type: type[ArtifactType]

    def relation_answers(
        self,
        answer: Callable[[ArtifactSpecRelation], AnswerT | None],
    ) -> tuple[AnswerT, ...]:
        """Return each distinct answer the declared relations give, in order."""
        return tuple(
            dict.fromkeys(
                value
                for relation in self.relations
                for value in (answer(relation),)
                if value is not None
            )
        )

    def single_relation_answer(
        self,
        answer: Callable[[ArtifactSpecRelation], AnswerT | None],
        what: str,
    ) -> AnswerT | None:
        """Return the one answer the relations give, if any; two is an error."""
        values = self.relation_answers(answer)
        if len(values) > 1:
            raise ValueError(
                f"Artifact {self.ref()!r} declares multiple {what}: {values!r}."
            )
        return values[0] if values else None

    def group_scope_sources(self) -> tuple[ArtifactSpecRef, ...]:
        """Return the declared sources that own this artifact's group scope."""
        return self.relation_answers(lambda relation: relation.group_scope_source())

    def source_context_sources(self) -> tuple[ArtifactSpecRef, ...]:
        """Return declared sources that carry this artifact's runtime context."""
        if self.artifact_type.carries_source_image_context:
            return self.relation_answers(
                lambda relation: relation.source_context_source()
            )
        return ()

    def source_context_source(self) -> ArtifactSpecRef | None:
        """Return the sole declared runtime-context source, if any."""
        sources = self.source_context_sources()
        if len(sources) > 1:
            raise ValueError(
                f"Artifact {self.ref()!r} declares multiple runtime-context "
                f"sources: {sources!r}."
            )
        return sources[0] if sources else None

    def source_stack_scope_sources(self) -> tuple[ArtifactSpecRef, ...]:
        """Return exact sources whose complete runtime stacks are preserved."""
        return self.relation_answers(
            lambda relation: relation.source_stack_scope_source()
        )

    def stack_broadcast_sources(self) -> tuple[ArtifactSpecRef, ...]:
        """Return exact input-stack sources that may broadcast this artifact."""
        return self.relation_answers(lambda relation: relation.stack_broadcast_source())

    def materialization_source(self) -> ArtifactSpecRef | None:
        """Return the sole declared materialization identity source, if any."""
        return self.single_relation_answer(
            lambda relation: relation.materialization_source(),
            "materialization identity sources",
        )

    def object_subject_binding(self) -> ObjectArtifactSubjectBinding | None:
        """Return the sole object-subject binding declared by this artifact."""
        return self.single_relation_answer(
            lambda relation: relation.object_subject_binding(),
            "object-subject bindings",
        )

    def measurement_subjects(self) -> tuple[MeasurementSubject, ...]:
        """Return every exact measurement subject the relations declare."""
        return self.relation_answers(lambda relation: relation.measurement_subject())

    def measurement_subject(self) -> MeasurementSubject | None:
        """Return the one subject of a table-wide measurement output, if any."""
        return self.single_relation_answer(
            lambda relation: relation.measurement_subject(),
            "measurement subjects",
        )

    def require_measurement_subject(self) -> MeasurementSubject:
        """Require the same declared subject at compile and runtime boundaries."""
        subject = self.measurement_subject()
        if subject is None:
            raise ValueError(
                f"Measurement output {self.ref()!r} has no declared "
                "measurement subject relation. Add ImageMeasurementSubjectRelation "
                "with the exact declared image ref for image-level rows, "
                "ObjectMeasurementSubjectRelation with the exact object-label ref "
                "for object-level rows, or ArtifactMeasurementSubjectRelation() "
                "for artifact-level rows to ArtifactSpec.output(..., relations=(...,))."
            )
        return subject

    def dependency_refs(self) -> tuple[ArtifactSpecRef, ...]:
        """Return exact artifacts required by this artifact's relations."""
        return tuple(
            dict.fromkeys(
                dependency
                for relation in self.relations
                for dependency in relation.dependency_refs()
            )
        )


class OutputTarget(ABC):
    """Where one function output goes, answering what its context must be."""

    variable_components: tuple[type[Axis], ...]
    requires_source_slice_identity: ClassVar[bool]
    """Whether a self-contextualized output must name its source's exact slices."""

    @abstractmethod
    def describe(self) -> str:
        """Name this target in diagnostics."""

    @abstractmethod
    def source_context_source(self) -> ArtifactSpecRef | None:
        """Return the declared artifact supplying the output's source context."""

    @abstractmethod
    def collapses_runtime_slices(self) -> bool:
        """Whether an output stored here holds one runtime slice, not the stack."""

    @abstractmethod
    def require_measurement_subject(self) -> MeasurementSubject:
        """Return the measurement subject the output's rows belong to."""

    @abstractmethod
    def validate_payload_name(self, payload: NamedArtifactPayload) -> None:
        """Require a named payload to carry the name this target declares."""


@dataclass(frozen=True)
class MainFlowTarget(OutputTarget):
    """The invocation's main image flow: it keeps the runtime stack it returns."""

    variable_components: ClassVar[tuple[type[Axis], ...]] = ()
    requires_source_slice_identity: ClassVar[bool] = False

    def describe(self) -> str:
        return "main-flow image output"

    def source_context_source(self) -> ArtifactSpecRef | None:
        return None

    def collapses_runtime_slices(self) -> bool:
        return False

    def require_measurement_subject(self) -> MeasurementSubject:
        raise ValueError(
            "The main image flow carries no measurement subject; measurement "
            "outputs require a compiled output plan."
        )

    def validate_payload_name(self, payload: NamedArtifactPayload) -> None:
        payload.require_name()


MAIN_FLOW = MainFlowTarget()


@dataclass(frozen=True)
class ArtifactPlan(DeclaredRelations, ABC, metaclass=AutoRegisterMeta):
    """Compiled storage plan shared by produced and consumed artifacts."""

    __registry_key__ = "plan_role"
    __skip_if_no_key__ = True

    plan_role: ClassVar[str]

    name: str
    path: str
    artifact_type: type[ArtifactType] = SpecialArtifactType
    group_scope: ComponentGroupScope = field(default_factory=UngroupedScope)
    variable_components: tuple[type[Axis], ...] = ()
    component_domains: tuple[ComponentGroupScope, ...] = ()
    paths_by_group: Mapping[str | None, str] | None = None
    sidecar_role: type[ArtifactSidecarRole] | None = None

    _missing_group_uses_default_path: ClassVar[bool] = False
    relations: tuple[ArtifactSpecRelation, ...] = ()

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "artifact_type",
            ArtifactType.coerce(self.artifact_type),
        )
        object.__setattr__(
            self,
            "variable_components",
            ComponentSet.of(self.variable_components).as_tuple(),
        )
        object.__setattr__(
            self,
            "component_domains",
            ComponentGroupScope.one_per_component(
                self.component_domains,
                owner=f"Artifact plan {self.name!r}",
            ),
        )
        for grouped in self.group_scope.as_grouped():
            if grouped.component in self.variable_components:
                raise ValueError(
                    f"Artifact plan {self.name!r} cannot group by "
                    f"{grouped.component.name!r} while also retaining it as a "
                    "variable component."
                )

    @property
    def participates_in_main_flow(self) -> bool:
        """Return whether this compiled artifact publishes to the main image flow."""

        return self.artifact_type.publishes_to_main_flow(self.sidecar_role)

    def relation_scope(
        self,
        component: type[Axis] | None,
    ) -> ComponentGroupScope:
        """Return the domain this plan carries for one relation component."""

        domain = None if component is None else self.component_domain(component)
        return self.group_scope if domain is None else domain

    def component_domain(
        self,
        component: type[Axis],
    ) -> ComponentGroupScope | None:
        """Return the compiled domain inherited for one component axis."""

        return next(
            (
                domain
                for domain in self.component_domains
                if domain.component is component
            ),
            None,
        )

    def component_coordinate_scopes(self) -> tuple[ComponentGroupScope, ...]:
        """Return every compiler-owned component coordinate domain for this plan."""

        scopes_by_component = {
            domain.component: domain for domain in self.component_domains
        }
        for group_scope in self.group_scope.as_grouped():
            inherited_domain = scopes_by_component.get(group_scope.component)
            if inherited_domain is not None and not inherited_domain.contains_scope(
                group_scope
            ):
                raise ValueError(
                    f"Artifact plan {self.name!r} group scope {group_scope!r} "
                    f"falls outside its compiled component domain "
                    f"{inherited_domain!r}."
                )
            scopes_by_component[group_scope.component] = group_scope
        return tuple(
            scopes_by_component[component]
            for component in sorted(
                scopes_by_component,
                key=lambda value: value.name,
            )
        )

    def is_component_coordinate_disjoint_from(self, other: ArtifactPlan) -> bool:
        """Return whether compiled component scopes prove two plans cannot collide."""

        other_scopes = {
            scope.component: scope for scope in other.component_coordinate_scopes()
        }
        return any(
            own_scope.excludes(other_scopes[own_scope.component])
            for own_scope in self.component_coordinate_scopes()
            if own_scope.component in other_scopes
        )

    def require_single_group_key(self) -> str | None:
        """Return the only artifact group key, failing for ambiguous groups."""
        if self.group_scope.names_several_keys:
            raise RuntimeError(
                f"Artifact plan '{self.name}' requires one group key, got "
                f"{self.group_scope.keys!r}."
            )
        return self.group_scope.single_key()

    def ref(self) -> ArtifactSpecRef:
        """Return this compiled plan's scope-free declaration identity."""
        return ArtifactSpecRef(
            plan_type=type(self),
            artifact_type=self.artifact_type,
            name=self.name,
        )

    @classmethod
    def require_exact_map(
        cls,
        plans: Mapping[object, object],
        *,
        boundary: str,
    ) -> None:
        """Require a caller-owned map to preserve each plan's exact identity."""

        for plan_ref, artifact_plan in plans.items():
            if not isinstance(plan_ref, ArtifactSpecRef):
                raise TypeError(
                    f"{boundary} maps require ArtifactSpecRef keys, got "
                    f"{type(plan_ref).__name__}."
                )
            if not isinstance(artifact_plan, cls):
                raise TypeError(
                    f"{boundary} maps require {cls.__name__} values, got "
                    f"{type(artifact_plan).__name__} for {plan_ref!r}."
                )
            if plan_ref != artifact_plan.ref():
                raise ValueError(
                    f"{boundary} key {plan_ref!r} conflicts with plan ref "
                    f"{artifact_plan.ref()!r}."
                )

    def _path_for_group(self, group_key: str | None) -> str | None:
        if not self.paths_by_group:
            return self.path
        if group_key in self.paths_by_group:
            return self.paths_by_group[group_key]
        if None in self.paths_by_group:
            component = self.group_scope.component
            if group_key is None or component is None:
                return self.paths_by_group[None]
            return grouped_artifact_path(
                self.paths_by_group[None], component, group_key
            )
        if self._missing_group_uses_default_path:
            return self.path
        return None

    def _plan_for_group(self, group_key: str | None) -> Self | None:
        group_path = self._path_for_group(group_key)
        if group_path is None:
            return None
        return cast(
            Self,
            replace(
                self,
                path=group_path,
                group_scope=ComponentGroupScope.of(
                    (group_key,), self.group_scope.component
                ),
                paths_by_group={group_key: group_path},
            ),
        )


@dataclass(frozen=True)
class ArtifactOutputPlan(ArtifactPlan, OutputTarget):
    """Compiled storage plan for one produced artifact."""

    plan_role: ClassVar[str] = "output"
    _missing_group_uses_default_path: ClassVar[bool] = True
    requires_source_slice_identity: ClassVar[bool] = True

    materialization: ArtifactMaterializationPayload | None = None
    viewer_streaming: type[ViewerStreaming] = AutomaticStreaming
    group_scope_sources_by_group: Mapping[
        str | None,
        tuple[ArtifactSpecRef, ...],
    ] = field(default_factory=dict)
    producer_step_index: int | str | None = None
    producer_step_scope_id: str | None = None
    producer_step_name: str | None = None

    def __post_init__(self) -> None:
        super().__post_init__()
        declared_group_scope_sources = super().group_scope_sources()
        normalized_sources_by_group: dict[
            str | None,
            tuple[ArtifactSpecRef, ...],
        ] = {}
        for group_key, source_refs in self.group_scope_sources_by_group.items():
            normalized_refs = tuple(dict.fromkeys(source_refs))
            undeclared = tuple(
                ref
                for ref in normalized_refs
                if ref not in declared_group_scope_sources
            )
            if undeclared:
                raise ValueError(
                    f"Artifact output {self.ref()!r} component groups reference "
                    f"undeclared group-scope sources {undeclared!r}."
                )
            normalized_sources_by_group[
                ComponentGroupScope.normalize_key(group_key)
            ] = normalized_refs
        object.__setattr__(
            self,
            "group_scope_sources_by_group",
            normalized_sources_by_group,
        )
        self.source_context_source()

    # -- OutputTarget ------------------------------------------------------

    def describe(self) -> str:
        return repr(self.ref())

    def collapses_runtime_slices(self) -> bool:
        return not self.variable_components

    def validate_payload_name(self, payload: NamedArtifactPayload) -> None:
        payload.validate_artifact_name(self.name)

    # -- runtime payloads --------------------------------------------------

    def normalize_payload(self, value: object, *, axis_id: str) -> object:
        """Normalize a produced payload through this compiled storage scope."""

        from openhcs.core.runtime_artifact_values import RuntimeValue
        from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

        kind = self.artifact_type
        returned = RuntimeSliceProjection.match_alignment(
            value,
            scalar=lambda scalar: scalar,
            aligned=lambda aligned: aligned.map_slices(RuntimeValue.payload_of),
        )
        normalized = RuntimeSliceProjection.match_alignment(
            kind.normalize_runtime_payload(self.name, returned),
            scalar=lambda scalar: scalar,
            aligned=lambda aligned: kind.normalize_slice_aligned_value(
                aligned, self, axis_id=axis_id
            ),
        )
        if not self.group_scope.as_grouped() or self.variable_components:
            return normalized
        return kind.normalize_group_scoped_payload(self, normalized)

    def materialization_uses_source_identity_filename(self) -> bool:
        """Return whether this output's materialized files require source identity."""
        return (
            self.materialization is not None
            and self.materialization.uses_source_identity_filename()
        )

    def retained_filename_qualifier(self) -> str | None:
        """Return the role this output's kind adds to retained source filenames."""
        return self.artifact_type.retained_filename_qualifier(self.name)

    def materialization_metadata(
        self,
        value: RuntimeValue,
    ) -> ImagePayloadMetadata:
        """Derive filename metadata from the declared naming source."""

        payload_metadata = self.artifact_type.materialization_image_metadata(value)
        if self.names_files_from_independent_source():
            source_metadata = value.materialization_source_metadata
            if source_metadata is None:
                raise ValueError(
                    f"Artifact output {self.ref()!r} declares independent "
                    f"materialization source {self.materialization_source()!r}, "
                    "but its runtime value carries no materialization-source "
                    "metadata."
                )
            return payload_metadata.with_source_provenance(
                source_metadata.source_provenance
            )
        return payload_metadata

    def names_files_from_independent_source(self) -> bool:
        """Whether files are named after a source other than the context source."""
        materialization_source = self.materialization_source()
        return (
            materialization_source is not None
            and materialization_source != self.source_context_source()
        )

    def group_scope_sources(self) -> tuple[ArtifactSpecRef, ...]:
        """Return the compiled sources that own this output's group scope."""

        declared = super().group_scope_sources()
        source_map = self.group_scope_sources_by_group
        group_keys = self.group_scope.keys
        if not source_map or len(group_keys) != 1:
            return declared
        selected = source_map.get(group_keys[0])
        if selected is None and group_keys[0] is not None:
            selected = source_map.get(None)
        return declared if selected is None else selected

    def for_group(self, group_key: str | None) -> ArtifactOutputPlan:
        """Return a group-specific output plan with the finalized path."""
        plan = self._plan_for_group(group_key)
        if plan is None:
            raise RuntimeError("ArtifactOutputPlan group resolution must be total.")
        return plan

    def for_invocation_group(
        self,
        group_key: str | None,
    ) -> ArtifactOutputPlan:
        """Resolve storage scope from the invocation or this exact output plan."""

        scope = self.group_scope
        return self.for_group(
            scope.select_runtime_key(None)
            if group_key is None
            else scope.resolve_runtime_key(group_key)
        )

    def for_execution_scope(
        self,
        execution_scope: ComponentGroupScope,
        component_key: str | None,
    ) -> ArtifactOutputPlan | None:
        """Project this output into one compiled component execution."""

        output_scope = self.group_scope
        for grouped in output_scope.as_grouped():
            if execution_scope.groups_by(grouped.component):
                if grouped.contains_runtime_key(component_key):
                    return self.for_group(grouped.resolve_runtime_key(component_key))
                return None
        single_key = output_scope.single_key()
        if single_key is not None:
            return self.for_group(single_key)
        return self


@dataclass(frozen=True)
class ArtifactInputPlan(ArtifactPlan):
    """Producer-owned storage plan for one consumed artifact."""

    plan_role: ClassVar[str] = "input"

    source_step_id: int | str | None = None
    source_step_scope_id: str | None = None

    def for_group(self, group_key: str | None) -> ArtifactInputPlan | None:
        """Return a group-specific input plan, or None if not available."""
        return self._plan_for_group(group_key)

    def composes_producer_groups(
        self,
        consumer_variable_components: ComponentSet,
    ) -> bool:
        """Return whether this consumer reconstructs the producer group axis."""

        return self.group_scope.component in consumer_variable_components

    def retains_producer_stack(
        self,
        consumer_variable_components: ComponentSet,
    ) -> bool:
        """Return whether the producer's third axis remains the consumer stack."""

        return (
            bool(self.variable_components)
            and bool(consumer_variable_components)
            and not self.composes_producer_groups(consumer_variable_components)
        )

    def runtime_variable_components(
        self,
        consumer_variable_components: ComponentSet,
    ) -> ComponentSet:
        """Return axes present after this input is reconstructed for a consumer."""

        if self.composes_producer_groups(consumer_variable_components):
            return ComponentSet((self.group_scope.component,))
        if self.retains_producer_stack(consumer_variable_components):
            return consumer_variable_components
        return ComponentSet()

    def runtime_query_snapshot(self) -> Self:
        """Own a point-in-time producer address without retaining mutable maps."""

        paths_by_group = self.paths_by_group
        if paths_by_group is not None:
            paths_by_group = MappingProxyType(dict(paths_by_group))
        return replace(self, paths_by_group=paths_by_group)

    def path_for_runtime_query(self, group_key: str | None) -> str:
        """Return the persisted input path addressed by a runtime query."""
        group_path = self._path_for_group(group_key)
        if group_path is not None:
            return group_path
        return self.path


def grouped_artifact_path(
    base_path: str, group_axis: type[Axis], group_key: str
) -> str:
    """Insert the group's filename token after the partition value in a path."""
    token = group_axis.filename_token(group_key)
    path = Path(base_path)
    filename = path.name
    if "_" not in filename:
        return str(path.with_name(f"{path.stem}_{token}{path.suffix}"))
    axis_id, rest = filename.split("_", 1)
    return str(path.parent / f"{axis_id}_{token}_{rest}")
