"""Artifact declarations: what a callable produces and consumes.

An ``ArtifactSpec`` is one declared artifact term. Its enclosing declaration
binds its plan role (input or output); the compiler turns it into a plan.
"""

from __future__ import annotations

from collections import OrderedDict
from collections.abc import Iterable, Sequence
from dataclasses import dataclass, field, replace
from typing import TYPE_CHECKING, Self, TypeVar

from openhcs.core.artifacts.kinds import (
    ArtifactType,
    ArtifactTypeValue,
    MeasurementsArtifactType,
)
from openhcs.core.artifacts.payloads import ArtifactMaterializationPayload
from openhcs.core.artifacts.plans import (
    ArtifactInputPlan,
    ArtifactOutputPlan,
    ArtifactPlan,
    ArtifactSpecRef,
    DeclaredRelations,
    require_plan_type,
    require_registered_plan_type,
)
from openhcs.core.artifacts.relations import (
    ArtifactGroupScopeSourceRelation,
    ArtifactSpecRelation,
    AssembledStackGroupLineageSourceRelation,
    GroupLineageSourceRelation,
    SourceStackLineageSourceRelation,
)
from openhcs.core.artifacts.sidecars import ArtifactSidecarRole
from openhcs.core.artifacts.streaming import AutomaticStreaming, ViewerStreaming

if TYPE_CHECKING:
    from openhcs.core.runtime_measurements import RuntimeMeasurementFeatureOwner

MergedT = TypeVar("MergedT")


@dataclass(frozen=True)
class ArtifactSpec(DeclaredRelations):
    """Artifact term whose enclosing declaration may bind its plan role."""

    name: str
    artifact_type: type[ArtifactType]
    parameter_name: str | None = field(default=None, compare=False)
    materialization: ArtifactMaterializationPayload | None = None
    viewer_streaming: type[ViewerStreaming] = AutomaticStreaming
    required: bool = True
    sidecar_role: type[ArtifactSidecarRole] | None = None
    relations: tuple[ArtifactSpecRelation, ...] = ()
    plan_type: type[ArtifactPlan] | None = field(default=None, kw_only=True)
    measurement_feature_owner: type[RuntimeMeasurementFeatureOwner] | None = field(
        default=None,
        kw_only=True,
    )

    def binds_callable_parameter(self) -> bool:
        """Distinguish a runtime argument from a context-only artifact identity."""
        return self.parameter_name is not None

    def declares_sidecar(self) -> bool:
        """Whether this declaration is a sidecar of a primary artifact."""
        return self.sidecar_role is not None

    def is_inspection_only(self) -> bool:
        """Whether this is a QA sidecar rather than a processing result."""
        return self.declares_sidecar() and self.sidecar_role.inspection_only

    def __post_init__(self) -> None:
        if self.parameter_name == "":
            raise ValueError("ArtifactSpec.parameter_name cannot be empty.")
        object.__setattr__(
            self,
            "artifact_type",
            ArtifactType.require_registered(
                self.artifact_type,
                "ArtifactSpec.artifact_type",
            ),
        )
        if self.measurement_feature_owner is not None:
            from openhcs.core.runtime_measurements import (
                RuntimeMeasurementFeatureOwner,
            )

            if self.artifact_type is not MeasurementsArtifactType or not issubclass(
                self.measurement_feature_owner,
                RuntimeMeasurementFeatureOwner,
            ):
                raise TypeError(
                    "ArtifactSpec.measurement_feature_owner requires a "
                    "RuntimeMeasurementFeatureOwner type on a measurements artifact."
                )
        if self.plan_type is None:
            return
        object.__setattr__(
            self,
            "plan_type",
            require_registered_plan_type(
                self.plan_type,
                "ArtifactSpec.plan_type",
            ),
        )
        object.__setattr__(
            self,
            "relations",
            tuple(
                dict.fromkeys(
                    relation.bind_target_spec(self) for relation in self.relations
                )
            ),
        )
        for relation in self.relations:
            relation.require_target_spec(self)

    def __hash__(self) -> int:
        # Equal specs share these fields, so hashing them keeps hash and eq
        # consistent without hashing the (possibly mutable) materialization.
        return hash((self.name, self.artifact_type, self.plan_type))

    def require_plan_type(self) -> type[ArtifactPlan]:
        """Return the exact role after its enclosing declaration has bound it."""

        if self.plan_type is None:
            raise ValueError(
                f"ArtifactSpec {self.name!r} has no plan role outside an "
                "artifact input/output declaration."
            )
        return self.plan_type

    def require_measurement_feature_owner(self) -> type[RuntimeMeasurementFeatureOwner]:
        """Require the declared row owner without inferring one from consumers."""
        if self.measurement_feature_owner is None:
            raise ValueError(
                f"Measurement output {self.ref()!r} requires its declared "
                "measurement_feature_owner. Finalize the callable contract "
                "before compiling heterogeneous rows."
            )
        return self.measurement_feature_owner

    def ref(self) -> ArtifactSpecRef:
        """Return the scope-free identity for this declaration."""
        return ArtifactSpecRef(
            plan_type=self.require_plan_type(),
            artifact_type=self.artifact_type,
            name=self.name,
        )

    @property
    def participates_in_main_flow(self) -> bool:
        """Return whether this declaration is part of the main image flow."""
        return self.artifact_type.publishes_to_main_flow(self.sidecar_role)

    def with_group_scope_relation(
        self,
        relation: ArtifactGroupScopeSourceRelation,
    ) -> Self:
        """Replace the relation that sets this declaration's group scope."""

        return replace(
            self,
            relations=(
                *(
                    existing
                    for existing in self.relations
                    if existing.group_scope_source() is None
                ),
                relation,
            ),
        )

    def bind_main_flow_source(self, sources: ArtifactSpecCollection) -> ArtifactSpec:
        """Resolve any declaration-owned dependency on the invocation's image flow."""

        return self

    @classmethod
    def input(
        cls,
        name: str,
        artifact_type: ArtifactTypeValue,
        **kwargs,
    ) -> ArtifactSpec:
        return cls(
            name=name,
            plan_type=ArtifactInputPlan,
            artifact_type=ArtifactType.coerce(artifact_type),
            **kwargs,
        )

    @classmethod
    def output(
        cls,
        name: str,
        artifact_type: ArtifactTypeValue,
        **kwargs,
    ) -> ArtifactSpec:
        return cls(
            name=name,
            plan_type=ArtifactOutputPlan,
            artifact_type=ArtifactType.coerce(artifact_type),
            **kwargs,
        )

    def for_plan_type(self, plan_type: type[ArtifactPlan]) -> ArtifactSpec:
        """Return this declaration with the same payload term under another role."""
        target_plan_type = require_plan_type(plan_type)
        return replace(
            self,
            plan_type=target_plan_type,
            parameter_name=(
                self.parameter_name if target_plan_type is ArtifactInputPlan else None
            ),
            relations=tuple(
                projected
                for relation in self.relations
                for projected in (relation.for_plan_type(target_plan_type),)
                if projected is not None
            ),
        )

    @classmethod
    def output_inheriting_group_scope(
        cls,
        name: str,
        artifact_type: ArtifactTypeValue,
        source: ArtifactSpecRef | ArtifactSpec,
        **kwargs,
    ) -> ArtifactSpec:
        """Declare an output artifact whose group scope follows a source artifact."""
        return cls._output_with_relation(
            name, artifact_type, GroupLineageSourceRelation(source=_ref_of(source)), kwargs
        )

    @classmethod
    def output_preserving_source_stack_scope(
        cls,
        name: str,
        artifact_type: ArtifactTypeValue,
        source: ArtifactSpecRef | ArtifactSpec,
        **kwargs,
    ) -> ArtifactSpec:
        """Declare an output artifact that remains compatible with the source stack."""
        return cls._output_with_relation(
            name,
            artifact_type,
            SourceStackLineageSourceRelation(source=_ref_of(source)),
            kwargs,
        )

    @classmethod
    def _output_with_relation(
        cls,
        name: str,
        artifact_type: ArtifactTypeValue,
        relation: ArtifactSpecRelation,
        kwargs: dict[str, object],
    ) -> ArtifactSpec:
        relations = tuple(kwargs.pop("relations", ()))
        return cls.output(
            name,
            artifact_type,
            relations=(*relations, relation),
            **kwargs,
        )

    def materialization_uses_source_identity_filename(self) -> bool:
        """Return whether this spec's materialized files require source identity."""
        return (
            self.materialization is not None
            and self.materialization.uses_source_identity_filename()
        )

    def participates_in_group_scope_sources(
        self,
        active_sources: Iterable[ArtifactSpecRef],
    ) -> bool:
        """Return whether this declaration participates in a source projection."""

        declared_sources = frozenset(self.group_scope_sources())
        return not declared_sources or not declared_sources.isdisjoint(active_sources)

    def preserves_source_stack_scope(self) -> bool:
        """Return whether this output retains a declared source stack axis."""

        return bool(self.source_stack_scope_sources())

    def source_stack_scope_identity(self) -> ArtifactSpecRef:
        """Return the single input-role identity owning this artifact's stack."""

        sources = self.source_stack_scope_sources()
        if len(sources) > 1:
            raise ValueError(
                f"Artifact {self.ref()!r} preserves multiple source stacks "
                f"{sources!r}; no singular stack identity exists."
            )
        return (sources[0] if sources else self.ref()).for_plan_type(ArtifactInputPlan)


def _ref_of(source: ArtifactSpecRef | ArtifactSpec) -> ArtifactSpecRef:
    """Return the identity of a declaration, or an identity unchanged."""
    return source.ref() if isinstance(source, ArtifactSpec) else source


class MainFlowStackOutputSpec(ArtifactSpec):
    """An output retaining the invocation's source-stack axes and provenance."""

    def bind_main_flow_source(self, sources: ArtifactSpecCollection) -> ArtifactSpec:
        if not sources:
            return self
        if len(sources) != 1:
            raise ValueError(
                f"Output {self.name!r} requires one compiled main-flow source, "
                f"got {sources.names()!r}."
            )
        return self.with_group_scope_relation(
            SourceStackLineageSourceRelation(source=sources[0].ref())
        )


class MainFlowPlaneProjectionOutputSpec(ArtifactSpec):
    """An explicit plane projection from the invocation's assembled image stack."""

    def bind_main_flow_source(self, sources: ArtifactSpecCollection) -> ArtifactSpec:
        if not sources:
            return self
        declared_sources = frozenset(self.group_scope_sources())
        new_relations = tuple(
            AssembledStackGroupLineageSourceRelation(source=source.ref())
            for source in sources
            if source.ref() not in declared_sources
        )
        if not new_relations:
            return self
        return replace(self, relations=(*self.relations, *new_relations))


@dataclass(frozen=True, slots=True)
class ArtifactSpecAccumulator:
    """Ordered merge of artifact specs for one producer or consumer role."""

    role: str
    specs: OrderedDict[ArtifactSpecRef, ArtifactSpec]

    @classmethod
    def empty(cls, role: str) -> ArtifactSpecAccumulator:
        """Create an empty ordered accumulator for an artifact role."""
        return cls(role=role, specs=OrderedDict())

    def add(self, incoming: ArtifactSpec) -> None:
        """Merge an incoming spec into this accumulator."""
        ref = incoming.ref()
        if ref not in self.specs:
            self.specs[ref] = incoming
            return
        self.specs[ref] = self.merge_existing(
            existing=self.specs[ref],
            incoming=incoming,
        )

    def _merged(
        self,
        existing: MergedT | None,
        incoming: MergedT | None,
        *,
        what: str,
        name: str,
    ) -> MergedT | None:
        """Keep whichever side declares a value; two different values conflict."""
        if existing is None:
            return incoming
        if incoming is None or incoming == existing:
            return existing
        raise ValueError(f"Conflicting {self.role} artifact {what} for '{name}'.")

    def merge_existing(
        self,
        *,
        existing: ArtifactSpec,
        incoming: ArtifactSpec,
    ) -> ArtifactSpec:
        """Merge two declarations for the same exact artifact reference."""
        if existing.ref() != incoming.ref():
            raise ValueError(
                f"Cannot merge distinct {self.role} artifact refs: "
                f"{existing.ref()!r} and {incoming.ref()!r}."
            )
        name = incoming.name
        return replace(
            existing,
            materialization=self._merged(
                existing.materialization,
                incoming.materialization,
                what="materialization",
                name=name,
            ),
            required=existing.required or incoming.required,
            sidecar_role=self._merged(
                existing.sidecar_role,
                incoming.sidecar_role,
                what="sidecar role",
                name=name,
            ),
            relations=tuple(dict.fromkeys((*existing.relations, *incoming.relations))),
            measurement_feature_owner=self._merged(
                existing.measurement_feature_owner,
                incoming.measurement_feature_owner,
                what="measurement feature owner",
                name=name,
            ),
        )


@dataclass(frozen=True, slots=True)
class ArtifactSpecCollection(Sequence[ArtifactSpec]):
    """Ordered query surface over declared artifact specs."""

    specs: tuple[ArtifactSpec, ...]

    def __init__(self, specs: Iterable[ArtifactSpec]):
        object.__setattr__(self, "specs", tuple(specs))

    def __len__(self) -> int:
        return len(self.specs)

    def __iter__(self):
        return iter(self.specs)

    def __getitem__(self, index):
        return self.specs[index]

    def stack_broadcast_source_indices(self) -> tuple[int | None, ...]:
        """Resolve exact stack-broadcast sources from declared input relations."""

        indices_by_ref: dict[ArtifactSpecRef, list[int]] = {}
        for input_index, spec in enumerate(self.specs):
            indices_by_ref.setdefault(spec.ref(), []).append(input_index)

        result: list[int | None] = []
        for input_index, spec in enumerate(self.specs):
            sources = spec.stack_broadcast_sources()
            if len(sources) > 1:
                raise ValueError(
                    f"Input {spec.ref()!r} declares multiple stack-broadcast "
                    f"sources: {sources!r}."
                )
            if not sources:
                result.append(None)
                continue
            source_indices = tuple(indices_by_ref.get(sources[0], ()))
            if len(source_indices) != 1:
                raise ValueError(
                    f"Input {spec.ref()!r} requires exactly one active occurrence "
                    f"of stack-broadcast source {sources[0]!r}, got "
                    f"{source_indices!r}."
                )
            source_index = source_indices[0]
            if source_index == input_index:
                raise ValueError(f"Input {spec.ref()!r} cannot broadcast from itself.")
            result.append(source_index)
        return tuple(result)

    def of_artifact_type(
        self,
        artifact_type: ArtifactTypeValue,
    ) -> tuple[ArtifactSpec, ...]:
        """Return specs with the requested artifact type, preserving order."""
        resolved_artifact_type = ArtifactType.coerce(artifact_type)
        return tuple(
            spec for spec in self.specs if spec.artifact_type is resolved_artifact_type
        )

    def for_plan_type(
        self,
        plan_type: type[ArtifactPlan],
    ) -> ArtifactSpecCollection:
        """Return specs with the requested artifact plan role."""
        resolved_plan_type = require_plan_type(plan_type)
        return ArtifactSpecCollection(
            spec for spec in self.specs if spec.plan_type is resolved_plan_type
        )

    def names_for_plan_type(
        self,
        plan_type: type[ArtifactPlan],
    ) -> tuple[str, ...]:
        """Return names for specs with the requested artifact plan role."""
        return self.for_plan_type(plan_type).names()

    def for_artifact_type(
        self,
        artifact_type: ArtifactTypeValue,
    ) -> ArtifactSpecCollection:
        """Return specs with the requested artifact type."""
        return ArtifactSpecCollection(self.of_artifact_type(artifact_type))

    def names(self) -> tuple[str, ...]:
        """Return artifact names in collection order."""
        return tuple(spec.name for spec in self.specs)

    def name_set(self) -> frozenset[str]:
        """Return artifact names as a set."""
        return frozenset(self.names())

    def names_of_artifact_type(
        self,
        artifact_type: ArtifactTypeValue,
    ) -> tuple[str, ...]:
        """Return names for specs with the requested artifact type."""
        return ArtifactSpecCollection(self.of_artifact_type(artifact_type)).names()

    def name_set_of_artifact_type(
        self,
        artifact_type: ArtifactTypeValue,
    ) -> frozenset[str]:
        """Return names for specs with the requested artifact type as a set."""
        return frozenset(self.names_of_artifact_type(artifact_type))

    def by_name(self, name: str) -> ArtifactSpec | None:
        """Return the first spec with a matching artifact name."""
        for spec in self.specs:
            if spec.name == name:
                return spec
        return None

    def by_name_and_artifact_type(
        self,
        name: str,
        artifact_type: ArtifactTypeValue,
    ) -> ArtifactSpec | None:
        """Return the one semantic artifact matching name and type."""
        resolved_artifact_type = ArtifactType.coerce(artifact_type)
        matches = tuple(
            spec
            for spec in self.specs
            if spec.name == name and spec.artifact_type is resolved_artifact_type
        )
        if not matches:
            return None
        first = matches[0]
        if any(spec != first for spec in matches[1:]):
            raise ValueError(
                f"Conflicting active {resolved_artifact_type.value} "
                f"artifact declarations are named {name!r}: {matches!r}."
            )
        return first

    def require_by_name_and_artifact_type(
        self,
        name: str,
        artifact_type: ArtifactTypeValue,
    ) -> ArtifactSpec:
        """Return the declared artifact with this identity or fail."""

        resolved_artifact_type = ArtifactType.coerce(artifact_type)
        spec = self.by_name_and_artifact_type(name, resolved_artifact_type)
        if spec is None:
            raise ValueError(
                f"No {resolved_artifact_type.value} artifact named "
                f"{name!r} is declared."
            )
        return spec

    def ref_set(self) -> frozenset[ArtifactSpecRef]:
        """Return full declared artifact references."""
        return frozenset(spec.ref() for spec in self.specs)

    def select_refs(
        self,
        refs: Iterable[ArtifactSpecRef],
    ) -> ArtifactSpecCollection:
        """Select exact declared identities while preserving declaration order."""

        selected_refs = tuple(refs)
        if len(frozenset(selected_refs)) != len(selected_refs):
            raise ValueError(
                "ArtifactSpecCollection.select_refs does not accept duplicate "
                f"identities: {selected_refs!r}."
            )
        selected_ref_set = frozenset(selected_refs)
        selected = ArtifactSpecCollection(
            spec for spec in self.specs if spec.ref() in selected_ref_set
        )
        resolved_refs = tuple(spec.ref() for spec in selected)
        if len(resolved_refs) != len(selected_refs):
            missing = tuple(ref for ref in selected_refs if ref not in resolved_refs)
            duplicate_declarations = tuple(
                ref for ref in selected_refs if resolved_refs.count(ref) > 1
            )
            raise ValueError(
                "Selected artifact identities must resolve to one exact declared "
                "occurrence: "
                f"missing={missing!r}, duplicate_declarations="
                f"{duplicate_declarations!r}."
            )
        return selected

    def rebind(self, replacements: Iterable[ArtifactSpec]) -> ArtifactSpecCollection:
        """Replace active artifact bindings while preserving declaration order."""

        replacement_specs = tuple(replacements)
        replacement_refs = tuple(
            spec.ref().for_plan_type(ArtifactInputPlan) for spec in replacement_specs
        )
        if len(set(replacement_refs)) != len(replacement_refs):
            raise ValueError(
                "Artifact replacements contain duplicate active identities: "
                f"{replacement_refs!r}."
            )
        replaced = frozenset(replacement_refs)
        return ArtifactSpecCollection(
            (
                *(
                    spec
                    for spec in self.specs
                    if spec.ref().for_plan_type(ArtifactInputPlan) not in replaced
                ),
                *replacement_specs,
            )
        )

    def by_ref(self, ref: ArtifactSpecRef) -> ArtifactSpec | None:
        """Return one spec by full artifact reference."""
        matches = tuple(spec for spec in self.specs if spec.ref() == ref)
        if not matches:
            return None
        first = matches[0]
        if any(spec != first for spec in matches[1:]):
            raise ValueError(
                f"Conflicting artifact declarations for exact ref {ref!r}: {matches!r}."
            )
        return first

    def relation_refs(
        self,
        relation_type: type[ArtifactSpecRelation],
    ) -> tuple[tuple[ArtifactSpec, ArtifactSpecRelation], ...]:
        """Return specs and relation tags of the requested relation family."""
        return tuple(
            (spec, relation)
            for spec in self.specs
            for relation in spec.relations
            if isinstance(relation, relation_type)
        )

    def validate_registered_relation_refs(
        self,
        *,
        owner_name: str,
        relation_specs: Iterable[ArtifactSpec] | None = None,
    ) -> None:
        """Validate relations owned by selected specs against this collection."""

        owners = self.specs if relation_specs is None else tuple(relation_specs)
        refs = self.ref_set()
        unknown = tuple(
            relation.source
            for spec in owners
            for relation in spec.relations
            if relation.source not in refs
        )
        if unknown:
            raise ValueError(
                f"{owner_name} declares artifact relation references to unknown "
                f"artifact specs: {unknown!r}."
            )

    def unique(
        self, *, conflict_context: str = "artifact spec"
    ) -> tuple[ArtifactSpec, ...]:
        """Return specs de-duplicated by artifact identity, failing on conflicts."""
        unique_specs: dict[ArtifactSpecRef, ArtifactSpec] = {}
        for spec in self.specs:
            key = spec.ref()
            if key in unique_specs and (
                unique_specs[key] != spec
                or unique_specs[key].parameter_name != spec.parameter_name
            ):
                raise ValueError(
                    f"Conflicting {conflict_context} declarations for "
                    f"{spec.require_plan_type().plan_role}:"
                    f"{spec.artifact_type.value}:{spec.name}."
                )
            unique_specs[key] = spec
        return tuple(unique_specs.values())

    def select_declared_occurrences(
        self,
        selected_specs: Iterable[ArtifactSpec],
    ) -> ArtifactSpecCollection:
        """Select exact occurrences while preserving declaration order."""

        remaining = list(selected_specs)
        selected: list[ArtifactSpec] = []
        for declared in self.specs:
            matching_index = next(
                (
                    index
                    for index, candidate in enumerate(remaining)
                    if candidate.ref() == declared.ref()
                ),
                None,
            )
            if matching_index is None:
                continue
            candidate = remaining.pop(matching_index)
            if (
                candidate != declared
                or candidate.parameter_name != declared.parameter_name
            ):
                raise ValueError(
                    "Selected artifact spec drifts from its declared occurrence: "
                    f"selected {candidate!r}, declared {declared!r}."
                )
            selected.append(declared)
        if remaining:
            raise ValueError(
                "Selected artifact specs are not declared with sufficient "
                f"occurrence cardinality: {tuple(remaining)!r}."
            )
        return ArtifactSpecCollection(selected)
