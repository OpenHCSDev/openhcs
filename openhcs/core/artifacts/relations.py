"""Relations a declared artifact has to the artifacts it depends on.

Each relation class declares, in its own body, which artifacts may be its
source and which declarations may carry it; the base class checks both.
"""

from __future__ import annotations

import json
from abc import ABC
from collections.abc import Mapping
from dataclasses import dataclass, field, replace
from typing import TYPE_CHECKING, ClassVar

from metaclass_registry import AutoRegisterMeta

from openhcs.core.artifacts.kinds import (
    ArtifactType,
    ImageArtifactType,
    MeasurementsArtifactType,
    ObjectLabelsArtifactType,
)
from openhcs.core.artifacts.plans import (
    ArtifactInputPlan,
    ArtifactOutputPlan,
    ArtifactPlan,
    ArtifactSpecRef,
)
from openhcs.core.component_group_scope import ComponentGroupScope

if TYPE_CHECKING:
    from openhcs.core.artifacts.specs import ArtifactSpec
    from openhcs.core.runtime_measurements import MeasurementSubject


@dataclass(frozen=True)
class ObjectArtifactSubjectBinding:
    """Bind one artifact-local identity field to an exact object subject."""

    SUBJECT_FEATURE: ClassVar[str] = "__openhcs_object_subject__"
    SUBJECT_ID_FEATURE: ClassVar[str] = "__openhcs_object_subject_id__"

    source: ArtifactSpecRef
    id_field: str

    def __post_init__(self) -> None:
        if self.source.artifact_type is not ObjectLabelsArtifactType:
            raise ValueError(
                "ObjectArtifactSubjectBinding requires an ObjectLabels source, got "
                f"{self.source.artifact_type.value}:{self.source.name}."
            )
        if not self.id_field:
            raise ValueError("ObjectArtifactSubjectBinding.id_field cannot be empty.")

    def subject_token(
        self,
        *,
        producer_step_scope_id: str | None,
        producer_step_index: int | str | None,
    ) -> str:
        """Return one scalar token shared by sibling outputs from this producer."""

        return json.dumps(
            (
                self.source.plan_type.plan_role,
                self.source.artifact_type.value,
                self.source.name,
                producer_step_scope_id,
                producer_step_index,
            ),
            separators=(",", ":"),
        )

    def feature_metadata(
        self,
        features: Mapping[str, object],
        *,
        producer_step_scope_id: str | None,
        producer_step_index: int | str | None,
    ) -> dict[str, object]:
        """Project the declared local member identity to framework metadata."""

        if self.id_field not in features:
            raise ValueError(
                f"Declared object-subject field {self.id_field!r} is absent from "
                f"artifact member features {tuple(features)!r}."
            )
        return {
            self.SUBJECT_FEATURE: self.subject_token(
                producer_step_scope_id=producer_step_scope_id,
                producer_step_index=producer_step_index,
            ),
            self.SUBJECT_ID_FEATURE: features[self.id_field],
        }


@dataclass(frozen=True)
class ArtifactSpecRelation(ABC, metaclass=AutoRegisterMeta):
    """Declare a semantic dependency on one source artifact.

    Specialized relations add projection or materialization behavior; the root
    relation preserves dependency provenance without changing runtime scope.
    """

    __registry_key__ = "relation_key"
    __skip_if_no_key__ = True

    relation_key: ClassVar[str]
    source_plan_type: ClassVar[type[ArtifactPlan]] = ArtifactPlan
    """The plan role the source artifact must be declared in."""
    source_artifact_type: ClassVar[type[ArtifactType]] = ArtifactType
    """The kind the source artifact must be."""
    target_plan_type: ClassVar[type[ArtifactPlan]] = ArtifactOutputPlan
    """The plan role of the declarations that may carry this relation
    (``ArtifactPlan`` itself: every role)."""
    target_artifact_type: ClassVar[type[ArtifactType]] = ArtifactType
    """The kind of the declarations that may carry this relation."""

    source: ArtifactSpecRef

    def __post_init__(self) -> None:
        self.require_source()

    def require_source(self) -> None:
        """Require the source this relation class declares."""
        if issubclass(self.source.plan_type, self.source_plan_type) and issubclass(
            self.source.artifact_type, self.source_artifact_type
        ):
            return
        raise ValueError(
            f"{type(self).__name__} requires an {self.source_plan_type.__name__} source "
            f"of kind {self.source_artifact_type.__name__}, got {self.source!r}."
        )

    def require_target_spec(self, spec: ArtifactSpec) -> None:
        actual_plan_type = spec.require_plan_type()
        if not issubclass(actual_plan_type, self.target_plan_type):
            raise ValueError(
                f"{type(self).__name__} requires target plan role "
                f"{self.target_plan_type.plan_role}, got {actual_plan_type.plan_role}."
            )
        if issubclass(spec.artifact_type, self.target_artifact_type):
            return
        raise ValueError(
            f"{type(self).__name__} requires target artifact type "
            f"{self.target_artifact_type.__name__}, got {spec.artifact_type.value}."
        )

    def bind_target_spec(self, spec: ArtifactSpec) -> ArtifactSpecRelation:
        """Bind target-owned relation state before validating the declaration."""

        del spec
        return self

    def group_scope_source(self) -> ArtifactSpecRef | None:
        """Return the source whose component group this relation propagates."""

        return None

    def materialization_source(self) -> ArtifactSpecRef | None:
        """Return the source whose identity names materialized output files."""

        return None

    def source_context_source(self) -> ArtifactSpecRef | None:
        """Return the source whose runtime context belongs to the target artifact."""

        return None

    def source_stack_scope_source(self) -> ArtifactSpecRef | None:
        """Return the source whose complete runtime stack the target preserves."""

        return None

    def measurement_subject(self) -> MeasurementSubject | None:
        """Return the exact measurement subject declared by this relation."""

        return None

    def object_subject_binding(self) -> ObjectArtifactSubjectBinding | None:
        """Return the target-local identity bound to one object subject."""

        return None

    def stack_broadcast_source(self) -> ArtifactSpecRef | None:
        """Return the source whose runtime stack may broadcast this input."""

        return None

    def input_producer_selection_scope(
        self, producer_scope: ComponentGroupScope
    ) -> ComponentGroupScope | None:
        """Return an explicitly declared producer domain for an input edge."""

        return None

    def dependency_refs(self) -> tuple[ArtifactSpecRef, ...]:
        """Return every artifact that must exist before the relation target."""

        return (self.source,)

    def for_plan_type(
        self,
        plan_type: type[ArtifactPlan],
    ) -> ArtifactSpecRelation | None:
        """Return this relation under another plan role, if it applies there."""

        if issubclass(plan_type, self.target_plan_type):
            return self
        return None


class ArtifactSidecarSourceRelation(ArtifactSpecRelation):
    """Declare the primary artifact whose identity selects one sidecar."""

    relation_key: ClassVar[str] = "artifact_sidecar_source"

    def bind_target_spec(self, spec: ArtifactSpec) -> ArtifactSpecRelation:
        if spec.declares_sidecar():
            return self
        raise ValueError(f"{type(self).__name__} requires an artifact sidecar target.")


class ArtifactSourceContextSourceRelation(ArtifactSpecRelation, ABC):
    """Target artifact preserves runtime source context from a declared source."""

    def source_context_source(self) -> ArtifactSpecRef:
        """Return the artifact that supplies the target's runtime context."""

        return self.source


class ArtifactGroupScopeSourceRelation(ArtifactSourceContextSourceRelation, ABC):
    """Target artifact inherits group scope from a declared source artifact."""

    def group_scope_source(self) -> ArtifactSpecRef:
        """Return this relation's declared group-scope source."""

        return self.source


class GroupLineageSourceRelation(ArtifactGroupScopeSourceRelation):
    """Target artifact inherits grouping from a declared source artifact."""

    relation_key: ClassVar[str] = "group_lineage_source"


class SourceStackLineageSourceRelation(GroupLineageSourceRelation):
    """Target artifact preserves source-stack compatibility with a source artifact."""

    relation_key: ClassVar[str] = "source_stack_lineage_source"

    def source_stack_scope_source(self) -> ArtifactSpecRef:
        """Return the source whose complete runtime stack is preserved."""

        return self.source


class InputGroupLineageSourceRelation(ArtifactGroupScopeSourceRelation):
    """Input artifact inherits invocation grouping from a declared input source."""

    relation_key: ClassVar[str] = "input_group_lineage_source"
    target_plan_type = ArtifactInputPlan


class InputImageSetContextSourceRelation(ArtifactSourceContextSourceRelation):
    """Consume an artifact in the image-set context of a declared input image."""

    relation_key: ClassVar[str] = "input_image_set_context_source"
    source_plan_type = ArtifactInputPlan
    source_artifact_type = ImageArtifactType
    target_plan_type = ArtifactInputPlan

    def require_target_spec(self, spec: ArtifactSpec) -> None:
        super().require_target_spec(spec)
        if spec.artifact_type.carries_source_image_context:
            return
        raise ValueError(
            f"{type(self).__name__} requires a target carrying source-image "
            f"context, got {spec.artifact_type.value!r}."
        )


class InputStackBroadcastSourceRelation(ArtifactSourceContextSourceRelation):
    """Input artifact may broadcast across one declared source input stack."""

    relation_key: ClassVar[str] = "input_stack_broadcast_source"
    source_artifact_type = ImageArtifactType
    target_plan_type = ArtifactInputPlan
    target_artifact_type = ImageArtifactType

    def stack_broadcast_source(self) -> ArtifactSpecRef:
        """Return the exact input whose runtime stack owns broadcast cardinality."""

        return self.source


class AssembledStackGroupLineageSourceRelation(ArtifactSpecRelation):
    """Declare one contributor to an assembled stack output's group scope.

    The runtime projected-image payload owns exact source-plane context. This
    relation therefore carries grouping only; it does not manufacture a single
    source-context owner for an output assembled from multiple image inputs.
    """

    relation_key: ClassVar[str] = "assembled_stack_group_lineage_source"

    def group_scope_source(self) -> ArtifactSpecRef:
        """Return one compiled main-flow contributor to the output group."""

        return self.source


class MaterializationSourceIdentityRelation(ArtifactSpecRelation):
    """Materialized output filenames inherit one declared source identity."""

    relation_key: ClassVar[str] = "materialization_source_identity"
    target_artifact_type = ImageArtifactType

    def materialization_source(self) -> ArtifactSpecRef:
        """Return the exact source artifact used for materialized filenames."""

        return self.source


@dataclass(frozen=True)
class ObjectMeasurementSubjectRelation(ArtifactSpecRelation):
    """Object-scoped measurements are owned by one ObjectLabels artifact."""

    relation_key: ClassVar[str] = "object_measurement_subject"
    source_artifact_type: ClassVar[type[ArtifactType]] = ObjectLabelsArtifactType
    target_artifact_type: ClassVar[type[ArtifactType]] = MeasurementsArtifactType
    id_field: str | None = None

    def measurement_subject(self) -> MeasurementSubject:
        from openhcs.core.runtime_measurements import (
            MeasurementScope,
            MeasurementSubject,
        )

        return MeasurementSubject(
            MeasurementScope.OBJECT,
            self.source.name,
            self.id_field,
        )

    def object_subject_binding(self) -> ObjectArtifactSubjectBinding | None:
        """Expose an explicit measurement-row identity for generic UI linkage."""

        if self.id_field is None:
            return None
        return ObjectArtifactSubjectBinding(self.source, self.id_field)


class InputObjectMeasurementSourceRelation(ObjectMeasurementSubjectRelation):
    """Consume all prior producer groups measuring the declared object source."""

    relation_key: ClassVar[str] = "input_object_measurement_source"
    target_plan_type = ArtifactInputPlan

    def matches_output(self, output: ArtifactSpec) -> bool:
        """Accept a measurement producer declared against this exact object source."""

        return (
            output.plan_type is ArtifactOutputPlan
            and output.artifact_type is MeasurementsArtifactType
            and any(relation.source == self.source for relation in output.relations)
        )

    def input_spec_for_output(self, output: ArtifactSpec) -> ArtifactSpec:
        """Bind the producer's declaration as this input, with its consumed subject."""

        if not self.matches_output(output):
            raise ValueError(
                f"Artifact output {output.ref()!r} does not measure declared "
                f"object source {self.source!r}."
            )
        input_spec = output.for_plan_type(ArtifactInputPlan)
        return replace(input_spec, relations=(*input_spec.relations, self))

    def input_producer_selection_scope(
        self, producer_scope: ComponentGroupScope
    ) -> ComponentGroupScope:
        """Object measurements retain their channels independently of the child."""

        return producer_scope


@dataclass(frozen=True)
class ObjectArtifactMemberSubjectRelation(ArtifactSpecRelation):
    """Artifact members are owned by objects through one declared local field."""

    relation_key: ClassVar[str] = "object_artifact_member_subject"
    source_artifact_type: ClassVar[type[ArtifactType]] = ObjectLabelsArtifactType
    source: ArtifactSpecRef | None = None
    member_id_field: str = "label"
    self_owned: bool = field(default=False, compare=False, repr=False)

    def __post_init__(self) -> None:
        if not self.member_id_field:
            raise ValueError(
                "ObjectArtifactMemberSubjectRelation.member_id_field cannot be empty."
            )
        if self.source is not None:
            self.require_source()

    def bind_target_spec(self, spec: ArtifactSpec) -> ArtifactSpecRelation:
        """Bind a source-less declaration to its owning ObjectLabels output."""

        if self.source is not None:
            return self
        if spec.artifact_type is not ObjectLabelsArtifactType:
            raise ValueError(
                f"{type(self).__name__} without an explicit source requires an "
                f"ObjectLabels target, got {spec.artifact_type.value}:{spec.name}."
            )
        return replace(self, source=spec.ref(), self_owned=True)

    def object_subject_binding(self) -> ObjectArtifactSubjectBinding:
        """Return the exact object subject and target-local member identity."""

        if self.source is None:
            raise RuntimeError(
                "ObjectArtifactMemberSubjectRelation must be bound to a target spec."
            )
        return ObjectArtifactSubjectBinding(self.source, self.member_id_field)

    def dependency_refs(self) -> tuple[ArtifactSpecRef, ...]:
        """A self-owned ObjectLabels member relation adds no dependency edge."""

        if self.source is None or self.self_owned:
            return ()
        return super().dependency_refs()


class ImageMeasurementSubjectRelation(ArtifactSpecRelation):
    """Image-scoped measurements are owned by one image artifact."""

    relation_key: ClassVar[str] = "image_measurement_subject"
    source_artifact_type = ImageArtifactType
    target_artifact_type = MeasurementsArtifactType

    def measurement_subject(self) -> MeasurementSubject:
        from openhcs.core.runtime_measurements import (
            MeasurementScope,
            MeasurementSubject,
        )

        return MeasurementSubject(MeasurementScope.SAMPLE, self.source.name)


@dataclass(frozen=True)
class ArtifactMeasurementSubjectRelation(ArtifactSpecRelation):
    """Artifact-scoped measurements are owned by the measurement output itself."""

    relation_key: ClassVar[str] = "artifact_measurement_subject"
    source_artifact_type: ClassVar[type[ArtifactType]] = MeasurementsArtifactType
    target_artifact_type: ClassVar[type[ArtifactType]] = MeasurementsArtifactType
    source: ArtifactSpecRef | None = None

    def __post_init__(self) -> None:
        if self.source is not None:
            self.require_source()

    def bind_target_spec(self, spec: ArtifactSpec) -> ArtifactSpecRelation:
        """Bind this self-subject relation to its exact target output."""

        target_ref = spec.ref()
        if self.source is None:
            return replace(self, source=target_ref)
        if self.source != target_ref:
            raise ValueError(
                f"{type(self).__name__} must reference its target output "
                f"{target_ref!r}, got {self.source!r}."
            )
        return self

    def measurement_subject(self) -> MeasurementSubject:
        from openhcs.core.runtime_measurements import (
            MeasurementScope,
            MeasurementSubject,
        )

        return MeasurementSubject(MeasurementScope.ARTIFACT)

    def dependency_refs(self) -> tuple[ArtifactSpecRef, ...]:
        """Self-subject declaration does not introduce an external dependency."""

        return ()
