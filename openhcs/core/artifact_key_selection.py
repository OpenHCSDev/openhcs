"""Nominal artifact-plan key selection shared by compiler declarations."""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Mapping
from typing import TYPE_CHECKING, ClassVar, TypeVar

from openhcs.core.artifacts import (
    ArtifactOutputPlan,
    ArtifactPlan,
    ArtifactSpec,
    ArtifactSpecCollection,
    ArtifactSpecRef,
    MeasurementsArtifactType,
)

ArtifactPlanT = TypeVar("ArtifactPlanT", bound=ArtifactPlan)

if TYPE_CHECKING:
    from openhcs.core.callable_contract import CallableContract


class ArtifactOutputPolicy(ABC):
    """Declaration-owned recording and payload obligations for output artifacts."""

    records_outputs: ClassVar[bool]

    @classmethod
    def preserves_input_main_flow(cls, contract: CallableContract) -> bool:
        """Derive native return behavior from the declared output roster."""
        return bool(contract.artifact_outputs) and not contract.main_flow_outputs

    @classmethod
    def validate_output_declarations(cls, specs: ArtifactSpecCollection) -> None:
        """Run common kind invariants before the ownership-specific obligation."""

        for spec in specs.for_plan_type(ArtifactOutputPlan):
            spec.artifact_type.validate_output_declaration(spec)
            cls.validate_payload_declaration(spec)

    @classmethod
    @abstractmethod
    def validate_payload_declaration(cls, spec: ArtifactSpec) -> None:
        """Validate what this owner needs to turn the declaration into a payload."""


class NativeReturnArtifactOutputPolicy(ArtifactOutputPolicy):
    """Returned payloads are normalized and recorded by the native runtime."""

    records_outputs = False

    @classmethod
    def validate_payload_declaration(cls, spec: ArtifactSpec) -> None:
        spec.artifact_type.validate_native_output_declaration(spec)


class AdapterRecordedArtifactOutputPolicy(ArtifactOutputPolicy):
    """The declared adapter records payloads without bypassing kind invariants."""

    records_outputs = True

    @classmethod
    def validate_payload_declaration(cls, spec: ArtifactSpec) -> None:
        spec.artifact_type.validate_recorded_output_declaration(spec, cls)

    @classmethod
    def validate_measurement_subject(cls, spec: ArtifactSpec) -> None:
        """Ordinary recorded tables have one declaration-owned subject."""

        MeasurementsArtifactType.require_output_subject(spec)


class ArtifactPlanKeySelector(ABC):
    """Nominal interface for declarations that select compiled artifact plans."""

    @property
    @abstractmethod
    def artifact_specs(self) -> ArtifactSpecCollection:
        """All artifact specs declared by this owner."""

    @property
    def artifact_key_specs(self) -> ArtifactSpecCollection:
        """Artifact specs that participate in compiled plan-key selection."""
        return self.artifact_specs

    def select_plans(
        self,
        plan_type: type[ArtifactPlanT],
        plans: Mapping[ArtifactSpecRef, ArtifactPlanT],
    ) -> tuple[ArtifactPlanT, ...]:
        """Select exact compiled plans in declaration order.

        The path planner owns whether a semantic input requires a runtime
        artifact plan. Inputs satisfied by source bindings, metadata, or main
        flow are therefore absent from ``plans``. Every present plan remains
        indexed by its declaration-owned exact artifact ref.
        """
        plan_type.require_exact_map(
            plans,
            boundary=f"{type(self).__name__} artifact plan",
        )
        declared = self.artifact_key_specs.for_plan_type(plan_type)
        selected: list[ArtifactPlanT] = []
        for spec in declared.specs:
            ref = spec.ref()
            plan = plans.get(ref)
            if plan is None:
                continue
            selected.append(plan)
        return tuple(selected)

    @property
    def artifact_output_policy(self) -> type[ArtifactOutputPolicy]:
        """Return the native output owner unless this declaration supplies another."""

        return NativeReturnArtifactOutputPolicy

    def validate_artifact_output_declarations(self) -> None:
        """Validate every output kind through its declared payload owner."""

        self.artifact_output_policy.validate_output_declarations(self.artifact_specs)

    def validate_artifact_relation_refs(self, *, owner_name: str) -> None:
        self.artifact_specs.validate_registered_relation_refs(
            owner_name=owner_name,
            relation_specs=self.artifact_specs.for_plan_type(ArtifactOutputPlan).specs,
        )
