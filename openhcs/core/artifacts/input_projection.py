"""How one invocation selects from a producer's stored artifact input."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from openhcs.core.artifacts.plans import ArtifactInputPlan
from openhcs.core.artifacts.specs import ArtifactSpec
from openhcs.core.axes import Axis
from openhcs.core.component_group_scope import ComponentGroupScope
from openhcs.core.component_set import ComponentSet

if TYPE_CHECKING:
    from openhcs.core.callable_contract import FunctionStepExecutionScope
    from openhcs.core.function_patterns import FunctionInvocationKey


@dataclass(frozen=True, slots=True)
class ArtifactInputProjectionPlan:
    """Invocation-edge projection of one exact producer-owned artifact input."""

    invocation_scope: ComponentGroupScope
    producer_selection_scope: ComponentGroupScope
    component_scopes: tuple[ComponentGroupScope, ...] = ()
    consumer_variable_components: tuple[type[Axis], ...] = ()

    @staticmethod
    def declared_producer_selection_scope(
        input_spec: ArtifactSpec, storage_plan: ArtifactInputPlan
    ) -> ComponentGroupScope | None:
        """Resolve one producer selection declared by the input's relations."""

        producer_scope = storage_plan.producer_group_scope()
        scopes = input_spec.relation_answers(
            lambda relation: relation.input_producer_selection_scope(producer_scope)
        )
        if len(scopes) > 1:
            raise ValueError(
                f"Artifact input {input_spec.ref()!r} declares conflicting producer "
                f"selection scopes: {scopes!r}."
            )
        return scopes[0] if scopes else None

    @classmethod
    def producer_selection_for_invocation(
        cls,
        *,
        input_spec: ArtifactSpec,
        storage_plan: ArtifactInputPlan,
        component_scopes: tuple[ComponentGroupScope, ...],
        consumer_variable_components: ComponentSet,
        invocation_key: FunctionInvocationKey,
        execution_scope: FunctionStepExecutionScope,
    ) -> ComponentGroupScope:
        """Keep declaration-owned consumption separate from invocation dispatch."""

        from openhcs.core.callable_contract import FunctionStepExecutionScope

        declared = cls.declared_producer_selection_scope(input_spec, storage_plan)
        if declared is not None:
            return declared
        producer_scope = storage_plan.producer_group_scope()
        if producer_scope.is_ungrouped:
            return producer_scope
        if (
            producer_scope.has_single_static_key
            or execution_scope is FunctionStepExecutionScope.PLATE
            or producer_scope.component in consumer_variable_components
        ):
            return producer_scope
        for scope in component_scopes:
            if scope.component is producer_scope.component:
                return scope
        raise ValueError(
            f"Invocation {invocation_key!r} input {storage_plan.ref()!r} has "
            f"producer scope {producer_scope!r} but no exact relation-owned "
            "selection coordinate."
        )

    def selects_declared_complete_producer(
        self, input_spec: ArtifactSpec, storage_plan: ArtifactInputPlan
    ) -> bool:
        """Require the compiled selection to keep its declared relation's meaning."""

        declared = self.declared_producer_selection_scope(input_spec, storage_plan)
        if declared is None:
            return False
        if self.producer_selection_scope != declared:
            raise ValueError(
                f"Artifact input {input_spec.ref()!r} compiled selection "
                f"{self.producer_selection_scope!r} contradicts declaration {declared!r}."
            )
        return declared == storage_plan.producer_group_scope()

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "invocation_scope",
            ComponentGroupScope.from_raw(
                self.invocation_scope.keys,
                component=self.invocation_scope.component,
            ),
        )
        object.__setattr__(
            self,
            "producer_selection_scope",
            ComponentGroupScope.from_raw(
                self.producer_selection_scope.keys,
                component=self.producer_selection_scope.component,
            ),
        )
        object.__setattr__(
            self,
            "component_scopes",
            ComponentGroupScope.one_per_component(
                self.component_scopes,
                owner="Artifact input projection",
            ),
        )
        object.__setattr__(
            self,
            "consumer_variable_components",
            ComponentSet.of(self.consumer_variable_components).as_tuple(),
        )

    def component_scope(
        self,
        component: type[Axis],
    ) -> ComponentGroupScope | None:
        """Return the exact compiled coordinate for one projected component."""

        return next(
            (scope for scope in self.component_scopes if scope.component is component),
            None,
        )

    def projected_variable_components(
        self,
        storage_plan: ArtifactInputPlan,
    ) -> ComponentSet:
        """Return producer stack axes projected out for this consumer invocation."""

        consumer_components = ComponentSet.of(self.consumer_variable_components)
        if storage_plan.retains_producer_stack(consumer_components):
            return ComponentSet()
        return ComponentSet.of(storage_plan.variable_components)

    def validate_storage_plan(self, storage_plan: ArtifactInputPlan) -> None:
        """Require this projection to select within its producer storage plan."""

        artifact_ref = storage_plan.ref()
        producer_scope = storage_plan.producer_group_scope()
        selection_scope = self.producer_selection_scope
        if producer_scope.is_ungrouped:
            if selection_scope.is_ungrouped:
                return
            raise ValueError(
                f"Ungrouped producer {artifact_ref!r} cannot use grouped "
                f"selection {selection_scope!r}."
            )
        if selection_scope.component is not producer_scope.component:
            raise ValueError(
                f"Artifact input {artifact_ref!r} producer component "
                f"{producer_scope.component.name!r} does not match selection "
                f"{selection_scope.component!r}."
            )
        if selection_scope.is_dynamic or producer_scope.contains_scope(selection_scope):
            return
        raise ValueError(
            f"Artifact input {artifact_ref!r} selection "
            f"{selection_scope!r} is outside producer scope "
            f"{producer_scope!r}."
        )

    def validate_axis_projection(self, storage_plan: ArtifactInputPlan) -> None:
        """Require one exact axis invocation projection or retained stack axis."""

        self.validate_storage_plan(storage_plan)
        artifact_ref = storage_plan.ref()
        producer_scope = storage_plan.producer_group_scope()
        selection_scope = self.producer_selection_scope
        retained_components = ComponentSet.of(self.consumer_variable_components)
        # validate_storage_plan proved an ungrouped producer has an ungrouped
        # selection, so only grouped producers reach either branch below.
        if producer_scope.component in retained_components:
            if selection_scope != producer_scope:
                raise ValueError(
                    f"Retained producer axis {producer_scope.component.name!r} for "
                    f"{artifact_ref!r} must select the complete producer scope."
                )
        elif selection_scope.is_dynamic and (
            self.invocation_scope.component is not selection_scope.component
            or self.invocation_scope.is_ungrouped
        ):
            raise ValueError(
                f"Dynamic producer selection {selection_scope!r} for "
                f"{artifact_ref!r} is not owned by invocation scope "
                f"{self.invocation_scope!r}."
            )

        for component in self.projected_variable_components(storage_plan):
            scope = self.component_scope(component)
            if scope is None:
                raise ValueError(
                    f"Artifact input {artifact_ref!r} projects producer stack "
                    f"component {component.name!r} without an exact coordinate."
                )
            if scope.is_static and len(scope.keys) != 1:
                raise ValueError(
                    f"Artifact input {artifact_ref!r} projection for component "
                    f"{component.name!r} is not a single exact coordinate: {scope!r}."
                )
            if scope.is_dynamic and self.invocation_scope.component is not component:
                raise ValueError(
                    f"Dynamic stack projection {scope!r} for {artifact_ref!r} "
                    f"is not owned by invocation scope {self.invocation_scope!r}."
                )

    def validate_complete_producer_projection(
        self,
        storage_plan: ArtifactInputPlan,
    ) -> None:
        """Require a plate invocation to select the complete producer scope."""

        self.validate_storage_plan(storage_plan)
        artifact_ref = storage_plan.ref()
        producer_scope = storage_plan.producer_group_scope()
        if self.producer_selection_scope != producer_scope:
            raise ValueError(
                f"Plate artifact input {artifact_ref!r} must select complete "
                f"producer scope {producer_scope!r}, got "
                f"{self.producer_selection_scope!r}."
            )
