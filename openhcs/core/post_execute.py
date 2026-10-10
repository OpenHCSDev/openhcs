"""Domain work that runs after a dataset's execution completes.

A :class:`PostExecuteHook` is bound at compile time from the global config and
travels with every compiled context. While steps run it may observe the
outputs they save; after every partition succeeds it runs once over the
combined observations. Domains register hooks from their ``extension_modules``;
the kernel calls only this family.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Iterable, Mapping
from types import MappingProxyType
from typing import TYPE_CHECKING, ClassVar

from metaclass_registry import AutoRegisterMeta

from openhcs.core.dataset_sources.discovery import domain_registry_config

if TYPE_CHECKING:
    from openhcs.core.compiled_step_plan import CompiledStepPlan
    from openhcs.core.config import GlobalPipelineConfig
    from openhcs.core.context.processing_context import ProcessingContext
    from openhcs.core.orchestrator.execution_result import (
        ExecutionResult,
        RuntimeExecutionObservation,
    )
    from openhcs.core.steps.function_artifact_materialization import (
        MaterializedRuntimeArtifact,
        RuntimeArtifactMaterialization,
    )
    from openhcs.processing.materialization.core import Output


HookObservations = Mapping[str, object]
"""Observations keyed by the observing hook's ``hook_name``."""


class PostExecuteHook(ABC, metaclass=AutoRegisterMeta):
    """One bound piece of post-execution domain work."""

    __registry_config__ = domain_registry_config(
        key_attribute="hook_name",
        registry_name="post-execute hook",
    )
    hook_name: ClassVar[str | None] = None

    @classmethod
    @abstractmethod
    def bind(cls, global_config: "GlobalPipelineConfig") -> "PostExecuteHook":
        """This hook configured for one compilation."""

    def observe_saved_outputs(
        self,
        context: "ProcessingContext",
        plan: "CompiledStepPlan",
        saved: "MaterializedRuntimeArtifact",
    ) -> object | None:
        """What this hook needs from outputs a step just saved (``None``: nothing)."""
        del context, plan, saved
        return None

    def observe_reused_outputs(
        self,
        context: "ProcessingContext",
        plan: "CompiledStepPlan",
        materialization: "RuntimeArtifactMaterialization",
        outputs: tuple["Output", ...],
    ) -> object | None:
        """What this hook needs from historical outputs a step reused."""
        del context, plan, materialization, outputs
        return None

    @classmethod
    def combine(cls, observations: Iterable[object]) -> object | None:
        """Merge this hook's observations from several steps or partitions."""
        merged = tuple(observations)
        if merged:
            raise NotImplementedError(
                f"{cls.__name__} observes outputs and must implement combine()."
            )
        return None

    @abstractmethod
    def run(
        self,
        compiled_contexts: Mapping[str, "ProcessingContext"],
        observation: object | None,
    ) -> None:
        """Do this hook's work after every partition succeeded."""

    # -- the family as the kernel uses it -------------------------------------

    @staticmethod
    def bind_all(global_config: "GlobalPipelineConfig") -> tuple["PostExecuteHook", ...]:
        return tuple(
            hook_type.bind(global_config)
            for hook_type in PostExecuteHook.__registry__.values()
        )

    @staticmethod
    def observe_saved(
        context: "ProcessingContext",
        plan: "CompiledStepPlan",
        saved: "MaterializedRuntimeArtifact",
    ) -> HookObservations:
        return _observations(
            (hook, hook.observe_saved_outputs(context, plan, saved))
            for hook in context.post_execute_hooks
        )

    @staticmethod
    def observe_reused(
        context: "ProcessingContext",
        plan: "CompiledStepPlan",
        materialization: "RuntimeArtifactMaterialization",
        outputs: tuple["Output", ...],
    ) -> HookObservations:
        return _observations(
            (hook, hook.observe_reused_outputs(context, plan, materialization, outputs))
            for hook in context.post_execute_hooks
        )

    @staticmethod
    def combine_all(observations: Iterable[HookObservations]) -> HookObservations:
        by_hook: dict[str, list[object]] = {}
        for observation in observations:
            for hook_name, value in observation.items():
                by_hook.setdefault(hook_name, []).append(value)
        return _observations_by_name(
            (hook_name, PostExecuteHook.__registry__[hook_name].combine(values))
            for hook_name, values in by_hook.items()
        )

    @staticmethod
    def run_all(
        compiled_contexts: Mapping[str, "ProcessingContext"],
        execution_results: Mapping[str, "ExecutionResult"],
        plate_runtime_observation: "RuntimeExecutionObservation",
    ) -> None:
        """Run every bound hook over the observations of this execution."""
        context_observations = tuple(
            context_observation
            for runtime_observation in (
                *(result.runtime_observation for result in execution_results.values()),
                plate_runtime_observation,
            )
            for context_observation in runtime_observation.contexts
        )
        for context_observation in context_observations:
            if context_observation.context_key not in compiled_contexts:
                raise KeyError(
                    "Runtime observation references unknown compiled context "
                    f"{context_observation.context_key!r}."
                )
        observations = PostExecuteHook.combine_all(
            context_observation.outputs.hook_observations
            for context_observation in context_observations
        )
        first_context = next(iter(compiled_contexts.values()))
        for hook in first_context.post_execute_hooks:
            hook.run(compiled_contexts, observations.get(hook.hook_name))


def _observations(
    items: Iterable[tuple[PostExecuteHook, object | None]],
) -> HookObservations:
    return _observations_by_name((hook.hook_name, value) for hook, value in items)


def _observations_by_name(
    items: Iterable[tuple[str, object | None]],
) -> HookObservations:
    return MappingProxyType(
        {hook_name: value for hook_name, value in items if value is not None}
    )


__all__ = ["HookObservations", "PostExecuteHook"]
