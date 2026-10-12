"""Transport normalization for FunctionStep declarations."""

from __future__ import annotations

from dataclasses import replace
from collections.abc import Mapping, Sequence
from typing import Any

from openhcs.core.callable_contract import CallableContract
from openhcs.core.function_patterns import (
    CompiledFunctionGroup,
    CompiledFunctionPattern,
    AuthoredFunctionPattern,
    NormalizedFunctionPattern,
    NormalizedFunctionItem,
)
from openhcs.core.function_reference import (
    FunctionReference,
    FunctionReferenceTransportAuthority,
)
from openhcs.core.pipeline_document_fields import PipelineDocumentField
from openhcs.core.steps.function_step import FunctionStep



class FunctionStepTransportAuthority:
    """Canonicalize FunctionStep callables before process or ZMQ transport."""

    @classmethod
    def source_from_pipeline(
        cls,
        pipeline_steps: Sequence[FunctionStep],
        *,
        clean_mode: bool = True,
    ) -> str:
        """Normalize and pycodify one public FunctionStep list."""
        import openhcs.serialization.pycodify_formatters  # noqa: F401
        from pycodify import Assignment, generate_python_source

        steps = list(pipeline_steps)
        cls._require_function_steps(steps)
        normalized = cls.normalize_pipeline(steps)
        return generate_python_source(
            Assignment(PipelineDocumentField.PIPELINE_STEPS.value, normalized),
            header="# Edit this pipeline and save to apply changes",
            clean_mode=clean_mode,
        )

    @classmethod
    def pipeline_steps_from_namespace(
        cls,
        namespace: Mapping[str, object],
    ) -> list[FunctionStep]:
        """Require and normalize the public FunctionStep export."""
        field_name = PipelineDocumentField.PIPELINE_STEPS.value
        if field_name not in namespace:
            raise ValueError(f"Pipeline source must define {field_name!r}.")
        pipeline_steps = namespace[field_name]
        if type(pipeline_steps) is not list:
            raise TypeError(
                f"{field_name} must be a list[FunctionStep], "
                f"got {type(pipeline_steps).__name__}."
            )
        cls._require_function_steps(pipeline_steps)
        return cls.normalize_pipeline(pipeline_steps)

    @classmethod
    def _require_function_steps(cls, pipeline_steps: Sequence[object]) -> None:
        for index, step in enumerate(pipeline_steps):
            if not isinstance(step, FunctionStep):
                raise TypeError(
                    f"Pipeline member {index} must be FunctionStep, "
                    f"got {type(step).__name__}."
                )

    @classmethod
    def normalize_pipeline(cls, definition_pipeline: list[Any]) -> list[Any]:
        normalized = [cls.normalize_step(step) for step in definition_pipeline]
        return normalized

    @classmethod
    def normalize_contexts(cls, contexts: Mapping[str, Any]) -> dict[str, Any]:
        # Preserve declaration aliases across axis-specific executable bindings.
        # The identity table lives only for this normalization.
        contracts: dict[int, CallableContract] = {}
        return {
            axis_id: cls.normalize_context(context, contracts=contracts)
            for axis_id, context in contexts.items()
        }

    @classmethod
    def normalize_context(
        cls,
        context: Any,
        *,
        contracts: dict[int, CallableContract] | None = None,
    ) -> Any:
        """Derive transport plans without replacing prepared runtime contracts."""
        if contracts is None:
            contracts = {}
        return context.with_step_plans({
            step_id: replace(
                step_plan,
                compiled_function_pattern=cls.normalize_compiled_pattern(
                    step_plan.compiled_function_pattern, contracts=contracts,
                ),
            )
            for step_id, step_plan in context.step_plans.items()
        })

    @classmethod
    def normalize_step(cls, step: Any) -> Any:
        if not isinstance(step, FunctionStep):
            return step
        func_spec = step.function_spec()
        if func_spec is None:
            return step
        normalized_func = cls.normalize_function_spec(func_spec)
        if normalized_func is func_spec:
            return step
        return step.with_function_spec(normalized_func)

    @classmethod
    def normalize_function_spec(cls, func_spec: Any) -> Any:
        if isinstance(func_spec, NormalizedFunctionPattern):
            contracts: dict[int, CallableContract] = {}
            return replace(
                func_spec,
                groups=tuple(
                    replace(
                        group,
                        items=tuple(
                            cls.normalize_compiled_invocation(item, contracts=contracts)
                            for item in group.items
                        ),
                    )
                    for group in func_spec.groups
                ),
            )
        return AuthoredFunctionPattern.map_leaves(func_spec, cls._normalize_leaf)

    @classmethod
    def _normalize_leaf(cls, leaf: Any, func: Any, kwargs: Any) -> Any:
        normalized = cls.normalize_callable(func)
        if normalized is func:
            return leaf
        return normalized if kwargs is None else (normalized, kwargs)

    @classmethod
    def normalize_callable(cls, func: Any) -> Any:
        if isinstance(func, FunctionReference):
            return cls.normalize_function_reference(func)
        if callable(func):
            from openhcs.processing.backends.lib_registry.registry_service import (
                RegistryService,
            )

            return RegistryService.registered_callable(func)
        return func

    @classmethod
    def normalize_function_reference(
        cls,
        reference: FunctionReference,
    ) -> FunctionReference:
        declaration = FunctionReferenceTransportAuthority.with_raw_function_reference(
            reference.declaration
        )
        if declaration is reference.declaration:
            return reference
        return replace(reference, declaration=declaration)

    @classmethod
    def normalize_compiled_pattern(
        cls,
        pattern: CompiledFunctionPattern | None,
        *,
        contracts: dict[int, CallableContract] | None = None,
    ) -> CompiledFunctionPattern | None:
        if pattern is None:
            return None
        if contracts is None:
            contracts = {}
        groups = tuple(
            cls.normalize_compiled_group(group, contracts=contracts)
            for group in pattern.groups
        )
        if all(
            normalized is original
            for normalized, original in zip(groups, pattern.groups)
        ):
            return pattern
        return replace(pattern, groups=groups)

    @classmethod
    def normalize_compiled_group(
        cls,
        group: CompiledFunctionGroup,
        *,
        contracts: dict[int, CallableContract] | None = None,
    ) -> CompiledFunctionGroup:
        if contracts is None:
            contracts = {}
        invocations = tuple(
            cls.normalize_compiled_invocation(invocation, contracts=contracts)
            for invocation in group.invocations
        )
        if all(
            normalized is original
            for normalized, original in zip(invocations, group.invocations)
        ):
            return group
        return replace(group, invocations=invocations)

    @classmethod
    def normalize_compiled_invocation(
        cls,
        invocation: NormalizedFunctionItem,
        *,
        contracts: dict[int, CallableContract] | None = None,
    ) -> NormalizedFunctionItem:
        contract = cls.normalize_callable_contract(
            invocation.contract, contracts=contracts,
        )
        if contract is invocation.contract:
            return invocation
        return replace(invocation, contract=contract)

    @classmethod
    def normalize_callable_contract(
        cls,
        contract: CallableContract,
        *,
        contracts: dict[int, CallableContract] | None = None,
    ) -> CallableContract:
        if contracts is not None and id(contract) in contracts:
            return contracts[id(contract)]
        normalized_func = cls.normalize_callable(contract.func)
        normalized = FunctionReferenceTransportAuthority.with_raw_function_reference(
            contract
        )
        if normalized_func is not contract.func:
            normalized = replace(normalized, func=normalized_func)
        if contracts is not None:
            contracts[id(contract)] = normalized
        return normalized
