"""Transport normalization for FunctionStep declarations."""

from __future__ import annotations

from copy import copy
from dataclasses import replace
from types import ModuleType
from collections.abc import Mapping, Sequence
from typing import Any

from openhcs.core.callable_contract import CallableContract, CallableMetadata
from openhcs.core.function_patterns import (
    CompiledFunctionGroup,
    CompiledFunctionInvocation,
    CompiledFunctionPattern,
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
        from pycodify import Assignment
        from openhcs.serialization.source_path_factoring import (
            OpenHCSPythonSourceDocument,
        )

        steps = list(pipeline_steps)
        cls._require_function_steps(steps)
        normalized = cls.normalize_pipeline(steps)
        return OpenHCSPythonSourceDocument(
            Assignment(PipelineDocumentField.PIPELINE_STEPS.value, normalized),
            header="# Edit this pipeline and save to apply changes",
            clean_mode=clean_mode,
        ).render()

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
        transport_context = copy(context)
        transport_context.step_plans = {
            step_id: replace(
                step_plan,
                compiled_function_pattern=cls.normalize_compiled_pattern(
                    step_plan.compiled_function_pattern, contracts=contracts,
                ),
            )
            for step_id, step_plan in context.step_plans.items()
        }
        return transport_context

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
        if isinstance(func_spec, FunctionReference):
            return cls.normalize_function_reference(func_spec)
        if isinstance(func_spec, list):
            normalized_items = [cls.normalize_function_spec(item) for item in func_spec]
            if all(
                normalized is original
                for normalized, original in zip(normalized_items, func_spec)
            ):
                return func_spec
            return normalized_items
        if isinstance(func_spec, dict):
            normalized_items = {
                key: cls.normalize_function_spec(item)
                for key, item in func_spec.items()
            }
            if all(normalized_items[key] is item for key, item in func_spec.items()):
                return func_spec
            return normalized_items
        if isinstance(func_spec, tuple) and func_spec:
            normalized_func = cls.normalize_function_spec(func_spec[0])
            if normalized_func is func_spec[0]:
                return func_spec
            return (normalized_func, *func_spec[1:])
        if isinstance(func_spec, ModuleType):
            raise TypeError(
                "Pipeline contains a module object where a callable is required: "
                f"{func_spec.__name__}. Reload or edit the step to select a function."
            )
        if callable(func_spec):
            from openhcs.processing.backends.lib_registry.registry_service import (
                RegistryService,
            )

            return RegistryService.registered_callable(func_spec)
        return func_spec

    @classmethod
    def normalize_function_reference(
        cls,
        reference: FunctionReference,
    ) -> FunctionReference:
        metadata = cls.normalize_callable_metadata(reference.metadata)
        if metadata is reference.metadata:
            return reference
        return replace(reference, metadata=metadata)

    @classmethod
    def normalize_callable_metadata(cls, metadata: CallableMetadata) -> CallableMetadata:
        """Derive declaration-only transport from one captured metadata owner."""
        metadata = FunctionReferenceTransportAuthority.reference_metadata(metadata)
        raw_processing_function = metadata.raw_processing_function
        normalized_raw = (
            cls.normalize_function_reference(raw_processing_function)
            if isinstance(raw_processing_function, FunctionReference)
            else raw_processing_function
        )
        raw_is_normalized = normalized_raw is raw_processing_function
        if metadata.prepare is None and raw_is_normalized:
            return metadata
        metadata = metadata.without_prepare()
        if not raw_is_normalized:
            metadata = metadata.with_raw_processing_function(normalized_raw)
        return metadata

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
        normalized_func = cls.normalize_function_spec(contract.func)
        metadata = cls.normalize_callable_metadata(contract.metadata)
        normalized = (
            contract
            if normalized_func is contract.func and metadata is contract.metadata
            else replace(contract, func=normalized_func, metadata=metadata)
        )
        if contracts is not None:
            contracts[id(contract)] = normalized
        return normalized
