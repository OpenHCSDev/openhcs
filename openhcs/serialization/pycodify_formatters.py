from __future__ import annotations

import inspect
from collections.abc import Callable
from pathlib import Path

from objectstate import semantic_values_equal
from objectstate.codegen import field_needs_source
from pycodify import (
    FormatContext,
    SourceFormatter,
    SourceFragment,
    imported_name,
    to_source,
)
from formbridge.pattern_metadata import PatternScopeToken
from python_introspect import callable_declaration_kwargs, parameter_exclusions

from openhcs.core.axes import is_grouping_declaration
from openhcs.core.callable_contract import CallableContract
from openhcs.core.function_reference import (
    FunctionReference,
    FunctionReferenceTransportAuthority,
)
from openhcs.core.steps.function_step import FunctionStep


class OpenHCSCallableFormatter(SourceFormatter):
    priority = 75

    def can_format(self, value) -> bool:
        return inspect.isfunction(value) or inspect.isbuiltin(value)

    def reference_for(self, value) -> FunctionReference:
        return FunctionReferenceTransportAuthority.function_reference(value)

    def format(self, value, context: FormatContext) -> SourceFragment:
        return to_source(self.reference_for(value), context)


class MaterializationSpecFormatter(SourceFormatter):
    priority = 110

    def can_format(self, value) -> bool:
        from openhcs.processing.materialization.core import MaterializationSpec

        return isinstance(value, MaterializationSpec)

    def format(self, value, context: FormatContext) -> SourceFragment:
        class_ref = imported_name(
            type(value).__module__, type(value).__qualname__, context
        )
        item_ctx = context.indented()
        output_frags = [to_source(output, item_ctx) for output in value.outputs]
        imports = set(class_ref.imports)
        for frag in output_frags:
            imports |= set(frag.imports)

        args = [frag.code for frag in output_frags]
        if value.allowed_backends is not None:
            allowed_backends_frag = to_source(value.allowed_backends, item_ctx)
            imports |= set(allowed_backends_frag.imports)
            args.append(f"allowed_backends={allowed_backends_frag.code}")
        if value.primary != 0:
            args.append(f"primary={value.primary}")
        from openhcs.processing.materialization.constants import WriteMode

        if value.write_mode is not WriteMode.OVERWRITE:
            write_mode_frag = to_source(value.write_mode, item_ctx)
            imports |= set(write_mode_frag.imports)
            args.append(f"write_mode={write_mode_frag.code}")

        inner = f",\n{item_ctx.indent_str}".join(args)
        return SourceFragment(
            f"{class_ref.code}(\n{item_ctx.indent_str}{inner}\n{context.indent_str})",
            frozenset(imports),
        )


def _public_pattern_callable(value: object) -> Callable | None:
    if isinstance(value, FunctionReference):
        return value.resolve()
    if is_grouping_declaration(value):
        return None
    return value if callable(value) else None


def _is_pattern_tuple(value) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) == 2
        and _public_pattern_callable(value[0]) is not None
        and isinstance(value[1], dict)
    )


def _is_pattern_item(value) -> bool:
    return _public_pattern_callable(value) is not None or _is_pattern_tuple(value)


def _strip_internal_pattern_metadata(args):
    """Remove UI-only metadata keys from function-pattern kwargs."""
    if not isinstance(args, dict):
        return {}
    return PatternScopeToken.without_token(args)


def _exported_callable_parameter_exclusions(func) -> set[str]:
    """Return parameters that must not be emitted for a callable wrapper."""

    func = _public_pattern_callable(func)
    if func is None:
        raise TypeError("Function-pattern leaves must resolve to public callables.")
    contract = CallableContract.from_callable(func)
    excluded = set(parameter_exclusions(func))
    excluded.update(contract.runtime_owned_parameter_names)
    raw_func = contract.raw_processing_function
    if callable(raw_func):
        excluded.update(parameter_exclusions(raw_func))
    return excluded.difference(contract.overridable_runtime_parameter_names)


class FunctionPatternTupleFormatter(SourceFormatter):
    priority = 85

    def can_format(self, value) -> bool:
        return _is_pattern_tuple(value)

    def format(self, value, context: FormatContext) -> SourceFragment:
        func, args = value
        public_func = _public_pattern_callable(func)
        if public_func is None:
            raise TypeError("Function-pattern leaves must resolve to public callables.")
        args = _strip_internal_pattern_metadata(args)
        hidden_parameters = _exported_callable_parameter_exclusions(public_func)
        if hidden_parameters:
            args = {
                name: arg_value
                for name, arg_value in args.items()
                if name not in hidden_parameters
            }

        if not args and context.clean_mode:
            return to_source(func, context)

        final_args = callable_declaration_kwargs(
            public_func,
            args,
            values_equal=semantic_values_equal,
            omit_defaults=context.clean_mode,
        )

        if not final_args and context.clean_mode:
            return to_source(func, context)

        declared_paths = CallableContract.from_callable(
            public_func
        ).declared_path_parameters
        final_args = {
            name: (
                Path(arg_value)
                if name in declared_paths and isinstance(arg_value, str)
                else arg_value
            )
            for name, arg_value in final_args.items()
        }

        func_frag = to_source(func, context)
        args_frag = to_source(final_args, context.indented())
        code = f"({func_frag.code}, {args_frag.code})"
        imports = func_frag.imports | args_frag.imports
        return SourceFragment(code, imports)


class FunctionPatternListFormatter(SourceFormatter):
    priority = 84

    def can_format(self, value) -> bool:
        return (
            isinstance(value, list)
            and value
            and all(_is_pattern_item(item) for item in value)
        )

    def format(self, value: list, context: FormatContext) -> SourceFragment:
        if context.clean_mode and len(value) == 1:
            return to_source(value[0], context)

        item_ctx = context.indented()
        item_frags = [to_source(item, item_ctx) for item in value]
        imports = frozenset().union(*(frag.imports for frag in item_frags))
        inner = f",\n{item_ctx.indent_str}".join(frag.code for frag in item_frags)
        code = f"[\n{item_ctx.indent_str}{inner}\n{context.indent_str}]"
        return SourceFragment(code, imports)


class FunctionStepFormatter(SourceFormatter):
    priority = 80

    def can_format(self, value) -> bool:
        return isinstance(value, FunctionStep)

    def format(self, value: FunctionStep, context: FormatContext) -> SourceFragment:
        from openhcs.core.steps.abstract import AbstractStep

        signatures = [
            (name, param)
            for name, param in inspect.signature(
                FunctionStep.__init__
            ).parameters.items()
            if name != "self" and param.kind != inspect.Parameter.VAR_KEYWORD
        ]
        seen = {name for name, _param in signatures}
        signatures.extend(
            (name, param)
            for name, param in inspect.signature(
                AbstractStep.__init__
            ).parameters.items()
            if name != "self" and name not in seen
        )

        default_step = FunctionStep(func=lambda: None)
        step_values = vars(value)
        default_values = vars(default_step)
        field_ctx = context.indented()
        params = []
        imports = set()

        for name, param in signatures:
            if name in step_values:
                current_value = step_values[name]
            else:
                current_value = param.default

            if name in default_values:
                default_value = default_values[name]
            else:
                default_value = param.default

            if not field_needs_source(current_value, default_value, context):
                continue

            frag = to_source(current_value, field_ctx)
            imports |= frag.imports
            params.append(f"{name}={frag.code}")

        class_ref = imported_name(
            FunctionStep.__module__, FunctionStep.__qualname__, context
        )
        imports |= class_ref.imports

        if not params:
            return SourceFragment(f"{class_ref.code}()", frozenset(imports))

        inner = f",\n{field_ctx.indent_str}".join(params)
        code = f"{class_ref.code}(\n{field_ctx.indent_str}{inner}\n{context.indent_str})"
        return SourceFragment(code, frozenset(imports))
