from __future__ import annotations

import inspect
from typing import Any, Dict, Tuple

from openhcs.core.steps.function_step import FunctionStep
from pyqt_reactive.services.pattern_data_manager import SCOPE_TOKEN_KEY

from pycodify import FormatContext, SourceFormatter, SourceFragment, to_source


def _is_external_registered_function(func: Any) -> bool:
    """Check if function is an external library function registered with OpenHCS."""
    return (
        hasattr(func, "slice_by_slice")
        and not hasattr(func, "__processing_contract__")
        and not func.__module__.startswith("openhcs.")
    )


class OpenHCSCallableFormatter(SourceFormatter):
    priority = 75

    def can_format(self, value: Any) -> bool:
        return callable(value) and not isinstance(value, type)

    def format(self, value: Any, context: FormatContext) -> SourceFragment:
        if inspect.ismethod(value):
            return SourceFragment(repr(value), frozenset())

        module = getattr(value, "__module__", None)
        name = getattr(value, "__name__", None)
        if not module or not name:
            return SourceFragment(repr(value), frozenset())

        if _is_external_registered_function(value):
            module = f"openhcs.{module}"

        import_pair = (module, name)
        mapped = context.name_mappings.get(import_pair, name)
        return SourceFragment(mapped, frozenset([import_pair]))


def _is_pattern_tuple(value: Any) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) == 2
        and callable(value[0])
        and isinstance(value[1], dict)
    )


def _is_pattern_item(value: Any) -> bool:
    return callable(value) or _is_pattern_tuple(value)


def _strip_internal_pattern_metadata(args: Dict[str, Any]) -> Dict[str, Any]:
    """Remove UI-only metadata keys from function-pattern kwargs."""
    if not isinstance(args, dict):
        return {}
    return {k: v for k, v in args.items() if k != SCOPE_TOKEN_KEY}


class FunctionPatternTupleFormatter(SourceFormatter):
    priority = 85

    def can_format(self, value: Any) -> bool:
        return _is_pattern_tuple(value)

    def format(self, value: Tuple[Any, Dict[str, Any]], context: FormatContext) -> SourceFragment:
        func, args = value
        args = _strip_internal_pattern_metadata(args)

        if not args and context.clean_mode:
            return to_source(func, context)

        try:
            defaults = {
                k: v.default
                for k, v in inspect.signature(func).parameters.items()
                if v.default is not inspect.Parameter.empty
            }
        except (ValueError, TypeError):
            defaults = {}

        if context.clean_mode:
            final_args = {
                k: v for k, v in args.items() if k not in defaults or v != defaults[k]
            }
        else:
            final_args = {**defaults, **args}

        if not final_args and context.clean_mode:
            return to_source(func, context)

        func_frag = to_source(func, context)
        args_frag = to_source(final_args, context.indented())
        code = f"({func_frag.code}, {args_frag.code})"
        imports = func_frag.imports | args_frag.imports
        return SourceFragment(code, imports)


class FunctionPatternListFormatter(SourceFormatter):
    priority = 84

    def can_format(self, value: Any) -> bool:
        return isinstance(value, list) and value and all(_is_pattern_item(item) for item in value)

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

    def can_format(self, value: Any) -> bool:
        return isinstance(value, FunctionStep)

    def format(self, value: FunctionStep, context: FormatContext) -> SourceFragment:
        from openhcs.core.steps.abstract import AbstractStep

        signatures = [
            (name, param)
            for name, param in inspect.signature(FunctionStep.__init__).parameters.items()
            if name != "self" and param.kind != inspect.Parameter.VAR_KEYWORD
        ] + [
            (name, param)
            for name, param in inspect.signature(AbstractStep.__init__).parameters.items()
            if name != "self"
        ]

        default_step = FunctionStep(func=lambda: None)
        field_ctx = context.indented()
        params = []
        imports = set()

        for name, param in signatures:
            current_value = getattr(value, name, param.default)
            default_value = getattr(default_step, name, param.default)

            if context.clean_mode and current_value == default_value:
                continue

            frag = to_source(current_value, field_ctx)
            imports |= frag.imports
            params.append(f"{name}={frag.code}")

        import_pair = (FunctionStep.__module__, FunctionStep.__name__)
        class_name = context.name_mappings.get(import_pair, FunctionStep.__name__)
        imports.add(import_pair)

        if not params:
            return SourceFragment(f"{class_name}()", frozenset(imports))

        inner = f",\n{field_ctx.indent_str}".join(params)
        code = f"{class_name}(\n{field_ctx.indent_str}{inner}\n{context.indent_str})"
        return SourceFragment(code, frozenset(imports))
