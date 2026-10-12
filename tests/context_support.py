"""Build processing contexts for tests without running the compiler."""

from __future__ import annotations

import inspect

from openhcs.core.context.processing_context import (
    CompiledContext,
    CompilingContext,
    ExecutingContext,
)

_INIT_PARAMETERS = frozenset(
    inspect.signature(CompilingContext.__init__).parameters
) - {"self"}


def compiled_context(**facts: object) -> CompiledContext:
    """Return a compiled context holding exactly the given compiled facts."""

    compiling = CompilingContext(
        **{name: value for name, value in facts.items() if name in _INIT_PARAMETERS}
    )
    unknown = facts.keys() - _INIT_PARAMETERS - vars(compiling).keys()
    if unknown:
        raise TypeError(f"Not compiled facts: {sorted(unknown)!r}.")
    for name, value in facts.items():
        setattr(compiling, name, value)
    return CompiledContext(vars(compiling))


def executing_context(**facts: object) -> ExecutingContext:
    """Return one execution of a context compiled from the given facts."""

    return compiled_context(**facts).executing()


def with_facts(context: CompiledContext, **facts: object) -> ExecutingContext:
    """Return a fresh execution of ``context`` with some compiled facts replaced."""

    return CompiledContext(context.compiled_facts() | facts).executing()
