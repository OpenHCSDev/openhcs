"""Public step package exports without eager concrete-step import cycles."""

from __future__ import annotations

from python_introspect import lazy_exports

from openhcs.core.steps.abstract import AbstractStep

__all__ = (
    "AbstractStep",
    *lazy_exports(globals(), {"openhcs.core.steps.function_step": ("FunctionStep",)}),
)


# PERFORMANCE OPTIMIZATION: Pre-warm step editor cache at import time
try:
    from objectstate import prewarm_callable_analysis_cache

    prewarm_callable_analysis_cache(AbstractStep.__init__)
except ImportError:
    # Circular import during subprocess initialization - cache warming not needed
    # for non-UI execution contexts (ZMQ server, workers, etc.)
    pass
