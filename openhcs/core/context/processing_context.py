"""Processing contexts for OpenHCS, one class per phase.

``ProcessingContext`` holds what the compiler decides for one multiprocessing-axis
value. ``CompilingContext`` is that state while the compiler fills it in;
``CompilingContext.freeze`` returns an immutable ``CompiledContext``, which is
what bundles and workers carry. ``CompiledContext.executing`` starts one
execution: an ``ExecutingContext`` holds the compiled facts plus the runtime
stores, caches and debug sink of that execution only.
"""

from __future__ import annotations

from collections.abc import Callable, Iterator
from contextlib import contextmanager
from dataclasses import dataclass
from typing import TYPE_CHECKING, TypeVar, cast

if TYPE_CHECKING:
    from openhcs.core.post_execute import PostExecuteHook
    from openhcs.core.orchestrator.worker_lanes import WorkerLaneExecutionContext
    from openhcs.core.steps.abstract import StepExecutionObservation

from polystore.filemanager import FileManager
from zmqruntime.config import ZMQConfig

from openhcs.core.config import StreamingConfig, TiffConfig
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.debug import (
    DebugEventSink,
    DebugExecutionContext,
    NO_OP_DEBUG_EVENT_SINK,
)
from openhcs.core.runtime_stores import RuntimeValueStore
from openhcs.core.runtime_pattern_cache import RuntimePatternDiscoveryCache
from openhcs.core.runtime_stack_cache import RuntimeImageStackCache
from openhcs.core.runtime_source_binding_cache import RuntimeSourceBindingContextCache
from openhcs.core.source_workspace_projection import (
    WorkspaceSourceProjections,
)
from openhcs.core.source_matching import SourceImageSetIdentityPolicy
from openhcs.core.streaming_config_declarations import ViewerFamily
from openhcs.core.axis_filter import StepAxisFilterMap
from openhcs.core.steps.function_output_identity import FunctionOutputIdentityCache
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG

_RuntimeStepValue = TypeVar("_RuntimeStepValue")


@dataclass(frozen=True, slots=True)
class RequiredVisualizer:
    """Streaming visualizer required by a compiled processing context."""

    backend_name: str | None
    config: StreamingConfig

    @property
    def key(self) -> tuple[type[ViewerFamily], int]:
        return (self.config.viewer_family, self.config.port)

    @property
    def launch_message(self) -> str:
        return (
            f"Launching {self.config.viewer_family.display_name} viewer "
            f"on port {self.config.port}"
        )


class ProcessingContext:
    """What the compiler decides for one multiprocessing-axis value.

    Attributes:
        step_plans: Compiled plan of each step, by step index.
        axis_id: The multiprocessing-axis value being processed.
        filemanager: FileManager for VFS operations.
        post_execute_hooks: Domain hooks bound for this compilation.
        output_dataset_root: Planned runtime output dataset root.
        pipeline_sequential_mode: Whether sequential combinations are pipeline-wide.
        pipeline_sequential_combinations: Combinations for pipeline-wide mode.
        current_sequential_combination: The combination this context compiles.
    """

    step_plans: dict[int, CompiledStepPlan]
    axis_id: str | None
    filemanager: FileManager | None

    @classmethod
    def require_parameter_name(cls) -> str:
        """Return the callable ABI name for runtime context injection."""
        return "context"

    def require_axis_id(self) -> str:
        """Return the compiled multiprocessing-axis identity."""

        if not self.axis_id:
            raise ValueError(f"{type(self).__name__} requires an axis_id.")
        return self.axis_id


class CompilingContext(ProcessingContext):
    """A processing context while the compiler fills it in.

    OWNERSHIP: only ``PipelineOrchestrator.create_context`` builds one.
    """

    def __init__(
        self,
        step_plans: dict[int, CompiledStepPlan] | None = None,
        axis_id: str | None = None,
        filemanager: FileManager | None = None,
        tiff_config: TiffConfig | None = None,
        post_execute_hooks: "tuple[PostExecuteHook, ...]" = (),
        output_dataset_root: str | None = None,
        transport_config: ZMQConfig = OPENHCS_ZMQ_CONFIG,
    ):
        self.step_plans = {} if step_plans is None else dict(step_plans)
        self.source_image_set_identity_policy = SourceImageSetIdentityPolicy()
        self.axis_id = axis_id
        self.filemanager = filemanager
        self.microscope_handler = None
        self.input_dir = None
        self.workspace_path = None
        self.dataset_root = None
        self.required_visualizers: list[RequiredVisualizer] = []
        self.step_axis_filters: StepAxisFilterMap = {}
        self.metadata_cache: dict[str, dict[str, str | None]] | None = None
        self.tiff_config = tiff_config if tiff_config is not None else TiffConfig()
        self.post_execute_hooks = tuple(post_execute_hooks)
        self.output_dataset_root = output_dataset_root
        self.transport_config = transport_config
        self.pipeline_sequential_mode = False
        self.pipeline_sequential_combinations = None
        self.current_sequential_combination = None

    def freeze(self) -> "CompiledContext":
        """Return the immutable compiled context once every fact is set."""

        if not self.axis_id:
            raise RuntimeError("Cannot freeze ProcessingContext: 'axis_id' is not set.")
        if self.filemanager is None:
            raise RuntimeError(
                "Cannot freeze ProcessingContext: 'filemanager' is not set."
            )
        return CompiledContext(vars(self))


class CompiledContext(ProcessingContext):
    """The compiler's immutable result for one axis value (or combination)."""

    def __init__(self, compiled_facts: dict[str, object]):
        object.__setattr__(self, "_compiled_facts", frozenset(compiled_facts))
        self.__dict__.update(compiled_facts)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError(
            f"{type(self).__name__} is immutable; cannot set {name!r}."
        )

    def compiled_facts(self) -> dict[str, object]:
        return {name: self.__dict__[name] for name in self._compiled_facts}

    def with_step_plans(
        self, step_plans: dict[int, CompiledStepPlan]
    ) -> "CompiledContext":
        """Return this compiled context with its step plans replaced."""
        return CompiledContext(self.compiled_facts() | {"step_plans": step_plans})

    def executing(
        self,
        execution_runtime: "WorkerLaneExecutionContext | None" = None,
    ) -> "ExecutingContext":
        """Start one execution of this compiled context."""
        return ExecutingContext(self, execution_runtime)


class ExecutingContext(CompiledContext):
    """One execution of a compiled context, with that execution's state.

    ``execution_runtime`` is the worker lane running it; dataset-scoped steps
    run in the parent without a lane.
    """

    def __init__(
        self,
        compiled: CompiledContext,
        execution_runtime: "WorkerLaneExecutionContext | None" = None,
    ):
        from openhcs.core.steps.abstract import StepExecutionObservation

        CompiledContext.__init__(self, compiled.compiled_facts())
        self.runtime_value_store = RuntimeValueStore()
        self.runtime_image_stack_cache = RuntimeImageStackCache()
        self.runtime_function_output_identity_cache = FunctionOutputIdentityCache()
        self.runtime_pattern_discovery_cache = RuntimePatternDiscoveryCache()
        self.runtime_source_binding_context_cache = RuntimeSourceBindingContextCache()
        self.completed_step_outputs = StepExecutionObservation.empty()
        self.debug_event_sink = NO_OP_DEBUG_EVENT_SINK
        self.execution_runtime = execution_runtime
        self._runtime_step_values: dict[type[object], object] | None = None
        self._runtime_source_workspace_projections: (
            WorkspaceSourceProjections | None
        ) = None
        if execution_runtime is not None:
            execution_runtime.install_debug_sink(self)

    def __setattr__(self, name: str, value: object) -> None:
        if name in self._compiled_facts:
            CompiledContext.__setattr__(self, name, value)
        object.__setattr__(self, name, value)

    @property
    def runtime_source_workspace_projections(
        self,
    ) -> WorkspaceSourceProjections:
        """Hold the context's metadata owners; projection documents remain live."""
        authority = self._runtime_source_workspace_projections
        if authority is None or not authority.is_bound_to_context(self):
            authority = WorkspaceSourceProjections.from_context(
                self,
            )
            self._runtime_source_workspace_projections = authority
        return authority

    def record_completed_step_outputs(
        self, observation: "StepExecutionObservation"
    ) -> None:
        """Own completed persisted facts across step cleanup and worker transfer."""
        from openhcs.core.steps.abstract import StepExecutionObservation

        if observation is self.completed_step_outputs:
            return
        self.completed_step_outputs = StepExecutionObservation.combine(
            (self.completed_step_outputs, observation)
        )

    def release_execution_image_cache(self) -> None:
        """Release image reuse storage without discarding runtime observations."""
        self.runtime_image_stack_cache.clear()

    @contextmanager
    def runtime_step_scope(self) -> Iterator[None]:
        """Own runtime-only values for exactly one FunctionStep invocation."""
        previous = self._runtime_step_values
        self._runtime_step_values = {}
        try:
            yield
        finally:
            self._runtime_step_values = previous

    def runtime_step_value(
        self,
        value_type: type[_RuntimeStepValue],
        *,
        factory: Callable[[], _RuntimeStepValue] | None = None,
    ) -> _RuntimeStepValue:
        """Resolve one declared runtime value shared within the active step."""
        values = self._runtime_step_values
        if values is None:
            raise RuntimeError("Runtime step values require an active FunctionStep.")
        value = values.get(value_type)
        if value is None:
            value = value_type() if factory is None else factory()
            values[value_type] = value
        return cast(_RuntimeStepValue, value)

    def record_runtime_step_outputs(
        self, observation: "StepExecutionObservation"
    ) -> None:
        """Retain exporter-owned output facts within the active step only."""
        from openhcs.core.steps.abstract import StepExecutionObservation

        values = self._runtime_step_values
        if values is None:
            raise RuntimeError(
                "Runtime output observations require an active FunctionStep."
            )
        values[StepExecutionObservation] = StepExecutionObservation.combine(
            (
                self.runtime_step_value(
                    StepExecutionObservation,
                    factory=StepExecutionObservation.empty,
                ),
                observation,
            )
        )

    @property
    def runtime_step_outputs(self) -> "StepExecutionObservation | None":
        """Return derived output facts admitted during the active step."""
        from openhcs.core.steps.abstract import StepExecutionObservation

        if self._runtime_step_values is None:
            return None
        return self.runtime_step_value(
            StepExecutionObservation,
            factory=StepExecutionObservation.empty,
        )

    def install_debug_event_sink(self, debug_event_sink: DebugEventSink) -> None:
        """Install the debug sink selected for this execution context."""

        if not isinstance(debug_event_sink, DebugEventSink):
            raise TypeError(
                "debug_event_sink must be DebugEventSink, "
                f"got {type(debug_event_sink).__name__}."
            )
        self.debug_event_sink = debug_event_sink


DebugExecutionContext.register(ExecutingContext)
