Multiprocessing coordination
============================

Multiprocessing is coordinated from compiled execution facts rather than from
a second task-planning model.

1. The dataset source discovers the values of the active axis family's
   partition axis.
2. ``PipelineCompiler`` produces a frozen ``ProcessingContext`` for each value.
3. Bundle execution validates the contexts and worker-safe steps.
4. The worker-start policy chooses one multiprocessing context for the entire
   execution.
5. The lane planner assigns the compiled axis contexts to deterministic worker
   lanes. The executor submits one task per active lane and collects a typed
   ``ExecutionResult`` for each axis.

Worker processes install the ``CompiledExecutionBundle`` through
``ForkInheritedWorkerExecutionState``, either inherited at fork or unpickled
from the bundle shipped to a prepared worker. Runtime stores and adapters are
process-local; cross-process state is limited to serialized bundle data,
progress channels, and result messages. Cancellation remains parent-owned:
process workers are terminated by the executor resources that own them, whereas
inline and threaded lanes observe the execution-scoped cooperative cancellation
signal directly.

Generic code must not ask the orchestrator for hard-coded axis names. Axis
identities come from the active ``AxisFamily`` declaration and the dataset
source. See :doc:`component_system_integration` and :doc:`concurrency_model`.
