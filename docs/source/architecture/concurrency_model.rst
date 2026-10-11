Concurrency model
=================

OpenHCS compiles the selected execution axes before starting workers. A
``CompiledExecutionBundle`` carries the worker-safe steps, frozen
``ProcessingContext`` instances, and environment decisions for one dataset.

Execution units
---------------

The active family's partition axis yields one context per value; in the
microscopy family that is one context per well. Source discovery determines the
available axis values; compiler stages create the corresponding typed step
plans. Each worker executes one lane, the compiled contexts of the partition
values it owns, one context at a time, and never shares mutable compiler state.

Each frozen ``ProcessingContext`` owns its multiprocessing ``axis_id``. Mapping
keys distinguish runtime contexts, including sequential combinations, but do
not encode an axis contract. Bundle projections and worker-lane grouping read
the context-owned identity instead of parsing those keys.

``bundle_execution`` owns the execution lifecycle of one compiled bundle.
``worker_execution`` owns executor construction, bundle installation, task
submission, result collection, cancellation, and cleanup; process workers serve
a typed ``WorkerCommand`` family over their connection to the parent.
``worker_lanes`` provides the process-local bundle authority used by worker
code.

At execution, each context binds its ``WorkerLaneExecutionContext`` directly.
The lane identity references the execution's worker-assignment mapping, without
carrying other workers' processing contexts. Progress projects the current
lane's owned partition values; streaming projects the complete assigned axis domain so that
every worker declares the same viewer coordinates. ``ProcessingContext`` does
not retain separate copies of the lane's execution, dataset, worker, or
ownership fields.

Start-method policy
-------------------

``resolve_worker_start_context`` is the single policy for ``spawn``, ``fork``,
and ``forkserver`` selection. It considers the requested method, platform,
server mode, and whether compiled plans require a GPU. GPU execution and macOS
default to ``spawn`` unless an explicit unsafe override is allowed.

Progress and cancellation
-------------------------

Workers emit typed progress events to the execution's progress queue; process
workers forward them over their parent connection. The parent and ZMQ
runtime project those events for UI consumers. ZMQRuntime owns the terminal
execution status and applies cancellation only to the requested execution.
OpenHCS owns an execution-scoped cancellation authority: inline and threaded
lanes check it between contexts, steps, and axes, while process execution stops
owned worker processes. A callable already in progress reaches its next safe
boundary before stopping. Cancellation never becomes success or failure when
late worker completion or an exception reaches the server, and every path still
runs cleanup.
Worker ``AXIS_COMPLETED`` events close only the axis-scoped portion. Terminal
dataset-scoped steps, post-execute hooks such as the microscopy domain's output
consolidation, viewer settlement, and final state projection remain
parent-owned; :doc:`progress_runtime_projection_system` defines the
separate final ``SUCCESS`` boundary.

Invariants
----------

- compile all selected axes before executing any of them;
- create every multiprocessing primitive from the same resolved context;
- pass typed bundles and values, not reconstructed path dictionaries;
- keep compiler state in the parent and immutable runtime state in workers;
- make success, failure, cancellation, and broken-pool paths converge on cleanup.

See :doc:`pipeline_compilation_system`,
:doc:`progress_runtime_projection_system`, and
:doc:`orchestrator_cleanup_guarantees`.
