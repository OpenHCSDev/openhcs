Progress and Debugger Runtime Projection System
================================================

Scope
-----

This page documents the OpenHCS implementation path only.

The generic progress registry and projection mechanisms live in
``zmqruntime.progress`` and are documented in the ``zmqruntime`` docs. OpenHCS
owns the microscopy-pipeline event vocabulary, execution-tree semantics, and
retained debugger state layered over those mechanisms.

OpenHCS Implementation Path
---------------------------

OpenHCS-specific modules:

- ``openhcs.core.progress.types`` owns the ``ProgressStream``, ``ProgressPhase``,
  and ``ProgressStatus`` class families carried by ``ProgressEvent``; each phase
  owns its stream and terminal semantics.
- ``openhcs.core.progress.registry`` owns OpenHCS semantic keying over the generic
  registry.
- ``openhcs.core.progress.projection`` and
  ``openhcs.core.progress.runtime_tree`` own the OpenHCS execution and tree
  projections.
- ``openhcs.core.progress`` emits worker events through the configured progress
  queue. ``openhcs.runtime.zmq_progress`` constructs execution-server events and
  owns the compiler queue adapter.

Consumption path:

1. Emit typed ``ProgressEvent`` values from compile/execute flows.
2. Route events through explicit queue wiring via ``set_progress_queue(...)``.
3. Register events in ``ProgressRegistry`` keyed by subject, axis, and stream.
4. Reconcile typed server-heartbeat running/queued entries by execution and
   subject identity in ``ExecutionRuntimeProjection``.
5. Build runtime and execution-tree projections for status derivation.
6. Coalesce registry mutations in the session's ``ExecutionProgress``: each
   mutation marks the projection dirty, and the session's main thread rebuilds
   it at most once per interval and publishes it as session events.
7. Render the same projection in the Plate Manager (through session events) and
   the ZMQ server browser.

OpenHCS Invariants
------------------

- The execution tree path is ``subject -> worker -> partition -> step``.
- ``PatternGroupProgressPhase`` is step-detail only and does not set partition pipeline
  percent.
- Subject/server status is derived from projection snapshots, not mutable cache.
- Event retention is monotonic per semantic key. Stale or duplicate timestamps
  are rejected before listeners and typed side-effect consumers run.
- Topology is reconstructed from the retained event snapshot. A late subscriber
  may render a shallow lifecycle node when the initialization event is absent.
- Each ``SubjectRuntimeState`` subclass owns its status label, count label,
  terminal policy, and live-server transition policy. ``state_counts`` is the
  only retained count projection; per-state count fields are forbidden.
- Runtime identity is ``SubjectRuntimeIdentity(execution_id, subject_id)``. A
  new queued execution may replace an older visible execution for the same
  subject without conflating their retained histories.
- A background progress callback may only dirty the retained projection.
  Rebuilding and rendering run on the client's main thread.

Debugger ownership
------------------

Debugger execution uses the normal progress transport but does not reduce its
retained state to status text:

- Each ``DebugCommandType`` subclass is one command and owns what it does to a
  paused worker; the execution and stop strategy families, keyed by command
  class, implement command-specific bounded-run behaviour.
- Each ``DebugBoundary`` subclass is one boundary event and owns its progress
  status and whether it reports output artifacts or carries an exception.
- ``DebugCursor`` and ``DebugSession`` retain the exact invocation and controller
  identity. ``DebugSnapshot`` retains boundary evidence, and ``DebugArtifactRef``
  plus ``DebugArtifactIdentity`` retain typed artifact provenance.
- ``DebugExecutionPolicy`` installs the selected event sink and controls bounded
  execution, replay, axis selection, and the debugger-specific execution shape.

These are nominal authorities in ``openhcs.core.debug``. Consumers query their
registries and typed values; they do not maintain command lists, event tables, or
parallel debugger state machines.

Debugger projection path
------------------------

``ProgressDebugEventSink`` encodes a ``DebugProgressContext`` in an ordinary
``ProgressEvent``. ``RuntimeProjectionBuilder`` then builds the normal execution
projection and the debugger projection from the same immutable event snapshot.
``DebugRuntimeProjectionBuilder`` filters events by debug session, resolves their
snapshots, and derives the current and last frames while retaining the
normal execution projection beside them.

The runtime projection is not the session-state machine. Given the selected
target, active session, manager execution state, terminal summary, pause state,
and snapshots, ``DebugSessionPhase.for_context`` selects the current debugger
phase. Toolbar, inspector, UI-bridge, agent, and MCP-facing adapters consume that
typed session context and projection instead of re-deriving phase semantics.

Snapshots, replay, and inspection
---------------------------------

``DebugSnapshotStore`` is the registered storage boundary for snapshot metadata;
its concrete stores select local or FileManager-backed persistence. Snapshots
refer to artifacts rather than embedding bulk runtime arrays. Artifact reads and
exports therefore remain explicit, bounded operations.

Warm replay validates skipped outputs through
``DebugWarmReplayArtifactReusePlan``. It matches the exact compiled artifact
plans and stable ``DebugArtifactIdentity`` values, then either finds or hydrates
the required values through the runtime store. It does not infer reusable outputs
from generated names. Persistent paused-worker mode instead retains the live
``RuntimeValueStore`` behind ``DebugPausedWorkerController`` and exposes a typed,
read-only inspection view while the worker is paused.

Other typed-progress consumers
------------------------------

The headless session registers progress exactly as the GUI does: one
``ExecutionProgress`` owner per session rebuilds the runtime projection and
publishes it as session events. ``openhcs_session_events`` returns those events
past a sequence number, blocking until one arrives, and
``openhcs_session_datasets`` reads each dataset's runtime state, so a caller can
tell continuing activity from a stall without polling.

Live measurement previews are a sibling consumer of the progress stream, not a
debugger projection. ``LiveMeasurementProgressPayload`` places bounded typed
measurement previews in event context, and the live-measurement notification and
window services retain their own UI projection. They do not consume debugger
command declarations, debugger snapshots, or debugger session phase state.

Axis completion is not plate completion
---------------------------------------

Workers execute only axis-scoped steps. ``AxisCompletedProgressPhase`` reports
the number of completed axis positions and deliberately stops at the first
terminal plate-scoped step. It is a successful terminal event for that
worker/axis key, but it does not assert that the plate execution has finished.

After every worker result succeeds, the parent merges runtime records and calls
``execute_dataset_scoped_steps()``, which runs each terminal plate-scoped step
once. The parent
then materializes those outputs, runs analysis consolidation, settles viewer
state, and projects the orchestrator result. Only after those stages succeed
does it emit the pipeline ``SuccessProgressPhase`` event at 100 percent.
Failure, cancellation, viewer settlement, or terminal-step errors therefore
cannot be hidden behind an earlier worker ``AxisCompletedProgressPhase`` event.

Abstraction Docs
----------------

See the published ``zmqruntime`` owner documentation for abstraction internals:

- `Progress Registry and Projection
  <https://github.com/OpenHCSDev/ZMQRuntime/blob/v0.2.11/docs/source/architecture/progress_registry_projection.rst>`_
- `ZMQ Execution System
  <https://github.com/OpenHCSDev/ZMQRuntime/blob/v0.2.11/docs/source/architecture/zmq_execution_system.rst>`_

Related OpenHCS Pages
---------------------

- :doc:`batch_workflow_service`
- :doc:`zmq_server_browser_system`
- :doc:`concurrency_model`
- :doc:`runtime_value_system`
