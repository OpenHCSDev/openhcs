Plate Manager batch workflow
============================

``PlateManagerBatchWorkflow`` is the OpenHCS-owned facade for Plate Manager
compilation, execution, debug runs, progress projection, and cleanup. It lives
in ``openhcs/pyqt_gui/services/plate_manager_batch_workflow.py``.

Composition
-----------

The facade creates a ``BatchWorkflowContext`` and a lazy
``BatchWorkflowComponents`` registry. The component owner constructs focused
services only when the workflow needs them:

- ``CompileBatchWorkflowService`` owns compile-only batches and the
  compile-before-execution policy;
- ``CompileWorkflowService`` submits and waits for one compile request;
- ``PlatePipelineRequestBuilder`` projects current plate/UI state into
  ``CompileJob`` and ``RunSpec`` declarations;
- ``ExecutionSubmissionService`` submits compiled runs and owns terminal
  polling callbacks;
- ``ExecutionControlService`` owns cancellation, disconnection, and failure
  convergence;
- ``ProgressWorkflowService`` projects the shared progress registry and server
  status into UI updates;
- debug and live-measurement notification services project their corresponding
  progress events.

This is composition of nominal services, not one monolithic
``BatchWorkflowService`` class.

Compile-only flow
-----------------

1. ``CompileBatchWorkflowService`` admits and reserves only the selected plates.
2. The request builder projects their saved declarations into ``CompileJob``
   values without replacing an active execution batch.
3. ZMQRuntime's ``BatchSubmitWaitEngine`` submits all compile jobs and waits for
   their results.
4. Successful compile artifacts are stored by plate and exact execution ID;
   completion releases only that compile request's reservation. Progress is
   reprojected from the current runtime owner.

Other plates remain available for initialisation, configuration and code editing
while a plate runs. A compile request may queue behind the active server job;
admission does not promise simultaneous server execution. Mutation guards protect
the exact plate whose initialisation, compilation or execution owns its live
orchestrator. Shared global changes and collection-wide replacement are guarded
when they would affect that work.

Run flow
--------

1. Admit the selected plates and reserve the execution batch before awaiting
   endpoint connection.
2. Reset that run's progress and build a ``RunSpec`` for every selected plate.
3. Compile every run spec before submitting any execution.
4. Submit each execution with its exact ``compile_artifact_id``.
5. Start completion polling and converge completed, failed, or cancelled state
   through the submission/control services.

The compile-all-before-execute invariant prevents a partially started batch
when a later plate cannot compile.

A later standalone compilation supersedes the selected member's terminal row
activity through the existing batch-member lifecycle. The batch's historical
success/failure counts remain intact, including while a sibling is still running.

Lifecycle
---------

``ProgressWorkflowService`` owns the Plate Manager's one registry-mutation
listener and removes it during ``cleanup()``. The execution client remains the
single progress-stream subscriber. Registry mutations only mark the projection
dirty from producer threads. The coalescing timer is started explicitly while
the Plate Manager is constructed on the Qt application thread, and that timer
is the sole owner of projection rebuilds and row refreshes. Running, completion,
and debugger snapshot notifications cross background boundaries through Qt
signals before widget mutation. The Plate Manager host owns UI state; component
services derive and update it through explicit callbacks.

The GUI owns its shared execution-client session for the Plate Manager lifetime.
Successful compile and run completion therefore leave that client connected;
configuration changes, explicit server shutdown, failures, and widget cleanup
own disconnection. Cleanup invokes the client owner even before application
admission, so an in-progress startup attempt is cancelled and its exact child
processes are reaped. ZMQRuntime reports that owner-requested path through its
typed connection-cancellation result rather than an endpoint-failure string.
The server browser's immutable endpoint snapshot is the
single input for the configured endpoint's browser row and dedicated status
indicator. ZMQRuntime's ``EndpointClientSession`` owns client admission and
connection state; browser-driven endpoint termination explicitly retires that
session. Startup events update the browser snapshot rather than writing a
parallel connection status. After the initialized desktop first paints, the
batch workflow uses the configured persistent endpoint policy to attach to a
compatible ready server or start one when none is available. Once that endpoint
is ready, the desktop prewarms the endpoint-owned callable catalogue in the same
background operation. The Function Selector and local MCP authoring context use
the same endpoint service; selecting a callable transports its exact reference
instead of reconstructing the complete catalogue in either consumer. Opening
the Function Selector requests a current endpoint projection or joins an
in-progress asynchronous request. The endpoint retains its prepared registry;
the GUI does not treat a completed snapshot as proof of current membership.
Endpoint preparation and catalogue discovery do not block the Qt thread.
Endpoint discovery remains owned by the server browser.

See :doc:`plate_manager_services`, :doc:`progress_runtime_projection_system`,
and :doc:`zmq_server_browser_system`.
