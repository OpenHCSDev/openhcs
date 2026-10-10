Compiling and running datasets
==============================

The session (:doc:`plate_manager_services`) compiles and runs datasets for every
client the same way.

Compile-only flow
-----------------

1. ``CompileDatasets`` checks that every target is initialised, idle and has a
   pipeline, then the session reserves the targets as compile-pending.
2. Each dataset's ObjectState is snapshotted into a ``DatasetPipelineRequest``.
3. ZMQRuntime's ``BatchSubmitWaitEngine`` submits every compile job and waits
   for the results; each success is stored as a ``CompiledDataset`` with the
   compiler's artifact inspection.

Other datasets stay editable while one compiles or runs; mutation guards
protect only the datasets whose work owns their orchestrator.

Run flow
--------

1. Reserve the execution batch before connecting to the server.
2. Reset that run's progress and snapshot a request for every dataset.
3. Compile every request before submitting any execution, so a batch never
   starts partially.
4. Submit each execution with its exact ``compile_artifact_id``; an optional
   runtime observation export rides on the same submission.
5. Follow each execution to its terminal status and converge the dataset state,
   the output dataset (when the run asks for it) and the batch summary as
   session events.

Lifecycle
---------

``ExecutionProgress`` owns the session's one registry-mutation listener.
Progress messages only mark the projection dirty; the session's main thread
rebuilds it at most once per progress interval and publishes it. The session
owns its execution client for its lifetime; configuration changes, explicit
server shutdown, failures and ``Session.close`` own disconnection. In the GUI
the server browser's endpoint snapshot is bound to the session as its endpoint
status, which selects whether the compile button connects or compiles.

See :doc:`progress_runtime_projection_system` and :doc:`zmq_server_browser_system`.
