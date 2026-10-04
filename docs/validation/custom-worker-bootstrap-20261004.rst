Custom callable failure at spawned worker bootstrap
==================================================

Owner: Singer. Source investigation at e30ca5783; no frozen author mutation.

Original failure
---------------

The retained BBBC007 fresh96 job10 execution
``cf99c387-9461-4416-a24c-cebdda173ad2`` failed after both axes compiled.
The native traceback shows ``ProcessPoolExecutor.submit`` starting its first
spawned process, then ``multiprocessing.reduction.dump(process_obj, fp)`` fails:
``inspect_seed_cell_identity`` is not the package export's identical object.

Original journal root:
``/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc007-fresh96-after08-20261004/BBBC007_FRESH08_96/author-workspace/output``.
The unmodified ``runtime/mcp.stdout`` records the failure at 66149/66176;
``runtime/data/openhcs/logs/openhcs_zmq_server_port_6016_1791155197649909431.log``
1611--1697 contains the complete native traceback. Registered source is
``runtime/data/openhcs/custom_functions/inspect_seed_cell_identity.py``;
the authored source and pilot pipeline remain original evidence.

Determining relationship
-----------------------

``ValidatedCompiledPlateExecution`` inherits ``ProgressExecutionContext`` but
also owns the untransported pipeline and rich runtime contexts. The execution
coordinator passes that entire object into ``WorkerExecutorFactory`` as a
progress context; the factory stores and passes it as process initializer
arguments. ``_configure_worker_process`` only tests its presence and never reads
its fields. Thus process bootstrap serializes unrelated raw runtime state,
before the separately normalized lane-task payload can run.

The existing custom source namespace, exact source-revision registry and
``FunctionReferenceTransportAuthority`` already own callable identity.
``FunctionStepTransportAuthority`` already owns worker task normalization.
Neither is to be bypassed, copied or replaced. The proposed correction deletes
the unused progress-context input from the original worker bootstrap owner,
its sole production constructor consumer, and focused test consumers. The
progress queue remains the original queue; execution identity remains on the
lane/task owners that actually consume it. No registry, alias, alternate
serializer, timeout, restart or broad reset is introduced.

Owner checks
------------

Current open PRs have no custom callable/process-bootstrap implementation.
PR701 touches orchestrator.py and zmq_execution_server.py, not the proposed
worker_execution.py / compiled_plate_execution.py hunks. Existing issues169/280
concern different serialization boundaries. Dewey retains the original science
runtime; this branch does not submit or replay its job. Whole relevant source
AST and semantic consumer review precede implementation; qualification follows.

Acceptance
----------

Exercise the real spawn executor factory and task transport with one persisted
custom source revision, a decorated typed artifact input and custom measurement
row declaration. Verify the worker resolves that same source revision and
returns the expected tiny synthetic values/rows. Exercise ordinary progress
queue setup, thread/inline/fork resource modes and stale-revision rejection.
A new progress-context subclass carrying deliberately nontransportable runtime
state must need only its own declaration: bootstrap must not consume it.

This initial checkpoint is source diagnosis, not behavioral or installed/native
acceptance. The original failed job and live author's frozen bundle are intact.
