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

Implemented source checkpoint
-----------------------------

The unused bootstrap context has now been deleted from WorkerExecutorFactory,
its stored fields, ProcessPoolExecutor initargs, _configure_worker_process and
the sole execution-coordinator caller. All five factory fixtures migrated;
there is no optional legacy argument or context alias. The initializer now
installs the original queue whenever a queue is supplied. It does not invent a
second execution identity; worker task/lane progress already owns that fact.
Existing executor-resource inheritance and mode-specific hooks are unchanged.
No ornamental capability or new generic consumer type dispatch was needed.

Complete source evidence uses the existing refactor-audit Package/ParsedModule
parser in validation/custom-worker-bootstrap708/source_family.py. At pinned
e3866e0c9 it parsed all701 production modules and705 test modules without parse
omissions;42 production and57 test modules selected for complete relevant AST.
The original Python3.12 process-pool, queues, spawn and reduction dependencies
were also read/parsed. The run completed20.22s,550072KiB maximumRSS, zero swaps.
This is related-family source evidence, not a whole dependency/global R1 claim.

Applicable catalog lessons: IDEN-7 (bootstrap state wider than its actual
question), BOUND-1 (keep boundary interpretation at its original owner), and
TIME-3 (delete the removed argument and migrate consumers, not leave an alias).
No competing export store or copied serializer is added. The error's callable
name does not justify changing the registry when the failing bootstrap input is
the unrelated rich execution graph.

Focused qualification adds a real spawn-factory control to the existing
persisted-custom-source integration fixture. Two durable source revisions,
typed artifact declarations, original helper rows/enums and independent MI
capabilities cross standard pickle; the worker invokes registered functions,
returns nominal rows and emits the terminal progress event on the initialized
queue. A new derived progress context carries an unpicklable local callback
without requiring a bootstrap consumer change.

The existing source bootstrap and receiving08 native tabular source agree:
the original source and this checkout's _tabular_native.cpp both SHA256
15acc82b8ab64268bd1ea4f83fa7a68f527bf317f002e9f39e15be321e03b28e.
The target remained read-only and was not installed or borrowed here. Actual
source checks reused engineering620/source-controls01.py, engineering599's
authenticated source-runtime dependencies and the existing paired interpreter.
The parent bootstrap asserted the unchanged existing build/lib native origin
(binary SHA7de8f671e79263518e56219b30085b2c39c9518db63739298c4ffc9265196aae).
The unchanged checkout also retains its older local binary SHA3c2dc1dcaa4cd8cf7f2c8505a673501de4c79f09372d6fef8fb5c044b6df3d56.
Neither binary was overwritten or rebuilt. These source checks are not whole
installed-package qualification; the future builder owns that byte proof.

Source qualification and original negatives
------------------------------------------

Original controls01 failed collection before execution because the foreign
PolyStore checkout lacks TiffPhotometric. controls02 used the original source
bootstrap:6 factory/initializer controls passed, but the new spawn fixture could
not create its basetemp because the receiving parent directory did not exist.
controls03 reached spawn and exposed the same foreign PolyStore import in the
child before initializer import. The source-only integration fixture now applies
the explicitly borrowed original source-dependency bootstrap at module loading,
before spawn unpickles the initializer, rather than only in __main__. There is
no product test flag or package mutation.

controls04:37PASS,10 deliberately unrelated transport parametrizations
deselected, one original stale cancellation fixture failed before its assertion:
empty SimpleNamespace had no execution_id. That test fixture is now the original
WorkerLaneExecutionContext; the cancellation-before-B01 assertion and visited
A01-only assertion are unchanged. Production at the failing line is byte-identical
to base; no cancellation/product workaround was made.

controls05:2PASS,46 deselected, terminal0,13.21s,310832KiB process maximumRSS,
zero swaps. This checks the migrated cancellation case and actual spawn again
with original child output retained. Worker2476635 resolved both durable custom
sources, executed their tiny2x3 arrays, returned original nominal rows and sent
the original progress event with exact execution/plate/PID, success/100.
The executor context joined; worker2476635 is absent. controls04 already passed
the inline/thread/fork/resource selection, factory initializer, lane planning,
result collection, settlement and normal executor shutdown controls. No fresh
interpreter/catalog/native service, UI/viewer, scientific input or provider ran.
This is real subprocess source acceptance, not public installed execution.
Reported RSS is process high-water, not a combined cgroup memory measurement.

Original R0-01 measures both changed production files against e30ca5783 using
the existing audit Repository/Census/Measure, not a copied detector: no parse
omissions, no positive deltas; none_identity-1, code_lines-5. Dynamic identity
resolution is exercised by the spawn fixture, not asserted from AST alone.
No global R1/dependency-universe proof is claimed. The eight foreign modified
gitlinks and all prior untracked evidence remain untouched and uncommitted.

Remaining installed acceptance
-----------------------------

Planck owns ONE future whole697/709/706 bundle; Singer owns the affected live
receiving with that bundle. Use the original public registered synthetic source,
at least two tiny axis inputs and two spawn workers; validate/compile/execute,
observe native progress and known terminal status, verify expected pixels/rows
through original artifact routes, then exact typed closure. No second client,
overlay, current08 SCI mutation or replay of the retained original job is allowed.
The separate697 first-terminal STATUS/OUTCOMES acceptance remains distinct.
