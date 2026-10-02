MCP process-resource lifetime, issue 455
======================================

Owner and current checkpoint
----------------------------

Dewey owns MCP process lifetime. Parent owns installed qualification. Base is
merged main b68029c0cfc017c5a4b086bc607bff3c0bec6c01. Root394 compiler/runtime,
PR404 result publication and PR454 viewer presentation files are untouched.
Production checkpoint is d3a07da38. This draft has not yet qualified a live JVM
shutdown. Addresses #455 without auto-closing its installed acceptance.

Original witness
----------------

Issue https://github.com/OpenHCSDev/openhcs/issues/455 retains successful public
responses followed by ``JPJavaFrame 49`` fatal teardown diagnostics. Original
engineering-453-live02 requests SHA is
e7d6c000907a7ff8dafc88846b1ab55f93a9c72f19d7f119ea899cdfc54ad207;
diagnostic SHA is
ae4d9968ccd5c88689af614b2a3b76c599b1840dd2ddbbc82252316e2e59146e.
The original driver exited zero, but the MCP child exit code was not retained.
No original query, journal or scientific input is replayed or changed.

Original native crash report, independently read
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The original report remains at
``/home/ts/wt/openhcs-issue-batch-20260929/carrier434-installed-20261002/hs_err_pid3996424.log``.
Size is 435048 bytes; SHA256 is
3736ac983126c24b8d89e114d21275f032f49be4b867348696b602d1bb108605.
No full report or original input is copied into this checkout.

Its header confirms SIGSEGV in the exact original MCP3996424, main thread
3996424, at Fri Oct 2 08:23:14 2026 EDT, OpenJDK21.0.7+6-LTS. The problematic
frame is ``JPypeException::toJava() [clone .cold]+0x6b`` in the original
``_jpype.cpython-312-x86_64-linux-gnu.so``. Java frames identify
``TypeFactoryNative.newWrapper`` and ``JPypeContext.newWrapper``. The process
thread section also contains a Java ``SIGTERM handler`` thread. This proves a
native JVM/JPype crash, not merely a fatal-looking diagnostic.

The SIGTERM handler is consistent with the original client's unconditional
``process.terminate()`` immediately after EOF. It does not uniquely establish
the failing exception's origin, Python finalization state or the causal sequence.
The header signal is not an observed subprocess return code: JVM fatal handling
may change the terminal signal. Original child exit remains unobserved. The
already-published patch removes premature termination and reaches original
process-resource shutdown on main; actual JVM-close acceptance remains pending.
Parent's separate454 process and its eventual exit disposition are independent.

Reason-first ownership trace
----------------------------

``McpDevStdioSession.__aexit__`` closed stdin then immediately terminated its
child, preventing ordinary EOF-driven cleanup. ``McpTransportExecutor.close``
only released dispatch/execution infrastructure. Both original stdio and
resident server close consumers call that shared owner on the process main
thread. Neither called PolyStore's registered process-resource cleanup.

PolyStore already owns the exact chain: ``cleanup_backend_connections`` with
``include_process_resources=True`` calls registered resource callbacks;
``BioFormatsJavaContext.shutdown_instance`` detaches its original singleton;
``ImageJRuntimePolicy.shutdown`` disposes the gateway and calls scyjava;
scyjava calls JPype. JPype explicitly requires the process main thread.
The existing native execution server uses this same PolyStore entrypoint.
No JVM shutdown policy, context, callback roster or algorithm is copied.

The MCP executor now invokes that owner before interpreter finalization, after
its original cooperative ``super().close()``. Its inherited closed state owns
idempotence; failures propagate. The dev client gives EOF and graceful child
exit one shared existing two-second teardown budget before existing escalation.
The existing two-second termination budget is unchanged. No request timeout,
JVM flags, signal handler, compiler placement or diagnostic suppression changes.

Catalog review: IMPL-12/IMPL-13 reject copying shutdown or process supervision;
TIME-7 rejects copying dependency defaults. Extensibility is the original
``register_cleanup_callback`` declaration, not a new MCP registry.

Before-edit census
-------------------

``validation/jvm455-owner-before-corrected.log`` uses existing audit
``ParsedModule``/``measure_source`` and NRA ``PythonEnumBaseAuthority`` across
the whole OpenHCS production root and actual readonly dependency roots. Those
roots were resolved by the paired interpreter, including ObjectState's actual
basicpy-live-candidate backing, not a guessed source checkout. Import, inheritance,
call, write and decision sites were read semantically. Dynamic import effects,
callback timing and JVM internals are not established by static parsing.
The first census invocation used the wrong ``measure_source`` signature;
its TypeError is retained here, not presented as a completed audit. The full
before/after closure in ``validation/jvm455-owner-closure.log`` also includes
the actual external MCP SDK root, absent from the first root list. Before source
comes from the exact Git base; after is the current production patch. Dependency
sources are readonly and unchanged. Static parse completion does not prove all
dynamic resolution or actual JVM shutdown.
The completed census parses 1177 modules per snapshot: OpenHCS 703, PolyStore
63, pyqt-reactive 193, zmqruntime 32, JPype 31, scyjava 11, imagej 7, MCP SDK
110 and ObjectState 27. Zero actual parse omissions in either snapshot.

Bounded source qualification
-----------------------------

One CPU, aggregate RSS below 512 MiB and wall below 60 seconds for each serial
shard, using the original scope monitor and readonly paired Python3.12:

* ``jvm455-lifetime-first.log``: 11 PASS, 472832 KiB, 11.587 seconds. Six new
  lifetime cases and five unchanged established-session/no-replay controls.
  Tests exercise original context detachment/gateway disposal, main-thread JVM
  call, independent registered resource, cooperative MI close, duplicate callback
  registration/idempotence and propagated failure. Off-main close is rejected
  before resource release. Real child processes retain exact EOF exit 0 and 7;
  a stuck child reaches SIGKILL using unchanged two-second budgets.
* ``jvm455-resident-first.log``: 1 PASS, 467588 KiB, 7.659 seconds. Two real SDK
  connections reuse the resident server; disconnect never releases the process
  resource. Original server closure releases it once on main.
* ``jvm455-sdkstdio-exactsource.log``: 2 PASS, 387788 KiB, 7.634 seconds. Real
  FastMCP/stdio SDK initialize, two successful health requests, EOF and registered
  cleanup, then exact child exit 0 (success) or 1 (original cleanup error).
  Child import root is explicitly derived from original runtime import authority.

The two earlier standalone SDK attempts remain RED. First omitted original
native ABI admission and failed import. The second launched its arbitrary test
script through a spec which, correctly, does not carry PYTHONPATH; it therefore
loaded installed source rather than the owned patch, exited 0 but did not write
the required resource-close marker. The corrected test proves its child source
identity. No production fallback, assertion weakening or installed-package edit
was used to repair either harness failure.

Acceptance still pending
-------------------------

Parent installed qualification must compare
a fresh health-only session and one distinct read-only physical query session,
then close each and retain exact exit codes and complete diagnostics. Shared Fiji
is reused with downloads disabled. No biological/native execution or viewer launch
is part of this acceptance.

``docs/validation/mcp-jvm-lifetime-455-20261002/qualify.py`` is ready for parent
invocation with explicit installed root and a fresh evidence directory. Invoke
once without ``--plate-path`` for health-only, and separately with the approved
readonly physical plate for inventory. It uses the original public dev client,
generic ten-second request idle policy, no resident adoption, no poller and no
mutations. Complete diagnostics, original requests/replies and exact child exit
are retained even if a request or shutdown assertion fails. Parent retains the
shared Fiji/no-download and serialized live-resource admission policy.

Original scoped R0
-------------------

``validation/jvm455-pinned-r0-first.log.gz``: PASS, zero positive deltas,
180980 KiB aggregate RSS, 15.974 seconds. Unchanged original tool comes from
agent-comms Git 3b03785f45df2ef5dc62ba6aed99294192ecbb01, with actual Python3.14
and readonly basicpy-live-candidate metaclass backing. Exact comparison is
main b68029c0cfc017c5a4b086bc607bff3c0bec6c01 to production
d3a07da381df6bf66b4563ed08667960dd43af9b, scope ``openhcs``; two changed
production files. This is scoped R0, not global FULL/R1 qualification. Later
tests and evidence do not change production. No completed453/443 gate rerun.

Storage and remaining blocker
------------------------------

Existing WT and readonly dependency environment reused. Owned scratch totals
about 140 KiB across lifetime/resident/corrected-SDK cases; failed marker evidence
is preserved. No cleanup, new worktree, environment, download or installed byte
change. Source ownership and bounded controls are ready; live health-only versus
physical inventory/JVM-close acceptance, exact child exits and fatal-diagnostic
absence remain parent-owned and unqualified by these source controls.
