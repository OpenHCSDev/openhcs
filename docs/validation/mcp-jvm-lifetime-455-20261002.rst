MCP process-resource lifetime, issue 455
======================================

Owner and current checkpoint
----------------------------

Dewey owns MCP process lifetime. Parent owns installed qualification. Base is
merged main b68029c0cfc017c5a4b086bc607bff3c0bec6c01. Root394 compiler/runtime,
PR404 result publication and PR454 viewer presentation files are untouched.
This working draft has not yet qualified a live JVM shutdown.

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
its TypeError is retained here, not presented as a completed audit.

Acceptance still pending
-------------------------

Bounded source controls must cover declared callback closure on the main thread,
cooperative close, error propagation/idempotence, ordinary EOF versus stuck-child
escalation and exact child exit status. Parent installed qualification must compare
a fresh health-only session and one distinct read-only physical query session,
then close each and retain exact exit codes and complete diagnostics. Shared Fiji
is reused with downloads disabled. No biological/native execution or viewer launch
is part of this acceptance.
