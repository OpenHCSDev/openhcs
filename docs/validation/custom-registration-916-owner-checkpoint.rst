Custom registration: selected owner is not caller admission
==========================================================

Issue916 original00326 remains immutable. Selected native PID1986611,
creation1791240410.93, differed from MCP PID1980094, creation1791240334.24.
The public error alone does not prove source evaluation happened in MCP or
that the native source-bearing exchange had no side effects. The retained
native log contains no corresponding registration traceback from which to
recover the masked original cause. No scientific input was replayed.

Existing ownership and correction
---------------------------------

CustomFunctionRegistrationRequest owns its admitted selected server identity.
CustomFunctionRegistrationHandle.from_request previously called the request's
native-process admission check while projecting an observation handle. Both
the endpoint service's error-receipt comparison and its uncertainty recovery
construct this handle in MCP. A native error or a lost/invalid mutation receipt
therefore produced a new caller/native mismatch, replacing the original cause
with a misleading claim that no source was evaluated (catalog IDEN-7).

The request now owns require_selected_server_identity: it requires a supplied
admitted identity but does not assert that the caller is the native process.
The existing handle projection consumes this operation. No new handle/store,
codec, endpoint fallback, local registration route or retry was introduced.
The native handler and FunctionCatalogService retain require_server_identity
unchanged; observation retains FunctionCatalogOperationHandle.require_current_owner.
Destination, write-path, source-store, preparation and one-shot dispatch guards
are unchanged. All handle consumers inherit the correction from its owner.

Source qualification
--------------------

Production/test pin: 8ffbbd0a0d9b5c407b5918eb340c7b7676defc6f. Normal main
integration used 18f8a10df09908ef539adea80d00f5191d396d1c. The sole add/add
archive-note conflict was resolved to Singer893's merged live acceptance text.
PR910/912 determining source files are disjoint; foreign submodules and existing
untracked bootstrap evidence were preserved.

Existing refactor-audit Package AST parsed all 1409 OpenHCS/test modules with
zero omissions: before403 sites, after415. Native admission has two production
callers, the control strategy and local catalog service. Handle construction
has four production consumers: local result, endpoint error comparison,
uncertainty factory and its own request identity projection. Dynamic service
dispatch is read semantically, not certified by this syntactic inventory.
Published zmqruntime ProcessIdentity remains the PID/creation-time owner.

Original controls01 terminal0: 136 passed in13.27s; whole process18.64s,
peak457532KiB, zero swaps. Files exercised: test_custom_registration_admission,
test_function_catalog_zmq, test_custom_function_lifecycle. Remote-owner success,
native typed error, lost reply, wrong receipt, exact store/path, cold readiness,
no resend, wrong native incarnation and foreign observation rejection passed.
The controls use a pinned Git archive and four unchanged receiving20 native
binaries, with receiving20's installed dependency roots. They are source-family
and generated-MCP controls, not a separate native process/live acceptance claim.

Original evidence root:
/home/ts/wt/openhcs-issue-batch-20260929/engineering-registration-916-20261005
(controls01.log/.time, AST-BEFORE.json, AST-AFTER.json, source-check01).

Remaining installed acceptance
------------------------------

Use one newly recorded synthetic registration through ordinary installed MCP
and an explicitly owned native endpoint: native declaration error must retain
its original cause and native observation handle; a separate valid synthetic
callable must register exactly once, discover, compile and execute with original
raw values and an admitted persisted source. Exact typed closure follows.
Dewey owns released endpoint custody. This is not permission to adopt the
original P001 native/client or to replay original00326; receiving19/20 and
current science remain unchanged. Issue916 remains open pending that path.
