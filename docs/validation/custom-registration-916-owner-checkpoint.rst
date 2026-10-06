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

Installed public acceptance and closure
---------------------------------------

Ordinary receiving21 pins eaf161df38147f5834f41e10cf1be8a81235fc80,
wheel SHA256 88f1aeaea5baeb4225a0deab9d6b067350aec47482aedf868fa371547590e32f.
Whole wheel RECORD/source and 13 managed skill files qualified; fresh MCP
health and context retrieval passed. No shared environment was altered.

Original persistent client02 handle66578 selected freshly owned native2281416,
creation1791245041.4, TCP6022 on released display89; MCP2281333 was distinct.
No viewer or science session was adopted. One deliberately undecorated source
returned the native ValidationError (zero decorated functions) and the correct
native observation handle, rather than masking it with MCP/native mismatch.
Read-only observation returned not_observed; that alone is not proof of no
mutation. The separate valid registration_probe916 source was submitted once,
registered once and persisted byte-identically (SHA256
fc86957e0d4e6972a9f501b68543b4454f81da3742a51a703bf340d9d7e1ecce).
Public discovery described its declared PURE_3D contract and image output.

Original pipeline01 incorrectly selected ImageXpress for loose synthetic TIFFs
without mandatory HTD metadata. Its compile refusal remains preserved. Distinct
pipeline02 uses the existing SOURCE_BINDINGS handler, LazySourceBindingsConfig,
filename metadata extraction and a named Fixture binding. Public artifact-plan
compiled all four source planes Z0..3. One execute-source request created
session-1/job-1, execution ede25c2f-9062-444a-9d8e-ea2c4e231838, and completed
with errors empty. Saved four uint16 5x7 planes exactly equal z*100+y*7+x:
140 original pixels preserved; original input hashes are unchanged.

Exact typed close acknowledged endpoint termination and process_exited=true
for native2281416/1791245041.4. Native and MCP PIDs were independently absent;
6022/7022 had no listeners. Original client66578 terminal1 is the aggregate
disposition of retained tool errors, not a failed typed close. The recorder
ended normally with COMMAND_EXIT_CODE=1. First client97487 terminal2 retains
predispatch syntax errors and a lock-file path admission refusal; it never
returned a native handle. Client02 admits only the exact owned transport lock
paths through the existing launch owner. Nothing uncertain was resubmitted.

Other retained negatives: incorrect observation driver argument, catalog ping
refusal while registration refreshed the catalog, and pipeline01 metadata
refusal. Explicit same-owner catalog preparation later returned READY; no
registration was repeated. These are not fabricated all-tools-pass receipts.

Evidence root:
/home/ts/wt/openhcs-issue-batch-20260929/engineering-registration-916-20261005/public-case01
contains both original journals, both pipeline revisions, PUBLIC-REPLIES02.json,
PIXEL-VERIFICATION02.json, original sources, persisted source and TIFF outputs.
Final journal SHA256s: stdin99e46a51f9a496332781b44a73568c8742ff2e8ce891e083429ba0eb1b4b37d1,
stdout3e2212cd13274c75cd4555425ad9c4adb1ea55ee5f961cfcf8bfa207bed6305a,
timingb467465b2b4e7b0b0ab87dfab85bb8c74a2281fc64f66240badcad38f19b6f47.

Normal final main integration used 354be9f9f; determining changes do not touch
the registration DTO or endpoint projection owner. Installed acceptance
qualifies the unchanged registration owner hunk, not those later unrelated
measurement changes. Issue916's caller-side error projection is repaired;
the original00326 native cause remains unknown and was never replayed.
Receiving19/20 and live scientific authors remain unchanged. Lane89 is released.
