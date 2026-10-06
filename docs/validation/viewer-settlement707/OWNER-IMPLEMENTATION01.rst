Accepted control reply and claimed settlement correction
========================================================

Implementation owner Dewey, same PR910/issue707. Singer retains read-only
accepted-reply consumer review. This supersedes investigation-only status;
it does not establish P001's historical occupier or installed acceptance.

NapariAcceptedControlRequest now owns a standard Future instead of a blocking
one-entry reply queue. Its completion method contains callback projection and
serialization failures through the existing typed control error response.
Duplicate/late completion cannot block Qt or replace the original response.
Action dispatch consumes that owner. Snapshot dispatch uses the original Qt
capture owner directly; the unused wrapper/projection callback is deleted.
The transport consumes the snapshot request's existing operation deadline:
expiry reports observation failure, NOT cancellation or not-started certainty.
Actions without an existing deadline do not gain a timer or new timeout.

The original layer settlement scheduler terminalizes an exact claimed route
when callback scheduling throws. Completion is inside the existing work-error
boundary. Aggregate-axis declarations, require_terminal and executing-work
retirement protections are unchanged. No state boolean is cleared on timeout.

Existing refactor-audit AST loader enumerated702 production modules plus
installed dependency owners:990 modules, zero parse omissions. Source sites
and consumers were read semantically; dynamic callback coverage is not proved
by AST. This checkpoint migrates the request family and deletes the redundant
snapshot wrapper rather than adding a competing recorder/store/codec.

Qualification status
--------------------

git diff --check passes. Four selected test files use the existing receiving23
installed dependencies and interpreter, with only two candidate runtime files
read-only mounted in a private process namespace. No installed science bytes,
dependency, worktree or environment were changed. First batched Qt observation
39183 exited1 with only three progress dots. Diagnostic observation56455
identified three passing QWidget checks followed by the real VisPy case's
unsupported offscreen QOpenGLWidget/GLX context creation (X BadValue), exit1.
This is preserved as a platform failure, not source or native acceptance.
Observation98605 terminal0:65 passed, one OpenGL case deselected,17.85seconds.
The accepted callback error and late queued snapshot controls passed on real
Qt with installed dependencies. No scientific/native request is replayed.
New checks cover deferred projection failure and original snapshot deadline
with late queued Qt work. Full installed public native/control acceptance is
still pending. Source tests alone will not be described as that acceptance.

Eight foreign gitlinks and four untracked validation directories are preserved.
All live science operations and receiving23 backers remain immutable.
