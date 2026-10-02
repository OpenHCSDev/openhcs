Addresses #436.

Working source fix: the original source-inspection binding can report progress
without putting Qt/ObjectState work on an arbitrary worker. It composes the
original progress declaration, extends UiThreadDispatcher with request-context
propagation, and reuses AsyncOperationExecutor/FutureCompletion for SDK I/O
separate from process-main execution. Stdio and resident transports use the
same integration owner. Compiler/kernel/catalog and merged422's client remain
unchanged; no timeout increase, second poller/store/registry or UNKNOWN replay.

Current main902913616 integrated normally. Existing13 progress controls PASS;
new generated-binding/MRO controls are under bounded qualification. The full
working patch and original-evidence links are visible now; receipt tracks
remaining source controls. Parent owns installed cold public qualification.

Original cold inspection remains UNKNOWN; scientific/native/GUI acceptance is
not claimed. Source check bounds: one CPU,512MiB aggregate RSS,60seconds.
