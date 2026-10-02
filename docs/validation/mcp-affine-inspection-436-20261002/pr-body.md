References #436; archives the completed technical checkpoint merged in PR438.

Working source fix: the original source-inspection binding can report progress
without putting Qt/ObjectState work on an arbitrary worker. It composes the
original progress declaration, extends UiThreadDispatcher with request-context
propagation, and reuses AsyncOperationExecutor/FutureCompletion for SDK I/O
separate from process-main execution. Stdio and resident transports use the
same integration owner. Compiler/kernel/catalog and merged422's client remain
unchanged; no timeout increase, second poller/store/registry or UNKNOWN replay.

Production08054fccf is merged at4d48ded6570ed0730dc8d6437ae130ab48e3ca47.
This follow-up changes only tests/validation evidence: **no production drift**.

- 26 generated/Qt-affinity/ContextVar/cooperative-MRO/resident controls PASS.
- Whole-scope real SDK stdio success/error progress PASS (387688KiB/11.829s).
- Actual generated binding/original compiler staged-field controls: 2 PASS.
- Unchanged original scoped R0, main902913616→08054fccf: PASS, zero positive deltas.
- Original bootstrap source-admission red retained and corrected through the
  existing stdio test owner; 1 PASS, no assertion weakening or added skip.

Parent's ordinary private installed fresh public health/guides/source artifact
inspection PASSes with unchanged10s idle: errors[], A01/file1/step1,
DeclaredSyntheticNlm/progress1. Original flag-parse/missing-binding attempts and
assisted5 UNKNOWN remain retained; no request replay or science/native/viewer
launch. Exact external evidence links/hashes and full R0 archive are in receipt.

Original cold inspection remains UNKNOWN; scientific/native/GUI acceptance is
not claimed. Source check bounds: one CPU,512MiB aggregate RSS,60seconds.
