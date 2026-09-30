# Issue264 source-only extension and materialization checkpoint

Implementation/file owner: Socrates, sole PR262/issues257+264 owner. Parent is
integration/live-verification owner; Lovelace owns R0/PR263, Zeno205 measurement.
No R0, L0 or S-surface implementation is included. Frozen H002B and held-out/
reference data are untouched. No original native request/job is replayed.

## Observed cause and shared authority

The original259-02 execution `30940da2-fbba-48b0-9824-32ace7747fe5` at
`5c1adc9c629433159d5809834c061fec656f1598` invokes the image-file writer,
not only a ROI archive writer. The saved input metadata contains an ordinary
primary-plane projection with native dtype/intensity metadata but empty source
provenance. Its separate source metadata declares all five address components,
but no extension. The loader supplies a source identity; the workspace join
then replaces it with the header-only persisted metadata, retaining geometry/
intensity but losing provenance. Output context supplies components without
recovering that lost source path/extension; materialization's strict guard
correctly rejects the incomplete identity.

Independently reproduced: `SourceImageIdentity.with_missing_from` retained
missing axes but discarded a declared extension whenever both identities
already carried component metadata. This affects scalar-plane consensus,
parsed external source identity, artifact provenance joins and component-only
filename identity. Five red cases at the prior PR262 head proved these losses;
two existing-extension/strict-rejection controls already passed.

264 and257 therefore share retained source filename facts, not a TIFF default
or a filename-regex repair. `FunctionOutputExtensionAuthority.from_metadata`
now consumes `SourceImageIdentity.filename_extension`, the same declared fact
retained by source-identity joins. No new parser call is introduced.

## Implemented owners

- `SourceImageIdentity.filename_extension` projects the explicitly supplied
  filename fact through the existing source metadata lookup owner. Missing
  identity/extension stays missing. Its existing component join retains that
  fact only when absent; authoritative extensions/axes and unrelated metadata
  are preserved. Unknown foreign metadata is not merged.
- `VirtualWorkspaceImagePayloadProjection` takes ownership of the former
  workspace static helper and deletes it in place. Its metadata join retains
  loaded source context only for a native header that declares neither scalar
  identity nor planes/contributors. Intentional collapsed or incomplete
  provenance remains authoritative. Geometry, dtype, aliases and masks use
  existing metadata mechanisms; no duplicate store or protocol reader.
- `SourceComponentMetadataStemAuthority.required_extension` and the strict
  FunctionStep missing-extension guard are unchanged. No guessed extension,
  coordinate, generated-path reparse, source-binding weakening, filter bypass,
  public function algorithm change or alternate scientific processing.

55 old production lines are deleted/replaced in this264 delta (the projection
helper moved, not a second path). Oversized `SourceImageProvenance` stays639
lines, unchanged; `VirtualWorkspaceSourceProjection` shrinks below500. New
payload-projection owner is53 lines. This is a bounded bug-owner extraction,
not a certificate for the full source surface.

## Ownership crossing and architecture limits

Direct shared-file notice was addressed to parent integration in the active
conversation before the product edit. Checked published PR205 and PR263 and
the merged259 source: none touches this delta's provenance/workspace owners.
No config/compiler edit. No foreign tree or unpublished worker files inspected.
The default agent-comms route did not contain Socrates/Lovelace/Zeno, so no
direct-worker delivery through that route is claimed. Any unpublished overlap
needs the affected file owner's direct reconciliation, not another coordinator.

Known additional presence: `openhcs-architecture-memory` records a continuity/
standby role, not an active S-surface implementation. No additional OpenHCS
surface-refactor implementation owner was verified. NRA-project agents are not
OpenHCS surface assignments.

Current NRA/refactor-audit instructions and R0 OWNER-OVERRIDES/rules read.
BOUND-2/4 and IDEN-1/5: facts stay on the identity declaration; consumers derive
views. The existing projection helper is replaced by one typed behavior owner.
No giant-class growth, foreign capability probes or parallel registry added.
The R0 R1 script was read but not executed: it materializes/analyses full
OpenHCS/dependency source context and is outside this light source-only budget.
Packaged `agent-comms-ratchet` is absent; no download/install attempted. This is
source tracing plus local AST class-size checks, not a full NRA/ratchet pass.
Hosted CI is not a waiting gate; actual enforced integration rules remain.

Persisted formats: all unchanged. Existing OpenHCS metadata/source-projection
schema, PipelineDocument, TIFF/ROI/CSV and MCP protocols unchanged; no adapter,
version, migration or reset introduced.

## Fixture evidence and remaining acceptance

Fresh checks:28 provenance/persisted-metadata/264 tests,6 existing image/ROI
materializer tests,16 identity/stack/runtime tests,43 produced inventory/
projection tests pass:93 distinct source tests. Bounded individual runs under
3s, thread1,55s shell timeout. One spawned-process case explicitly deselected.
Global runtime/GUI cleanup conftest and plugin autoload disabled. Existing
installed ABI imported only for source fixture collection, as already recorded
for257; no worker, JVM, MCP, GUI, environment/package/source install or heavy
test. New tests call the real workspace projection, nominal source-stem
authority and image writer with tiny synthetic arrays; no original pixels.

Readback tests forbid parsing typed generated names, cover dotted wells,
compound declared extensions, absent/null extension, authoritative conflicts,
alias-only headers, deliberate scalar omissions and collapsed contributors.
Both source-identity incompleteness and extension rejection stay strict.

Still required from parent integration with an explicit native slot: ordinary
public PipelineDocument registration -> compile -> execution with image/
labels/CSV/ROI publication enabled, actual saved inventory/pixels, object-ID,
pixel-count16 and ROI readback. Source tests do not establish installed/native
or complete user-workflow acceptance. Preserve original failure receipts and
use a fresh owned synthetic journey, not a replay of259-02.

Original ledger SHA256: `37850b1ecb11fe9dfe47634c2f35645828542068d176e42db7cf4b0196057cc3`.
Original full native log SHA256: `84fbdccf0b497784b59e1aa7d31eb3e9be4bbbfc1002a0ba195b54e24d72f761`.
Original plate metadata SHA256: `cf7fe8ee79b2082ed016d54325b2260e6c15a86cfd5c8434113abf9c0891e287`.
All read-only under `openhcs-issue-batch-20260929/source-live-runtime-payload-259-20260930-02`.
Original257 probe and receipt hashes remain byte-identical to `ae6c90b6d`.

Integrated current main `dbf1c7a8bb699f975bd072a0f39dbe4bd7131ecb` normally,
without conflicts, at `b5572e660b6ba25535f3fd94fa6c5ef4939d7e1d`. Post-integration
checks:28 provenance/persistence/264 tests pass in1.90s and16 runtime identity/
stack tests pass in2.23s. The93-test set above is the pre-integration source
checkpoint;44 were rechecked against the merged source. Working draft262 is
OPEN/DRAFT/MERGEABLE. No source/runtime installation or live acceptance claimed.
