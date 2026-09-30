## Working typed produced-address publication fix

Fixes #257 and #264. Implementation/file owner: Socrates. Parent/OpenHCS
coordinator is integration owner. Draft pending native acceptance; Zeno retains
the source-live slot.

- Resolve source extensions through existing metadata/parser identity owners,
  preserving dotted well tokens and compound declared extensions.
- Place named-output qualifiers before the declared extension.
- Publish image addresses directly from retained producer storage coordinates,
  keeping collapsed semantic coordinates distinct.
- Reconcile the actual saved inventory through the existing durable typed
  projection store in an atomic transaction. No parsing generated filenames,
  new store, protocol fallback, or guessed coordinates.
- Preserve source lineage, actual saved dtype/calibration and artifact aliases.
- Retain declared extensions in the existing `SourceImageIdentity` join;
  `FunctionOutputExtensionAuthority` derives that same typed fact.
- Preserve loaded source identity when persisted native headers declare no
  provenance. Declared scalar/plane/contributor semantics remain authoritative;
  collapsed omissions are not restored from storage filenames.

Source checks:93 bounded tests pass (43 produced inventory/projection,
28 provenance/persistence/264,16 identity/stack,6 image/ROI materializer), with generated-path
parsing made to fail and final reconciliation after memory release. Existing
installed ABI module preloaded solely to collect source tests; no rebuild or
installation. `git diff --check` passes. Global GUI/runtime cleanup fixtures and
plugin autoload disabled; no native worker/JVM/MCP/GUI/heavy tests.

Original investigation/reproducer/receipt retained at `ae6c90b6d`; original
reproducer and receipt unchanged. Current ownership and implementation limits
are recorded in `docs/validation/issue257-implementation-20260930.md`.
264 root cause, original trace/input hashes and red/green reproduction are in
`docs/validation/issue264-source-extension-20260930.md`. The ROI-worded strict
guard fails in an actual image writer too; it is preserved, not weakened.

Persisted formats: unchanged OpenHCS metadata/source-projection, PipelineDocument,
TIFF/ROI/CSV and MCP; no migration, adapter or reset. Owning declarations:
`SourceImageIdentity`, `FunctionOutputIdentity`, `VirtualWorkspaceImagePayloadProjection`
and the existing atomic metadata publication owner. Oversized provenance class
does not grow; workspace helper is deleted in place. Full R1/packaged ratchet
not claimed under the source-light constraint; no tool installation attempted.

Still required before readiness: ordinary native compile -> execute -> saved
inventory/readback using a tiny synthetic OME-TIFF and typed image/artifact
outputs, publication enabled, first/chained source lineage. No original failed
job replay or scientific/held-out data is needed or used.

Source guards also cover reordered dotted stacks, atomic missing-address
rejection, concurrent publication and deletion from projection/component
coverage. No R0/L0/S1–S8 surface refactor is absorbed here; hosted CI is not a
wait condition.264 shares the retained extension/address contract and is combined
under the same sole file owner; no competing patch. No config/compiler edit or
committed overlap with checked PR205/PR263/merged259 source. Parent owns
integration and affected installed/native acceptance; this remains a draft.

Integrated current main `dbf1c7a8b` without conflict at `b5572e660`;44 relevant
source cases rechecked after integration.93 is the complete pre-integration
source checkpoint, not an installed/native acceptance claim. Latest: normal
merge of main205 `fb5fea4f1` at `82f679895`, no conflicts; the same93 bounded
source tests pass against that merged source. Parent owns fresh source-live262
images+labels+CSV+ROI inventory/readback and257 dotted-OME chained acceptance,
then merge/install. No native owner launched or old job replayed here.

Ratchet clarification: only the CLI entrypoint was absent, not the package.
Existing `/home/ts/wt/comms-owner-startup-sol-20260929/src/agent_comms/debt_ratchet.py`
and Python3.14 are available. No install/copy/replacement measure/repeated scan;
parent reviews the checkpoint rather than requesting another scan.
