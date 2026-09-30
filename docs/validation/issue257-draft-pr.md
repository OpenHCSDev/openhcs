## Working typed produced-address publication fix

Fixes #257. Implementation/file owner: author of this branch. Parent/OpenHCS
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

Source checks: 58 bounded fixture/architecture tests pass (28 publication/stack,
15 existing identity/stack,15 projection/boundary), with generated-path
parsing made to fail and final reconciliation after memory release. Existing
installed ABI module preloaded solely to collect source tests; no rebuild or
installation. `git diff --check` passes. Global GUI/runtime cleanup fixtures and
plugin autoload disabled; no native worker/JVM/MCP/GUI/heavy tests.

Original investigation/reproducer/receipt retained at `ae6c90b6d`; original
reproducer and receipt unchanged. Current ownership and implementation limits
are recorded in `docs/validation/issue257-implementation-20260930.md`.

Still required before readiness: ordinary native compile -> execute -> saved
inventory/readback using a tiny synthetic OME-TIFF and typed image/artifact
outputs, publication enabled, first/chained source lineage. No original failed
job replay or scientific/held-out data is needed or used.

Source guards also cover reordered dotted stacks, atomic missing-address
rejection, concurrent publication and deletion from projection/component
coverage. No R0/L0/S1–S8 surface refactor is absorbed here; hosted CI is not a
wait condition. Newly assigned264 is being traced under the same file owner;
no separate competing patch will be opened.
