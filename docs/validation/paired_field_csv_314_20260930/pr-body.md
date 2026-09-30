## Summary

Refs #314. Source-only repair, originally reproduced on `702b2c2c9`, now normally merged with current main `2b7969f700c33eb7f73f891d975afd1efc0628bb`. Parent owns integration and final installed/MCP acceptance.

- Fix the earliest original owner, `SourceImageSetIdentityPolicy.from_source_bindings`: shared singleton binding coordinates constrain the paired field rather than becoming plane-member axes. Explicit source-stack and group declarations retain precedence.
- Consume existing `NamedSourceBinding.component_values()` authority; no CSV joining, axis/module switches, parallel registries, mirrors, compatibility reader, measurement-module workaround, or shared-file edit.
- Reproduce through the real spreadsheet exporter using tiny synthetic typed paired fields. Original source produces eight partial rows instead of four complete rows; repaired source combines lineage/location and shape while keeping fields distinct.
- Preserve H003e as immutable REJECT; no frozen data/output access, rerun, retune or mutation.

## Evidence and limits

On merged source head `e3d991e9cf02c496daa7c9df32c73bfde4a7ad00`, **131 distinct source tests pass; eight inherited fixture failures remain**. Shards: 101 passed (14.13s, RSS406828KiB), then30 passed/8 failed (6.01s, RSS387968KiB), under an enforced512MiB / one CPU / one numeric-thread scope. Covers source identity, real exporter/counts, pipeline-config propagation, provenance/group scope, independent well/site/z/time, explicit stack/group overrides, third-channel extension, assignment precedence, missing-metadata paths and applicable shape/secondary/module contracts. Source/test `git diff --check` passes; raw logs deliberately retain diagnostic whitespace.

The eight failures are synthetic matched-anchor fixtures lacking the strict `MeasurementSubjectRelation` required by main's existing artifact owner, before the repaired policy runs. All eight reproduce on untouched original main (8 failed/3 passed); affected fixtures/guard are unchanged in new main. Parent integration owns their disposition. No guard/assertion was relaxed; this is not a green broad suite or issue closure.

Original collection/build, behavioral split, patch-syntax and baseline-harness assembly failures are retained. Full-context NRA returned an explicit deadline-incomplete receipt (exit124, parse stage, internal20s deadline, elapsed22.054s; peak RSS524536KiB); it was not an empty result or proven OOM. No complete package NRA/R1/DSL/native-equivalence proof claimed and no global limit raised. A one-module compact loop completed with79 detectors/0 omitted/0 findings, scoped only to the unchanged policy module. Exact merged-head core census shows +16 code lines and zero other measured debt-screen deltas. Actual pattern IDs/source witnesses, commands, dependency import qualifications and original failures are published under `docs/validation/paired_field_csv_314_20260930/`. Disposable owned scratch/builds are archived and removed; `SHA256SUMS` seals evidence/source bytes.

Shared owners remain read-only; [direct Avicenna coordination](https://github.com/OpenHCSDev/openhcs/pull/217#issuecomment-5920836946) identifies the boundary. No new agent/model/provider or installation. Local unchanged extension build only; no MCP/GUI/native-process/JVM/external-oracle or biological acceptance. Parent owns those final gates. This draft does not close #314 or claim live readiness.
