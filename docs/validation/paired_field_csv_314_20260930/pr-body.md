## Summary

Refs #314. Source-only checkpoint based on current main `702b2c2c9`; parent owns integration and final installed/MCP acceptance.

- Fix the earliest original owner, `SourceImageSetIdentityPolicy.from_source_bindings`: shared singleton binding coordinates constrain the paired field rather than becoming plane-member axes. Explicit source-stack and group declarations retain precedence.
- Consume existing `NamedSourceBinding.component_values()` authority; no CSV joining, axis/module switches, parallel registries, mirrors, compatibility reader, measurement-module workaround, or shared-file edit.
- Reproduce through the real spreadsheet exporter using tiny synthetic typed paired fields. Original source produces eight partial rows instead of four complete rows; repaired source combines lineage/location and shape while keeping fields distinct.
- Preserve H003e as immutable REJECT; no frozen data/output access, rerun, retune or mutation.

## Evidence and limits

100 focused source tests pass in 15.52s, maximum RSS 455620KiB under an enforced 512MiB / one CPU / one numeric-thread scope. Covers source identity, exporter/counts, provenance and measurement group scope, independent well/site/z/time, explicit stack/group overrides, third-channel extension, assignment precedence and missing-metadata path identity. `git diff --check` passes.

Original collection/build, behavioral split and initial patch-syntax failures are retained. Full-context NRA stopped (exit124, peak RSS524536KiB, no result); no complete NRA/R1/DSL/native-equivalence proof claimed and no global limit raised. Current-head census, actual pattern IDs and source witnesses are in `docs/validation/paired_field_csv_314_20260930/ownership-receipt.rst`; exact source results/commands and proof limits are in `checkpoint.rst` and retained logs.

Shared owners remain read-only; [direct Avicenna coordination](https://github.com/OpenHCSDev/openhcs/pull/217#issuecomment-5920836946) identifies the boundary. No new agent/model/provider or installation. Local unchanged extension build only; no MCP/GUI/native-process/JVM/external-oracle or biological acceptance. Parent owns those final gates. This draft does not close #314 or claim live readiness.
