Multi-image measurement provenance producer checkpoint
=====================================================

Owner: Singer. This is separate from PR732's aggregate publication receiving
and PR734's export projection. Dewey confirmed no source claim on the
measurement recording/request/invocation family; Planck was asked about the
exact execution/source composition seam before implementation. No scientific
author, installed target, runtime or foreign checkout was changed.

Original public witness
-----------------------

The closed receiving11 engineering case selected Process and Nuclear in one
registered MeasureObjectIntensity invocation. Numeric photometry contains
both source-qualified feature families, while the resulting native table's
provenance names only Process. This is distinct from issue722's already
repaired pixel selection (PR725), and from PR734's exporter: an exporter cannot
recover an image that its native input never represented.

Original complete declarations and native receipt remain at::

  /home/ts/wt/openhcs-issue-batch-20260929/engineering-pre-first-routing-20261004/receiving11/public88/ADMIN734_88/author-workspace/output/export-case03/pipeline-forward.py
  /home/ts/wt/openhcs-issue-batch-20260929/engineering-pre-first-routing-20261004/receiving11/public88/ADMIN734_88/author-workspace/output/export-case03/pipeline-reverse.py
  /home/ts/wt/openhcs-issue-batch-20260929/engineering-pre-first-routing-20261004/receiving11/public88/ADMIN734_88/author-workspace/output/provenance-forward03.json

Determining source relationship
-------------------------------

Inspected current main e00129f64 on the reused isolated checkout. The object
measurement executor retains both measurement images and both numeric row
batches. CellProfilerSourceIdentityMixin.composed_source_metadata flattens
sources image-major. CellProfilerObjectMeasurementRowPolicy uses row source
names to force STACK topology, although a source name is not a runtime-slice
coordinate. CellProfilerMeasurementTableModule.measurement_rows_and_source_provenance
then projects the resulting axis using the rows' local slice_index=0. In the
two scalar-image case this discards the second image before native export.

The fix belongs to the existing source composition/measurement owners:
preserve the declared runtime-slice axis, representing all measured images at
each slice as source contributors. Do not reconstruct provenance from feature
name strings or filenames, add an export-side alias, or add a parallel store.
The single-image and strict source-plane projection contracts remain intact.

Source ownership evidence
-------------------------

Latest NRA skill and authoritative refactor-audit archive SKILL, README,
surface receipt, and complete identity/boundary/implementation/membership
patterns were read before implementation. Applicable risks are IDEN-1
(source-image identity versus runtime-slice coordinate), BOUND-2 (bypassing
the existing provenance owner), MEMB-2 (a copied source roster), and IMPL-5/12
(consumer decisions or composition copied instead of sharing the owner).

The unchanged existing validation/custom-worker-bootstrap708/source_family.py
used refactor-audit's Package parser against this exact main source. It parsed
701 production and 705 test modules, selecting 70/128 relevant full ASTs;
zero parse omissions. Original stdlib process dependencies are emitted by that
reused tool as extra context, not claimed as this defect's cause. Raw evidence::

  /home/ts/wt/openhcs-issue-batch-20260929/engineering-multi-image-measurement-20261005/source-family-before.jsonl
  /home/ts/wt/openhcs-issue-batch-20260929/engineering-multi-image-measurement-20261005/source-family-before.stderr

Parser terminal0: 25.41s, peak549924KiB, swaps0. This is relevant-family source
evidence, not a complete global NRA R1 or behavioral acceptance.

Acceptance and current tier
---------------------------

Source qualification must exercise actual registered multi-image measurement,
both input orders, single-image controls, multiple runtime slices, and retained
exact source aliases/paths/calibration on each represented slice. A new module
declaration using the existing measurement capability must need no generic
consumer edit. Existing malformed/unaligned source-axis checks stay strict.

Ordinary installed public acceptance must execute two distinct selected images
on the same objects, retain their distinct numeric photometry, and export both
typed source identities independently of input order. It will use a separate
recorded ordinary engineering case, never replay the closed receiving11 case.

Working owner fix and first qualification
----------------------------------------

Planck explicitly released invocation.py, module_execution.py and
object_measurement_row_policies.py from his claims; his automatic Points/saved
label producer work is disjoint. The implementation is on the existing
CellProfilerSourceIdentityMixin ancestor. Its aligned_source_metadata uses the
existing source_provenances hook to retain the nominal runtime-slice axis, and
the original SourceImageProvenance bundle/contributor/stack operations to retain
each measured image at each slice. Metadata construction is shared with the
existing composed-source path. The per-object executor consumes that owner.
The row policy's source-name-based composition decision and the executor's
old flattened-source/fallback path are deleted, not retained as compatibility.
No core provenance store, artifact exporter or request codec was added.

The ancestor is already composed with runtime image execution and measurement
alignment through CellProfilerMeasurementImage's real multiple inheritance.
A new nominal source subtype exercises its source_provenances hook with
cooperative super(), and a third source works without generic consumer edits.
The new cases do not add a concrete module/type switch.

Focused source controls used the original engineering620/source-controls01.py
bootstrap, existing paired interpreter, read-only source dependencies and the
already compiled native tabular ABI. No build, installation, native server,
viewer, provider or scientific input was used. Actual registered
MeasureObjectIntensity execution with synthetic source artifacts covers both
image orders, one/two/three images, one/two runtime slices, distinct uint16
photometry, exact represented paths/Z identities and retained pixel-size
metadata. Existing source pixel selection and row-plane projection controls
passed; empty/unequal aligned source axes reject. Original logs::

  /home/ts/wt/openhcs-issue-batch-20260929/engineering-multi-image-measurement-20261005/controls01.stdout
  /home/ts/wt/openhcs-issue-batch-20260929/engineering-multi-image-measurement-20261005/controls01.stderr

Terminal0: 23 passed, 400 deselected, 22.95s whole wrapper, peak474388KiB,
swaps0. Plugin-free pytest reports its two existing unused asyncio configuration
warnings; originals are retained. Source tests are not installed/public proof.
After-owner AST and original R0 remain to be recorded before source delivery.
Ordinary installed/public acceptance remains separate and is not a PR732 gate.
