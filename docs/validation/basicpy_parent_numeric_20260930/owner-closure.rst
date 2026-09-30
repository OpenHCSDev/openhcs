Fitted-field ownership closure
==============================

Parent owns this PR217 continuation from08d7d3acc2287619e0278df82e94d021169177c0.
Current main remainsd3a99c0d46dea979bba3f9076da87386e49cbed3. Paginated open
PR256 file inventory and PR206/207 inventories show no overlapping claims on
the three core projection/metadata files. Socrates' native ACK work is untouched.

The prior guard failure was reproduced and retained, not waived. The source
correction is e0fbf1b06, with final volume-coverage tests and source recipe fixes
included in this checkpoint. Full package census:354488code lines, no parser
warnings. This is lightweight source census and tracing, not a complete NRA
semantic/global proof. Exact patches, not claimed native DSL replay.

Ownership and migration
-----------------------

* BOUND-1: observation_count is internally generated from the real model's
  NumPy observation shape and carried by an integer-typed runtime declaration.
  Remove duplicate exact-type revalidation; keep the genuine count>=2 invariant.
  No external MCP input, saved declaration or wire-format decode is weakened.
* BOUND-2/IDEN-3: ImagePayloadMetadata now owns admission of its independent
  observation coordinate. It uses original retained provenance and preserves
  the raw-array/no-source-identity case. Fitted fields delegate; they no longer
  probe or reconstruct the metadata owner's absent/present state themselves.
* BOUND-2/IDEN-3: RuntimePlaneAxisValueProjection owns complete-axis admission
  through its existing type, beside its selected-plane and shape contracts.
  Optional absence is rejected at that boundary; the instance owns its plane
  selection state. Both selected-plane outputs and fitted fields delegate.
  No family roster, new dispatcher, wrapper type or metadata mirror is added.
* Remove the two identical overwritten from_mapping and retained_plane_component_values
  declarations from ImagePayloadMetadata. Effective bodies remain unchanged;
  source-contract checking now rejects duplicate methods in that declaration.

A new complete-stack consumer calls the existing owner instead of restating
its projection state. Both registered runtime-axis enum members exercise the
same declaration in the new-case test. No MRO change, external format or
persisted-state migration; optional input remains explicitly rejected where a
complete source proof is required. Domain error text carries caller context.

Executed acceptance
-------------------

152PASS,15.89s pytest/18.09s process,1133744KiB peakRSS, zero swaps, no skips
or deselections, one CPU/thread, existing Python3.12.3. Four actual source
imports asserted, including the newly initialized own ArrayBridge submodule
at the same published d6d92a7 pin. Real 2D and4D(N,Z,Y,X) OpenHCS BaSiC
fits retain native corrected values and same-fit fields. Covers prior provenance,
source-projection, context proof, singleton alignment and invalid selection/
independent-axis/grid/count behaviors. Seven source contracts pass in0.032s.
Two warnings are disabled async pytest plugin configuration, not skipped tests.

First owner-check launch stopped before pytest because the asserted physical
ArrayBridge path still named the separate integration worktree after the own
submodule was initialized. Preserve that original failure; correct the recipe
to the actual pinned checkout, not the production behavior. The initial corrected
suite had151PASS; adding the adapter's documented4D volume case produced152PASS.
All original logs/XML and resources remain under
``/home/ts/wt/openhcs-issue-batch-20260929/basicpy-owner-closure-20260930``.
No install, new environment, download, JVM, GUI or biological input.

Unmodified original packaged agent-comms ratchet against main:5143metrics,
no positive deltas, exit0. ImagePayloadMetadata class-excess -9, projected-image
foreign absence probe -1, string subscripts -2. The comparison from the prior
PR checkpoint independently reports exact-type checks -1, foreign absence
probes -3, string subscripts -2, and no added dispatch/type switches, codec
subclasses, attribute-name access or long Boolean-chain terms. Original raw
before/after records and complete census are retained, no baseline manipulation.

Paired library checkpoints use the same original packaged guard:
ArrayBridge38metrics and BaSiCPy43metrics, neither adds a positive metric.
Actual paired dtype tests and CPU BaSiC numerics were executed in the prior
checkpoint. Merge/remote verification is recorded separately from installation.

GitHub plus independent git ls-remote verification:
BaSiCPyPR1 merged mainc1d7c3dc6a57a26acc1179de3f2e14b1c5faa0ec at19:07:50UTC.
ArrayBridgePR2 merged into its old stacked base branch, not main; parent
verified that branch821696e7 is tree-identical to tested d6d92a7, includes
current main409, and contains only the two intended main-delta files.
Main-targeted PR3 then merged main ea3f2a4cc91c4810d12343f58f85c1195e1a41e6
at19:13:30UTC. No optional hosted-CI wait, bypass, force push or install.
OpenHCS retains the same exact tested ancestor pins, not a dependency rollback.

Remaining acceptance
--------------------

This closes the reported source ownership guard failure, not the full expanded
ZIP goal or installed application acceptance. Parent still owns serialized
compiled/MCP discovery/execution and persisted corrected/flatfield/darkfield
artifact readback. Frozen biology runs, actual installed harness and managed
skill remain unchanged. Hosted CI is not the gate; real application verification
is still required before readiness or activation is claimed.
