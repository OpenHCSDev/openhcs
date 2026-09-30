BaSiCPy parent numerical integration
====================================

Latest source ownership closure: owner-closure.rst. The prior failed guard
below is preserved historical evidence; its findings are now corrected and
the unmodified guard passes. Installed/MCP acceptance is still separate.

Integration owner: parent, 2026-09-30, existing PR217. Original Linnaeus
worktrees are unchanged. Normal current-main merge incorporates
d3a99c0d46dea979bba3f9076da87386e49cbed3. The sole merge conflict was the
ArrayBridge gitlink: paired PR2 was normally merged with its own current main
409b1e0, producing d6d92a716b91f0148dc2c04f9e744bddb7e32ed4. This preserves
both the current main changes and the published typed callable dtype default.
No source file conflict, reset, rebase, force push or installed change.

Published BaSiCPy fork checkpoint is855af6b10c87e832cb6a6594fb288c28d74f46e5.
Requirements and gitlink pin the exact paired published versions.
The fork's real Python3.14.7 source-import run has6PASS in13.96s pytest,
15.97s process,690508KiB peakRSS, zero swaps: public inverseDCT/SciPy
comparison, 2D/3D fit/correction/profile roundtrip and stationary signal
negative control. Canonical fork receipt: docs/python314-numeric-20260930.rst.

Paired OpenHCS source checks
---------------------------

Original attempt failed collection because this fresh source worktree had
no ``openhcs.core._tabular_native`` build. That failure's original log/XML is
retained, not called a production regression or passing test. Existing declared
``setup.py build_ext --inplace`` built the extensions in3.51s,144852KiB peakRSS,
exit0, no install or download. Re-run through run-source-check.sh:

15PASS,9.20s pytest,11.93s process,1026844KiB peakRSS, zero swaps, exit0.
No skips or deselections. Two warnings concern disabled async pytest plugin
configuration. Tests cover actual BaSiCPy fit-transform through OpenHCS's
real decorator, floating correction units, same-fit field values, stationary
signal confounding, aggregate source contributors and component metadata,
invalid Z/channel/time variation and partial projections, field conversion,
grid/count rejection, native direct-call dtype defaults, explicit overrides,
unchanged preserve-input behavior and untyped default refusal.

Actual source paths for OpenHCS, ArrayBridge, BaSiCPy and native2c68 were
asserted. Existing shared Python3.12.3 environment and installed remaining
dependencies were used; CPU-only, one affinity CPU, thread1, isolated scratch,
shared Fiji cache with download explicitly false. No JVM, GUI, blind data,
new environment, package install or provider run. Real app import comes first
so existing OpenHCS metadata configuration owns initialization.

Source ownership
----------------

BOUND-2: model/DCT/dtype/source-projection declarations remain the authorities;
no copied schema or numeric algorithm. BOUND-7: new fork tests access declared
model attributes directly. IMPL-13/TIME-1: the prior private inverse-DCT helper
remains deleted, not revived as a fallback. This checkpoint changes numerical
tests, receipts and exact paired requirements/gitlinks; no extra production
dispatch, alias, store or compatibility reader is introduced.

This is focused source review and executed numerical behavior, not a complete
NRA/global ownership proof. Original logs/XML/build evidence and the original
ratchet invocation error (absolute --root is disallowed) are preserved in
``/home/ts/wt/openhcs-issue-batch-20260929/basicpy-parent-numeric-20260930``.
The corrected original packaged guard uses repository-relative ``--root openhcs``.

That guard is NOT passing:5122 compared metrics, two positive metric keys:
TypeIdentity+1 and ForeignAbsenceProbe in flatfield.py+2. Original raw record
is openhcs-ratchet-corrected.json. These are existing PR217 additions, not
hidden by accepting the numerical tests: exact-int validation in fitted-field
construction and caller-side metadata/projection predicates need source-backed
ownership review. Parent owns that follow-through within this PR. No waiver,
copied detector, changed baseline or global proof claim. Current-main source
integration is a visible draft checkpoint, not ready for a main merge.

Remaining boundaries
--------------------

No installed user entrypoint, compiled/MCP execution, GPU, fitted additive
darkfield or biological result is accepted. Retain the paired default policy
and SOURCE/field projection for serialized installed execution plus artifact
readback before declaring application readiness. Socrates owns ACK-routing;
parent retains final runtime integration. Hosted CI is not the waiting gate.
