Issue424 / PR425 source qualification
====================================

Source owner Lorentz; installation/native owner parent; biological tuning
Dalton. Base faf8e1f263244bf4d3dbb1e16833c416bbc811bf. Qualified published
source58e6cc40f243e84b5dd46ad1132a62d96975718f. Receiving ownership and source
trace are in RECEIVING.rst. This is a control fix, not biological acceptance.

Ownership and units
-------------------

The existing MetaXpressCellBodySettings.minimum_inscribed_diameter_px exposes
the existing 2*max(EDT)-1 soma acceptance threshold. Its default is derived from
the original compact engine profile10, unchanged. The default modular profile12,
CP smoothing/declumping settings, calibrated area, upper minor-axis width and
intensity statistics are unchanged. Zero explicitly disables only this lower
gate. The existing settings owner now supplies contract_candidates to both
primary and nuclear-propagated consumers through one inherited hook. The two
repeated argument projections and the predicate's hidden global lookup are gone.
No new detector, config schema copy, registry, settings mirror or stored facts.

The module, settings and callable documentation explicitly label this as an
OpenHCS-exposed engine gate, not a vendor MetaXpress control or parity claim.
No numerical biological setting was selected. Test values are synthetic controls.

Completed behavior
------------------

* qualified-controls:13 passed,8.38s,496416KiB single-worker max RSS, zero swap.
  Exact synthetic56-pixel labels at1.3556um/pixel exceed100um2 but fail default10
  and pass the deliberately smaller test gate. Separate area/intensity/upper-
  width negatives remain. Physical calibration changes area qualification,
  while the lower gate remains explicitly pixel-based. Default CP outputs equal
  an explicit legacy10 gate; candidate profile kwargs remain identical.
* Actual primary and nuclear-propagated consumers execute an independent
  GateAudit capability plus original settings through cooperative super/MRO;
  they observe the same declared gate respectively once and twice. No consumer
  edit is needed for this independent capability.
* Real source FastMCP lists an independently declared settings capability's
  generated numeric/default10 input schema, admits5.0, executes cooperative
  validation and inherited calibrated qualification, and returns the original
  typed settings. No hand-written schema or replaced MCP transport is used.
* Actual openhcs_describe_function dispatch projects original field help,
  pixel units and default into the callable detail. PipelineDocument render /
  from_source retains the exact typed cell_body value and rendered source.
  This uses already-declared original metadata in the original source catalog
  fixture; it is not fresh installed catalog discovery/ABI acceptance.
* regression-768:85 passed /1 failed,10.20s,480220KiB, zero swap. Complete
  tests/unit/test_neurite_outgrowth.py and original declaration-help tests.
  Includes genuine physical length calibration and original explicit2-D
  rejection. The failed case is unchanged on exact base: see below.

Behavior was qualified at30cc0f800.30cc..58e6 changes documentation only in the
one production file; both new test files and executable statements are identical.
The source hash manifest pins the final reviewed documentation and test bytes.

Original R0 and explicit limits
-------------------------------

Unmodified packaged agent_comms.debt_ratchet SHA256
e323c94d49c2b72d9524a5169f123e64b4a6e46a41035ca9fb4497e49b6ca562,
readonly tool root /home/ts/wt/openhcs-s1-original-ratchet-20261001/src.
Actual --root openhcs --base faf8e1f --head58e6cc40f covers the entire changed
production path openhcs/processing/backends/analysis/neurite_outgrowth.py:
5190 measurements, zero positive/negative deltas,exit0,17.53s,86964KiB,zero swap.
This is original changed-path R0, not a completed whole-context semantic audit.
Full-context R1 is not rerun; the existing58s incomplete357 boundary remains.

Base-regression: exact tracked source/tests extracted from faf8e1f into the
declared owned scratch snapshot.85 passed /same1 failed,24.07s,564424KiB,zero swap.
Both base/head fail test_cell_rows_do_not_remeasure_owned_paths_with_cp_seed_
propagation at missing backing LazyDiscoveryDict.discover_matching, followed
by missing CellProfilerBackendModule.skeleton. No assertion, required input,
detector or loader is skipped/weakened. Parent owns independent public-dependency
repair; backing versions are recorded verbatim in backing-dependencies.txt.

Retained failures and reproducibility
------------------------------------

All original logs/XML/JSON/resource output are byte-exact in EVIDENCE.tar.gz,
with per-member SHA256SUMS and ARCHIVE-SHA256SUM. SOURCE-SHA256SUMS pins every
changed production/test file. Tool commands are in original time/monitor logs.
Original red6 missing-setting failures plus1 unsupported CP-mask assumption;
green2 fixture failures/5 passes; controls2 authoring fixture failures/9 passes;
authoring/debug and controls-768 catalog/extension failures all remain.
final-controls and original-neurite512MiB monitor stops are incomplete, not
passes. Base-original missing pytest plugin and base-comparison conftest path
collision are retained preparation failures, not product regressions.

Initial source catalog preparation children terminated with missing
openhcs.core._tabular_native before preparation completed. No native application,
viewer/listener, installed-package change or scientific execution occurred.
Final prepared-metadata fixtures do not claim fresh installed catalog behavior.

Original source/testing stashes and all S1 evidence are untouched. The21MiB
base scratch was a disposable tracked-only Git snapshot plus bytecode; no unique
source, history, science data or handoff. After workers exited and lsof returned
no open files, that exact scratch directory was deleted without an archive;
the original Git base and all qualification logs remain. No S1/biological data
or saved session was removed. EVIDENCE.tar.gz is159473 bytes; tar compare passed.
Parent owns source merge and later installed/native acceptance; Dalton measures
and tunes biological candidates only after the separate installed419 repair.
