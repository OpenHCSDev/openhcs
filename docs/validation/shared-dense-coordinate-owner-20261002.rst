Shared dense coordinate reduction
================================

The shared reducer is integrated into PR394 for issue #384. The isolated
qualification source was ``d5441f960fb4cafe5a1f56740cf8c52de7a7d69d``, normally
merged with qualified PR394 ``eb2f23efd`` and main ``a6c18f054``. Integrated
controls use clean ``6e69b85122d3c1a44857835ba9b3fe77e743240d``.

``ObjectLabelStorageStrategy`` retains the genuine sparse-IJV algorithm and
owns shared sum allocation/division. The existing dense leaf specializes int32
2D/3D arrays; ``ObjectLabelValueStorageStrategy`` delegates actual storage.
Tracking and relationships consume one core numerical primitive through their
existing ABI adapters. Their two duplicate kernels are deleted, with all five
compiled consumers migrated. No new class, registry, dispatch table or cache
was introduced.

Before a public domain iterator can mutate pixels or raise, the dense leaf
captures coordinate moments from a borrowing strided 3D view. The existing
``DenseIntegerObjectLabelIdDomain`` bounds moment allocation by the number of
positive pixels. Empty or large sparse ID spans use the original sparse path;
a lone ID ``2**31 - 1`` therefore reaches the original domain error without
allocating a max-ID-sized table. Unsupported dtypes/ranks retain original
conversion, warnings and errors. Readonly, reversed, Fortran and zero-stride
inputs avoid flatten copies. This establishes an O(nnz) allocation bound, not
identical heap thresholds under OOM or a resolution of issue #433.

Existing provider/callable preparation warms C/F/A writable and readonly
signatures before execution. An isolated PrimaryObjects preparation control
refuses both compilation and cache loading during subsequent admitted calls.
Controls preserve effectful Sequence iteration, NumPy allocation-phase errors,
NaNs/counts, independent result buffers and input mutation/alias semantics.
Eleven effect controls also run against the actual unchanged Git parent.

Qualification
-------------

* Isolated synchronized controls: 100 passed, 2 existing skips.
* Integrated controls at ``6e69b85122``: 101 passed, 2 existing skips in
  194.57 seconds; tracked source hashes remain unchanged.
* Original scoped R0: every metric delta zero; original R1: no increases,
  unchanged 160-second budget. Both compare ``eb2f23efd`` to ``d5441f960``.
* Global NRA census: 5,526 original classes, 5,513 canonical declarations,
  13 explicitly OPEN syntax rows, no parse errors.
* Saved real Wound pair: exact coordinates/counts and physical allocation/
  alias gates; original median 0.160669 s, candidate 0.019144 s, local saving
  0.141524 s across paired replay. Preparation/JIT precede timing.
* Twenty-one saved Track frames and old-Git tracking/relationship numerical
  ABI comparisons pass. This is not a full relationship transaction proof.

Initial admission, readiness and high-ID negative evidence remains retained.
These local results alone do not establish ordinary pipeline performance.
Root-owned ordinary qualification is recorded separately below. Illumination
has no centroid calls.

Evidence: ``/var/tmp/openhcs-shared-dense-coordinate-owner-closure-v2-20261002.json``;
``/var/tmp/openhcs-shared-dense-production-saved-replay-v4-20261002/receipt.json``;
``/var/tmp/openhcs-pr394-integrated-dense-coordinate-controls-20261002.log``.

Ordinary integrated comparison
------------------------------

Four uninstrumented public sweeps in ABBA order compare frozen b4700288f
(shared geometry baseline) with integrated 6e69b8512 (shared coordinate owner).
Each case has one well, inline worker and thread on CPU5, default OUTCOMES
and memory observer, and a reused READY server. Server/library/kernel startup
and shutdown are excluded; compilation remains in total. No samples are removed.

Two-sample descriptive means (seconds; not statistical significance):

* ExampleWoundHealing: execution 3.287030339 -> 2.984141707;
  compilation 0.337689161 -> 0.340739846;
  total 3.866369809 -> 3.562642806.
* ExampleTrackObjects: execution 5.338271976 -> 5.052027345;
  compilation 0.929434419 -> 1.252314091;
  total 6.629491309 -> 6.684317434.

Track total regresses by 0.054826125 seconds in this comparison. Its compilation
increases by 0.322879672 seconds; no causal late-JIT attribution is established.
Wound total decreases by 0.303727004 seconds. Neither result satisfies the
remaining whole-pipeline objective or replaces the generic-plumbing frontier.

Every observation, in case/compile/execution/total seconds:

* 0-A ExampleTrackObjects: 0.950359821,
  5.625208855, 6.914708113.
* 0-A ExampleWoundHealing: 0.343463182,
  3.276733875, 3.827193568.
* 1-B ExampleTrackObjects: 1.421878338,
  5.020748138, 6.829343345.
* 1-B ExampleWoundHealing: 0.342035055,
  3.044292212, 3.623388787.
* 2-B ExampleTrackObjects: 1.082749844,
  5.083306551, 6.539291524.
* 2-B ExampleWoundHealing: 0.339444637,
  2.923991203, 3.501896825.
* 3-A ExampleTrackObjects: 0.908509016,
  5.051335096, 6.344274506.
* 3-A ExampleWoundHealing: 0.331915140,
  3.297326803, 3.905546051.

All eight complete authored-output inventories, strict table/image comparisons,
scientific file bytes and source/environment/native/input freezes pass. Wound
retains full native qualification through the exact qualified output reference.
Track preserves all original OH bytes and its original 77,726-pixel native RED;
this does not include the separate draft renderer repair in PR468. No parity
tolerance, exclusion or output policy changes.

Receipt: ``/var/tmp/openhcs-pr394-shared-dense-ordinary-abba-science-20261002.json``
SHA256 ``affb93c5955585be6963936552a1f40da051989688e7b0c58f406f398e894400``.
Commands: ``run_pr394_shared_dense_ordinary_abba_20261002.py`` and
``validate_pr394_shared_dense_ordinary_abba_science_20261002.py`` under /var/tmp.
