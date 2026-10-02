Singleton label projection at the final invocation boundary (#477)
=================================================================

The ordinary translocation benchmark failed on frozen ``6e69b851`` before
producing a successful well. Its OverlayOutlines invocation paired a scalar
640-by-640 RGB image with object labels on a declared singleton runtime root.
The image had a channel axis but no image-plane projection. Treating the RGB
channels as image planes would violate the existing strict axis contract.

The input binding request initially derived label shape with the callable's
FLEXIBLE default. The module executor resolved the final NATURAL mode later,
after binding, so its semantic controls and the bound labels could disagree.

Existing nominal ownership
-------------------------

``ObjectLabelInputExecutionMode.invocation_kwargs`` now owns this final
projection. MATCH_IMAGE_STACK with a NATURAL scalar image may project an
already-bound label argument only when the original runtime declaration proves
exactly one plane. It delegates to the existing ``RuntimeSliceProjection`` and
merges the resolved semantic controls once. The module executor delegates to
that owner after resolving execution mode.

Explicit FULL_STACK label declarations and FULL_STACK execution remain intact.
Multiple or unproved runtime axes and retained image-plane projections keep
their original strict guards. The fix neither invents an image axis nor reloads
artifacts. Redundant intermediate image/default-mode locals are removed. No
new policy class, cache, per-module exception, or color-processing change is
introduced.

Source and local validation
---------------------------

The final isolated source is ``ccaa4cba6a1eca818cd544438941f1c1cedb3e32``,
integrated into PR #394 by ``1763ef07eba959dbefa7643cb90c8230fdf12518``.
The initial inline implementation and its original R0 failure are retained in
history; that route added GodClass, boolean-chain and foreign-absence metrics.
The final existing-owner implementation passes unchanged original R0 metrics
and original R1 with its original 160-second budget.

The original reproducer recorded two expected failures and five passing
controls. The repaired module-consumer gate passes 402 controls. The global
source census parsed 703 modules with no errors. All five registered
MATCH_IMAGE_STACK consumers currently declare FLEXIBLE processing contracts.
External custom MATCH consumers with a non-FLEXIBLE stack-only contract have
not been qualified; this report makes no blanket callback-equivalence claim.

The source-qualified receipt is
``/var/tmp/issue477-policy-owner-qualified-receipt-20261002.json`` with SHA256
``7ebcd89739bbe58cf7630c093f02b92ecf41732a196073641ec373e4d9b019ca``.

Actual public pipeline consumer
-------------------------------

The frozen integrated source at
``/var/tmp/openhcs-pr394-singleton-label-qualified-20261002`` remains immutable.
Its ordinary public run completed both translocation and WoundHealing with one
successful well each, a reused READY server, one inline worker and one thread
on CPU 5. All input, native-binary, environment, dependency and tracked-source
freezes pass. Server/library/kernel preparation and shutdown are outside the
pipeline clocks; compilation and OUTCOMES closure remain inside total.

The single observations are:

================= ============== ============== ==============
Case              Compilation(s) Execution(s)   Total(s)
================= ============== ============== ==============
Translocation     0.527004       1.570796       2.539227
WoundHealing      1.296431       2.897727       4.421997
================= ============== ============== ==============

These are correctness observations, not matched optimization evidence.
Wound's higher compilation observation is retained and its cause is unknown.
The original failed translocation clocks remain excluded from speedup claims.
The observation receipt is
``/var/tmp/openhcs-pr394-singleton-label-ordinary-v1-20261002/observations.json``;
its source-freeze SHA256 is
``ea4969dbfe48e7a42ff039b07a32eb0d2464374362b89588682483fa33039128``.

Wound's complete authored output inventory, table comparison and exact
scientific bytes pass against the qualified ``9aa3918d`` reference. Its
two-row Image.csv SHA256 remains
``939735fa17a067137fea2adc77d57f9ce1df24bfcb6588c49023de1cc3998677``.
The read-only scientific receipt is
``/var/tmp/openhcs-pr394-singleton-label-wound-science-20261002.json`` with SHA256
``7a8c3cafa33e54394d9a24f7744c6a6b641e48c6f712f1baab7c632dcace0655``.

Translocation still requires fresh warm-native execution and complete authored
table, image, discrete-value and inventory comparison before issue acceptance.
The first native-controller preparation correctly rejected an auxiliary CSV
misclassified as an image input; its failure is retained. No tolerance change,
scientific-output exclusion or issue-closure claim is made here.
