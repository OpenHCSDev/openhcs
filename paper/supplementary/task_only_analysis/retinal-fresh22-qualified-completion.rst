Fresh retinal analysis: body-scale admission and measurement repair
==================================================================

R0010_FRESH22_96 independently analysed the released R0010 development field
using the receiving22 package, task brief and recorded MCP client. No held-out
image or manual reference was opened. The acquisition contains three physical
2586-by-2586 uint8 channels: AF647/RBPMS, AF488 with unspecified identity and
Hoechst. Parameters and geometry use pixels because metadata calibration was
not independently verified. Regional nuisance patches are limited negative
comparators, not an exhaustive specificity reference.

Scientific progression
----------------------

The first candidate produced 274 parent labels and 289 ROI members. Its
grain-scale smoothing and top-hat admission flooded sampled nuisance regions
and missed clear bodies. Raising the threshold reduced the result to 62 labels
and 63 ROI members but lost dim bodies. The author then selected body-scale
contrast, retaining 141 labels and 141 ROI members. A fourth, technical attempt
corrected photometry without changing these labels. These are successive
self-directed development attempts, not four independent autonomous repeats.

The final detection image uses raw AF647 divided by 255, Gaussian smoothing
at sigma 10, then sigma 75 on that smoothed image, and nonnegative subtraction
of the two scales. The broad effective sigma is approximately 75.66 pixels.
Primary-object identification uses threshold 0.012, shape markers and watershed,
40--200-pixel diameter bounds and 35-pixel suppression. These are retained
trial settings, not a universal retinal recipe. The complete nine-step
PipelineDocument, including lazy source configuration, is frozen unchanged.

Independent review personally opened final whole-field, northwest and southwest
raw-only, result-only and combined MCP captures. The northwest bright pair is
represented by separate compact supports. Whole-field nuisance flooding is
reduced, but weak southwest bodies retain small partial masks and some broad
extensions remain uncertain. The author retained seven distributed final
triplets and three additional comparisons/selections, 24 final captures in all;
the coordinator's bitmap review does not claim to cover all 24. Nine labels
touch the image border and 132 are internal. There is no independent manual
count or sensitivity/specificity estimate. Useful bright-body localisation and
local separation are supported; complete soma extent and a biological census
are not established.

Measurement-source correction
-----------------------------

The third attempt's nominal RBPMS measurements were scaled label values with
zero within-object variation. The author detected this error and bound final
photometry to the exact pre-smoothing UnitAF647 artifact, measured against the
same Somata object set. Independent CSV review joined all 141 geometry and
intensity rows by slice and label and found nonzero within-object variation.
Labels 49 and 53 have areas 8812 and 4855 pixels squared, with raw-equivalent
means 38.76 and 36.98. These include background and are not calibrated expression
values. The third and fourth label TIFFs are byte-identical, SHA256
01f37c8a2fd5c3b7dd10cd7c4c69680a6801df0235d5cd51291c480cb9977652.
The author also retained three native raw/unit pixel-correspondence samples;
that per-pixel calculation is author evidence, not an independently repeated
coordinator measurement.

Freeze and closure
------------------

Control root:
/home/ts/wt/openhcs-issue-batch-20260929/next-retina-fresh22-96-after-retina20-20261006/R0010_FRESH22_96/author-workspace/output.
Canonical payload root:
/run/media/ts/hdd/openhcs-science/next-retina-fresh22-96-after-retina20-20261006/R0010_FRESH22_96.
Final source SHA256:
283245318eab94fb35d23bfd1e3f00ece6614198c1533aa1fd426d9ffea7b9ca.
Acquisition SHA256:
3609adc418bb772307804aac1fbecc40d7da54b16cd2a5e3ab8aedbb4d83a851.

The coordinator independently verified all 903 manifest entries, including
sizes and SHA256 hashes: 1736112071 bytes, zero missing or mismatched files.
Final manifest SHA256:
5c0cce6ed48d670afa53da97fe5cff03df8bd29a72e6b59d2561a1c3572ab870.
This manifest verifies its listed files, not later-grown outer journals.
Recorded journal prefixes remain prefix evidence until the harness seals
completed writers. All eight compile/execution jobs completed. The final
execution is cba643bc-6f9e-43e7-9021-3276ab3ac255.

Typed owned viewer/native shutdowns reported process exit; an independent
process check found neither retained PID alive. The original client ended with
exit code 2, preserved rather than replayed or described as clean CLI success.
A two-channel composite was unavailable because singleton channel routes
occupied different aggregate positions; matched individual Hoechst views
provided context without establishing validated colocalisation. Later merged
skill lessons are not credited to this receiving22 author.
