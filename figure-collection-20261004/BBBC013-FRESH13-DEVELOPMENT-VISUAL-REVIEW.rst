BBBC013 fresh13: measured first candidate and local visual evidence
=================================================================

This is an independent development-stage review, not the final reserve
evaluation or a validated whole-plate result. The original author remains
active. No review feedback was sent into its fresh scientific context.

Original owner root::

  /home/ts/wt/openhcs-issue-batch-20260929/next-bbbc01388-p00196-fresh13-20261005/BBBC013_FRESH13_88/author-workspace

Native PNG root::

  /run/media/ts/hdd/openhcs-science/next-bbbc01388-p00196-fresh13-20261005/BBBC013_FRESH13_88/QA

The author retrieved the Official30 translocation conversion contract and
foreground/marker measurement guidance before its first scientific proposal.
Six development wells were A01,A02,A12,E02,E12,H01. Its rationale records
distributed DNA/GFP samples, genuine-pair peaks/valleys, a broad ordinary
nucleus, rejected contaminated background boxes and provisional marker
choices. Explicit intensity smoothing6/suppression7 were related to measured
pair separation rather than justified only by a borrowed diameter default.
The author records no scientific parameter change after that first proposal;
technical source-binding, table and executor adaptations remain separate.

Candidate-freeze.json is dated 2026-10-05T14:37:55.228591+00:00 and names
90 reserve wells plus six prospective review witnesses. All five named frozen
source hashes independently matched at review. The final PipelineDocument
SHA256 is 24553b92d3e9a16e1dd5269708ba2845178ff7758939df9377581d0b88ceb2e1.
This review did not inspect reserve scientific pixels or reference answers.
It does not independently reconstruct every access before freeze.

The coordinator personally opened nine original development PNGs, raw-only,
result-only and combined for each of these groups:

* devA01pairp99: timestamps 20261005T143653533031Z,
  143700330498Z and 143707365852Z. Ordinary nuclei are mostly intact; two
  visibly close pairs have separate masks. The upper-left complex cluster
  remains ambiguous and is not counted as a proved splitting success.
* devE12dim01: timestamps 20261005T143220941641Z,
  143227848826Z and 143235048785Z. Several dim ordinary bodies have aligned
  masks; the lower-right close pair is separated. This is local positive
  evidence, not exhaustive dim-object recall.
* devA12shell01: timestamps 20261005T143341586837Z,
  143348807994Z and 143355801339Z. The expanded regions contain bright GFP
  interiors but extend into nearby weak/background signal. They support the
  declared local measurement-proxy interpretation, not whole-cell boundaries.

Each filename ends _napari_6021_OpenHCS_Napari_Visualization.png. All nine
PNGs matched their receipt hashes and sizes. Every capture reports
render_complete and the same 953 x 464 canvas, XY orientation, dimension
order and axis point within its set. Those fields alone do not establish
equal numeric intensity windows or the complete camera/source state.

The A01 viewport acknowledgement applied centre(0,300,325), zoom4.0;
A12 applied centre(0,250,350), zoom1.6. The named E12 viewport receipt instead
contains a strict request-validation failure: presentation was missing and
top-level center/zoom were rejected. Its requested (0,350,310)/zoom2 must not
be cited as applied. The preserved bitmaps can still be inspected at their
observed matching layout, but exact camera attribution needs subsequent
readback. A screenshot filename is not a successful navigation receipt.

Distance-N10 cell regions and cell-minus-nucleus cytoplasm are intentionally
local photometry proxies. Raw GFP means and ratios are not corrected full-cell
photometry, and no physical calibration was verified; geometric units remain
pixels. The final declared measurement callable is translocation_rows_v2;
the separately retained v3 experiment is not the final pipeline's callable.

This checkpoint demonstrates useful measured first-candidate reasoning and
supported local nuclear segmentation. It does not certify reference parity,
all-well counts, unbiased ratio magnitudes, dose-response fitting or final
assay statistics. Those require the original reserve execution and final
artifact/claim review, which remain assigned to the active author.

Subsequent frozen plate execution and arithmetic check
-----------------------------------------------------

The original finalstatus09.json receipt records job-7 complete, sequence1263,
terminal status ok and no job error. This updates execution coverage, not
the unfinished final reserve-label review or lifecycle closure.

The coordinator read the frozen final PipelineDocument with Python AST and
literal-evaluated its declared public_layout; no author source was executed.
All 96 saved well-table CSVs contain one row, with exactly the 96 declared
well identities and finite mean ratios. Independent stdlib arithmetic from
those rows reproduced all 24 dose-table rows: wells present/finite counts,
mean, sample between-well SD and standard error. Both assay rows' Z-prime,
declared replicate-SD V-factor and number of curve levels matched to 1e-12
relative/absolute tolerance. These computations do not rerun segmentation.

Wortmannin negative/positive control mean ratios were 1.0459212737991468
and 7.396750666634699, Z-prime0.747241932867265, replicate-SD V-factor
0.6003763080817637 over11 curve levels. LY294002 control means were
1.2640299921979108 and 7.330033021311369, Z-prime0.4925629984068619,
replicate-SD V-factor0.7290714708945047 over10 levels. Each control group
has four wells. The different concentration units remain nM and uM;
neither compounds nor individual cells were pooled as independent replicates.

Saved table root is the HDD owner root above, acquisition_final01/results.
A01_dose_response_table_step3_details.csv SHA256 is
978eeaa3ce3089375e6f4cd4411e0320227b9c744923a7e4afd1571a2d5f4372;
A01_assay_statistics_step4_details.csv SHA256 is
e1e0613caa7f5754a502646f364f1b65bc0d4e8bc63afa3bef126183b03e182e.

Z-prime is computed as 1-3(SDpositive+SDnegative)/absolute control-mean
difference. The separately named V-factor is the author's explicitly declared
1-6*mean(dose replicate SD)/range(dose means), using sample SD. Arithmetic
agreement is not equivalence to another publication's V-factor definition.
Likewise it does not prove unbiased compartment photometry or complete
nuclear detection. The control-separation finding is useful within this
fixed local-ROI method while reserve visual review remains active.

Post-freeze reserve witnesses and retained controls
--------------------------------------------------

The coordinator subsequently opened nine original reserve PNGs: raw-only,
result-only and combined for B01 DNA, B01 GFP local compartments and F12 DNA.
All nine files matched their original capture-receipt sizes and SHA256 hashes.
These are bounded post-freeze witnesses, not an inspection of all 90 reserve
wells. No pipeline, parameters or scientific arrays were changed, and no
finding was sent to current fresh authors.

The original viewport and intensity acknowledgements identify B01 at
centre(0,330,370), zoom2, DNA limits(0,100) and GFP limits(0,139); F12 is at
centre(0,350,350), zoom2, DNA limits(0,64). Both channels are site1/Z1/T1.
The corresponding isolation receipts report exactly raw, result and their
union as the visible routes. The intensity receipts identify the actual
B01/F12 source components, rather than inferring channel from a layer title.

B01 ordinary nuclei have aligned support. A faint central oval remains
unlabelled, with uncertain identity and size eligibility; a textured core
is not independently resolved as a genuine pair. F12 ordinary and elongated
bodies generally retain aligned masks, including separated neighbours, but
some faint support is unlabelled. These views support useful localisation,
not exhaustive recall, a manual count or a numeric segmentation accuracy.
B01 GFP regions overlap cytoplasmic signal but also extend into weak or
extracellular signal and omit distal cell extent. They remain fixed local
measurement compartments, not inferred whole-cell boundaries.

Capture groups under the native PNG root above are:

* reserveB01DNAdetail01: raw145749928171, result145756671799,
  combined145804587846;
* reserveB01shell01: raw150147690344, result150155317925,
  combined150202803464;
* reserveF12DNAdetail01: raw145915652984, result145922967601,
  combined145930161255.

Each timestamp has prefix20261005T and suffixZ, followed by the same native
filename suffix used above. Camera and window receipts are the corresponding
output/receipts/<group>view.json and <group>win.json; visibility receipts use
rawiso, resultiso and combinediso. In the B01 DNA result/combined screenshots,
the raw-layer title instead says GFP/G06. The typed visible-route and intensity
identities select DNA/B01, and the displayed raw structures match the B01
raw-only image. This is a retained presentation-identity discrepancy, not
evidence that the scientific arrays were channel-swapped. Its source cause
is assigned separately to the viewer owner; no new capture was requested.

Independent handoff verification found 367 complete author-control files
unchanged and one append-only outer native journal with an intact recorded
42,477,117-byte prefix. At review the journal was42,494,204 bytes, an append
of17,087 bytes; its full SHA256 was
38d50748c9c1b749824e73479a6a7ebbde0ca4767f26459657f65c63f81d188f.
The prefix SHA256 still matched the original handoff manifest. That manifest
explicitly delegates the final outer-writer seal to the harness after author
exit. This is not a claim that all368 current complete files match their old
hashes. The original manifest and journal were left unchanged.

This extends the development and arithmetic evidence with supported reserve
localisation and explicit compartment limitations. It does not promote the
pipeline to a universal recipe or establish unbiased absolute photometry.
