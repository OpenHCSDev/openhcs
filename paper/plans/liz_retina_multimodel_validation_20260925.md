# Prospective OpenHCS analysis of Liz's retinal whole mounts

Status: input preparation and diagnostic authoring in progress. No pipeline has
passed visual QA or been frozen. No colleague reference measurements have been
opened or scored.

On goal resumption, the parent agent directly reopened three retained native
raw-plus-ROI bitmaps: R0001's 45-pixel peak-spacing witness, its otherwise
matched 180-pixel maximum-size witness, and R0096's right-side transfer
witness (paths below). The R0001 size change visibly restores coverage of
several broad bright profiles, but adjacent colored identities still divide
some continuous profiles; the R0096 right-side field contains numerous small,
irregular patches without convincing cell-body morphology. These observations
support the existing **reject** decisions, not an accepted count. The
recorded channel/windows and source identities were not re-queried from a
live viewer during that earlier recheck because the MCP server then reported
stale source; the screenshots and prior state notes remain its provenance.
The MCP server was restarted and reported current source for the separate
27 September R0001 matched-channel review documented below.
No held-out image or colleague reference was opened in this recheck.
The canonical development authoring root is
`mcp_outputs/liz_retina_blind_20260925/development/` (16 existing files).
Its public manifest matches a later duplicate extraction at
`/home/ts/liz-rbpms-blind/development/` exactly; use the canonical root for
future OpenHCS work and do not treat the duplicate as an independent sample.
No move into the MCP path-policy root is required.

## 26 September calibration and native-viewer recheck

The Bio-Formats CZI decoder read R0001 at 0.12353054911059548 µm/pixel in
both X and Y, but its source candidates lacked per-plane physical spacing.
The workspace metadata writer therefore replaced the scalar header value with
its uncalibrated compatibility value of 1.0. The source adapter now attaches
the declared X/Y micrometer spacing to each candidate; the focused Bio-Formats
suite passed (43 tests). A new one-image OpenHCS MCP run on a fresh execution
port completed in `trials/parent_exploratory/R0001_calibration_probe/`.
Both its source and output workspace metadata contain 0.12353054911059548,
and all 184 per-object area measurements equal the retained label pixel area
multiplied by that value squared. This fixes the unit calculation for this
image, not the biological segmentation.

The native Napari witness is
`trials/parent_exploratory/20260926T040026497259Z_napari_5598_OpenHCS_Napari_Visualization.png`.
The viewer was isolated to the new raw AF647 image and its matched ROI route;
both report the same 0.12353054911059548 Y/X scale. The raw window was set
from its actual pixels to 4–70 (1st–99.7th percentile). Positive observation:
many colored masks land on bright AF647 soma-like profiles. Rejection/ambiguity:
multiple conspicuous bright profiles remain unmasked, while a few masked
profiles are weak or crowded. Because Liz warned that a smaller underlying
cell layer bleeds through, this view alone cannot classify every unmasked
profile as an RGC. The 184 detections are **diagnostic candidates, not an
accepted RGC count**. Hoechst and spatially separated sparse/dense regions,
plus a declared Z policy for the other files, remain to be reviewed before
parameter tuning or a development-set freeze. The first attempted viewer
stream timed out and partially mixed older pixel-scale layers; it was not
used as QA evidence.

The matched Hoechst witness at the same R0001 viewport is
`trials/parent_exploratory/20260926T040448735464Z_napari_5598_OpenHCS_Napari_Visualization.png`.
The native viewer displays only the selected semantic channel at a time, so
the AF647 ROI route is correctly hidden on the Hoechst slice. The retained
label rasters have 184 cell-body IDs and 483 nuclear IDs. All 184 cell-body
labels overlap at least one nuclear label; a deliberately permissive audit
criterion (at least 25% of each nucleus's area within a cell-body mask) flags
8 cell-body IDs with two nuclei and 13 with none meeting that threshold.
These are inspection targets, not accepted error counts. For example, cell
body ID 163 spans pixels Y=1279–1447, X=1496–1635 and contains 62.5% and
92.5% of nuclear IDs 427 and 428 respectively. Native-viewer closeups of
the same field are retained at
`trials/parent_exploratory/20260926T040652440363Z_napari_5598_OpenHCS_Napari_Visualization.png`
(AF647/ROI) and
`trials/parent_exploratory/20260926T040758727969Z_napari_5598_OpenHCS_Napari_Visualization.png`
(Hoechst). This supports review for merged candidates; it does not establish
ground-truth RGC identity.

R0013 raw AF647 has two Z planes and Hoechst is channel 3. A compile-only
artifact inspection initialized its normal Bio-Formats virtual workspace;
the native direct plane stream initially failed because the shared viewer
loader passed only the `.czi` container path to the Bio-Formats backend. The
viewer loader now uses the declaration-owned `SourcePixelRef` exact plane
address, with a regression test; its affected suite passed (65 tests). MCP
then streamed both planes successfully. Matching 1st–99.7th percentile
limits across both planes were 3–69. The Z1 and Z2 witnesses are
`trials/parent_exploratory/20260926T042056544183Z_napari_5598_OpenHCS_Napari_Visualization.png`
and
`trials/parent_exploratory/20260926T042149383667Z_napari_5598_OpenHCS_Napari_Visualization.png`.
At this field/viewport, many soma-like AF647 profiles are clearer on Z1;
Z2 appears softer while retaining some punctate signal. This is insufficient
to select a dataset-wide Z policy, and a blind max projection is not yet
justified.

R0069 has six Z planes. The same calibrated Bio-Formats source was prepared
without executing a counting pipeline, and AF647 Z1, Z3, and Z6 were streamed
through MCP with a shared 0–49 intensity window. Native-viewer witnesses are
`trials/parent_exploratory/20260926T043030503927Z_napari_5598_OpenHCS_Napari_Visualization.png`
(Z1),
`trials/parent_exploratory/20260926T043813796679Z_napari_5598_OpenHCS_Napari_Visualization.png`
(Z3), and
`trials/parent_exploratory/20260926T043859084780Z_napari_5598_OpenHCS_Napari_Visualization.png`
(Z6). At the inspected viewport, Z1 contains the clearest soma-like profiles,
Z3 is softer, and Z6 is visibly out of focus. This is a local observation,
not a per-file or dataset-wide focus policy. Strong spatial background
variation remains, so a global intensity threshold alone would be unsafe.

The first attempt to navigate to route-local Z index 1 landed on an empty Z2
slot left in the shared viewer domain by another route. That screenshot is
rejected as biological evidence. The navigation code now maps route-local
indices through the route's declared Z values before selecting the shared
axis; the sparse-Z regression and complete viewer test file pass (138 tests).
The live viewer was launched before this code edit, so its Z3 and Z6
screenshots were reached using the old shared indices 2 and 3 and were
independently checked against their displayed Z labels. Restart the viewer
before relying on the corrected route-local indexing in an agent trial.

R0096 is a separate single-Z, three-channel development image. Its AF647
and Hoechst channels were streamed together through MCP and reviewed at the
same native viewport. The AF647 image used its actual 1st–99.7th percentile
limits (4–114), with witness
`trials/parent_exploratory/20260926T044648146749Z_napari_5598_OpenHCS_Napari_Visualization.png`;
the Hoechst witness used 0–87 at
`trials/parent_exploratory/20260926T044809830894Z_napari_5598_OpenHCS_Napari_Visualization.png`.
The AF647 view has conspicuous bright puncta and spatially uneven background
alongside more diffuse soma-like signal. The Hoechst view has many nuclei,
including a denser smaller-looking layer. This is a visual stress case for
cytosolic RBPMS specificity, not evidence that the puncta or every Hoechst
object is an RGC. A later unchanged-detector transfer is described below;
no R0096 count is accepted as a biological result.

The registered `inspect_metaxpress_round_objects` function was compiled and
executed through MCP for R0001 Hoechst using exactly the nuclear settings in
the calibrated soma diagnostic (channel index 1, width 5–30 µm, local
background difference 5). The retained probe is
`trials/parent_exploratory/rbpms_r0001_nuclear_stage_probe.py` and its
`R0001_nuclear_stage_probe/` outputs. Its measurement rows contain 324,284
prefilter labels, of which 483 were accepted; 309,797 prefilter labels had
area below five pixels. The 483 agrees with the previous soma diagnostic's
nuclear-label count. From that diagnostic's exact rasters, 231 nuclear IDs
touch a final soma mask and 252 do not; non-overlap does not by itself mean a
missed RGC, because many retinal nuclei are not RGCs. The accepted-nucleus
ROI archive expanded to tens of thousands of polygons and briefly slowed the
viewer. The additive display of its label TIFF as a second grayscale image
was also rejected as a QA witness because it saturates nuclei. The usable
native raw-Hoechst plus accepted-ROI witness is
`trials/parent_exploratory/20260926T050539642024Z_napari_5598_OpenHCS_Napari_Visualization.png`
at the actual Hoechst 0–42 window. Many accepted masks coincide with bright
nuclei, but some visible nuclei remain unmarked, and a conspicuous large
accepted region merges multiple nuclear profiles. The largest accepted
region has area 56,379 pixels, major axis 43.7 µm and minor axis 29.7 µm.
**Reject the 483 as an accurate nuclear count.** This stage-level failure
precludes treating the 184 soma candidates as validated; a bounded nuclear
detector revision and a separate AF647 soma-stage review are needed before
expansion. Neither count is a manuscript result.

A controlled nuclear-only variant changed only the maximum width from 30 to
20 µm on the same R0001 source, through a separate complete MCP pipeline
document at `trials/parent_exploratory/rbpms_r0001_nuclear_width20_probe.py`.
The compiled one-image run completed. It retained 481 accepted labels versus
483 before, and its largest accepted region is 17,750 pixels rather than
56,379. The same-coordinate Hoechst/ROI witness at 0–42 is
`trials/parent_exploratory/20260926T051929540708Z_napari_5598_OpenHCS_Napari_Visualization.png`.
The giant merged region is absent, but visibly nuclear profiles remain
unmarked and other colored regions still have ambiguous boundaries. This is
an improvement in one failure mode, **not** a QA pass or an accepted nuclear
count. The variant is not applied to the RBPMS soma pipeline, and no
development-set or held-out scoring has been performed.

A second controlled variant retained the original 5–30 µm width range and
changed only the local-background difference from 5 to 8, using
`trials/parent_exploratory/rbpms_r0001_nuclear_threshold8_probe.py` through
the MCP compile/execute route. It completed for R0001 and retained 309
accepted nuclear objects versus the original 483. At the same Hoechst
0–42 display window, the native raw/ROI witness is
`trials/parent_exploratory/20260926T053444152960Z_napari_5598_OpenHCS_Napari_Visualization.png`.
Many faint but clearly nuclear profiles in the left side of this fixed field
lost their masks, while a large merged accepted region remains on the right.
**Reject the threshold-8 variant.** No parameter was propagated into the
RBPMS pipeline. The paired failures indicate that simple width or threshold
adjustment alone is not sufficient for the nuclear stage; inspect the
source-component/watershed evidence or choose a different declared detector
before another broad run.
The largest region in the original probe came from a threshold-stage source
component that produced three watershed outputs; the threshold-8 probe's
largest region came from a source component producing four. Thus watershed
did run, but its surviving large output still merges profiles. Neither
failure can be described as merely a missing watershed invocation.

A third one-parameter probe reduced the Hoechst minimum width from 5 to
3 µm while retaining maximum width 30 µm and local-background difference 5.
The complete MCP pipeline document is
`trials/parent_exploratory/rbpms_r0001_nuclear_minwidth3_probe.py`.
It compiled and executed on R0001, increasing accepted objects from 483 to
733. The original 56,379-pixel merged region survived unchanged, now as one
of four watershed outputs from the same threshold-stage source component.
The native 0–42 Hoechst/raw-plus-ROI witness is
`trials/parent_exploratory/20260926T054454968218Z_napari_5598_OpenHCS_Napari_Visualization.png`.
The additional masks include many smaller or fragmentary profiles, while the
merged region remains. **Reject this variant** as a solution to the observed
failure. The initial ROI stream client timed out, but the viewer state
independently confirmed the revised route was mounted before isolation and
snapshot; the pipeline execution itself completed normally. Stop the
R0001-only width/threshold sweep here. A changed detector or a registered
stage-specific correction must be visually tested on spatially separated
development images before any count is accepted.

Registry search after the rejected parameter probes found
`openhcs:cellprofiler_identify_primary_objects` as a declaration-owned
alternative nuclear detector, as well as registered watershed implementations.
At that point they had not been executed or validated for this assay. The current
`count_neuronal_cell_bodies_metaxpress` internally computes its own nuclear
labels, so a replacement nucleus detector is not yet a drop-in parameter
change; the next pipeline needs an explicit typed artifact relationship or a
separately composed soma workflow before testing it. Do not imply that the
presence of a registered function solves nuclear QA.

An initial attempt to compile that alternative detector as a complete
one-image OpenHCS pipeline failed because the CellProfiler invocation lacked
an exact named input-image/output-object identity. A subsequent diagnostic
`trials/parent_exploratory/rbpms_r0001_cp_nuclei_probe.py` supplied the
identity but initially stopped with `No pattern groups found for step 0`.
In-process inspection identified the authoring error: the step-local binding
asked for alias `Hoechst`, but the native CZI source projections had no such
alias, so source-anchor selection excluded both planes. Declaring the alias
at pipeline level and consuming it through step source bindings resolved
admission. The compiled artifact plan then selected only channel 2, with
0.12353054911059548 µm pixel spacing, and the complete OpenHCS execution
finished as ID `6b407b4e-22fb-4bf5-8e5f-7596483a8fb2`.

The diagnostic output is retained under
`trials/parent_exploratory/R0001_cp_nuclei_probe/`: a nuclear-label TIFF, ROI
ZIP, segmentation summary, and measurement CSV. The measurement reports 547
`R0001Nuclei` objects. This is a **candidate nuclear-label count, not an RGC
count**. ROI streaming reported missing source-plane metadata, while the
label TIFF streamed successfully. The pre-existing viewer was then closed to
release approximately 3.3 GiB of resident memory. A subsequent fresh viewer
showed that the derived label TIFF was inventoried as a second image, making
the otherwise unique source plane ambiguous for ROI streaming. The streaming
service now excludes declared derived-image artifacts when resolving that
unique source; its focused suite passed 14/14. This is a viewer-admission fix,
not a segmentation improvement.

The same-coordinate raw Hoechst plus ROI witness was captured at native
0.12353054911059548 µm/pixel with a 0.5–99.5 percentile raw display window
(resolved 0–37 intensity). The full-field screenshot is
`trials/parent_exploratory/20260926T131451530841Z_napari_5555_OpenHCS_Napari_Visualization.png`;
the zoomed upper-left witness is
`trials/parent_exploratory/20260926T131551677914Z_napari_5555_OpenHCS_Napari_Visualization.png`.
The zoomed witness has conspicuous unmarked Hoechst nuclei and some partial
colored fragments. **Reject the 547-label variant as a reliable nuclear
detector.** The number is not an RGC count. AF647 soma admission and tests on
spatially separated development images remain outstanding. The temporary
viewer was closed after capture to release its approximately 1 GiB resident
memory; retained outputs and screenshots remain on disk.

The next bounded development diagnostic changed the biological source, not
the detector settings: `trials/parent_exploratory/rbpms_r0001_cp_soma_probe.py`
binds AF647/RBPMS channel 1 and reuses the same registered CellProfiler
primary-object detector settings from the Hoechst probe. The MCP artifact
plan selected one R0001 channel-1 source plane and declared durable labels,
ROIs, and measurements; execution `75223bde-c482-4b09-b3da-3b2ae1e0a3ba`
completed. The retained label TIFF contains 503 nonempty IDs (median area
2,759 pixels; largest 11,102 pixels), consistent with the CSV's diagnostic
`Count_R0001RBPMSBodies=503`. The summary counted 503 in-memory ROI objects
before archive encoding, while the ZIP contains 668 `.roi` polygon members
plus one metadata member and the viewer renders 668 polygons. The extra
polygon members do not imply extra biological objects; the generic summary
wording was clarified for future runs. None of these numbers is an accepted
RGC count.

The same-coordinate raw AF647 plus ROI witness used a 1st–99.7th percentile
display window, resolved to 4–70, with the full field at
`trials/parent_exploratory/20260926T133332049634Z_napari_5555_OpenHCS_Napari_Visualization.png`
and an object-scale upper-left view at
`trials/parent_exploratory/20260926T133442537101Z_napari_5555_OpenHCS_Napari_Visualization.png`.
Positive: many colored masks coincide with broad bright AF647 profiles.
Failure: several visibly continuous soma-like profiles are divided into
multiple differently colored objects, and some bright profiles remain
unmarked. **Reject this direct-AF647 variant.** The earliest obvious failure
is over-declumping; test one bounded peak-suppression or unclumping change
before any expansion or held-out scoring.

The one-factor no-declumping ablation is
`trials/parent_exploratory/rbpms_r0001_cp_soma_nodeclump_probe.py`; it compiled
on the same single AF647 source and completed as execution
`144f48ff-6f95-40bb-bf33-77ca4ff330e0`. The materialized raw image is
byte-identical to the prior AF647 trial (SHA-256
`7ad70b565439a7f022872897bc54401b56e344c3efb427669b0ae80334749987`).
Accepted diagnostic IDs fell from 503 to 151, with foreground pixels falling
from 1,620,333 to 807,730 and median retained area rising from 2,759 to
5,863 pixels. At the same native viewport and 4–70 AF647 display window,
`trials/parent_exploratory/20260926T134829288274Z_napari_5555_OpenHCS_Napari_Visualization.png`
shows that several former multi-color splits become single objects (positive),
but numerous broad bright AF647 profiles are now unmasked (failure). **Reject
the no-declumping variant under its original size settings.** The implementation
applies the diameter-area filter *after* declumping, so merged source regions
in this ablation may disappear simply by exceeding the 120-pixel maximum.
This paired result therefore does **not** establish that declumping itself is
biologically necessary; it establishes an interaction between splitting and
the downstream size gate. The automatic peak spacing remains too permissive
for some visibly continuous profiles, while threshold and identity admission
are still unresolved.

An intermediate, one-gate variant
`trials/parent_exploratory/rbpms_r0001_cp_soma_peak45_probe.py` retained
declumping but replaced its automatic peak suppression with a 45-pixel
minimum spacing; all other detector settings and the AF647 source remained
unchanged. It compiled and completed as execution
`ce118c00-9448-4b39-a155-7093bc2900d2`. It produced 307 nonempty label
IDs, 1,462,379 foreground pixels, and a 4,850-pixel median retained area.
The object-scale raw-plus-ROI witness at exactly the prior viewport
`[0,80,80]`, zoom 4, and raw AF647 window 4–70 is
`trials/parent_exploratory/20260926T135532496620Z_napari_5555_OpenHCS_Napari_Visualization.png`.
Positive: it preserves more separated, bright candidates than the
no-declumping ablation while avoiding some of the baseline's severe splits.
Failure: several conspicuous broad profiles remain unmarked, and some
continuous profiles remain split. **Reject as a final detector.** This is a
bounded mechanism diagnostic, not a parameter sweep sufficient to freeze a
pipeline. Review a different development field and expose threshold/size
admission evidence before further tuning. The temporary viewer was closed
after this witness to recover its approximately 0.9 GiB resident memory.

The unchanged 45-pixel-spacing detector was then transferred to the spatially
separate development field R0096, using its AF647 channel 1 rather than the
Hoechst or AF488 channel. The complete MCP pipeline is
`trials/parent_exploratory/rbpms_r0096_cp_soma_peak45_probe.py`; its artifact
plan selected one channel-1 source plane, and execution
`e440b3f2-cc1f-4a3a-b2e1-3af2b56f02ac` completed with retained labels,
ROIs, and measurements under `R0096_cp_rbpms_peak45_probe/`. The CSV and
label TIFF agree on 306 nonempty diagnostic objects (844,964 foreground
pixels), **not 306 confirmed RGCs**. Native raw-plus-ROI QA used the actual
1st–99.7th percentile AF647 display window 4–114. The full-field witness is
`trials/parent_exploratory/20260926T141915167592Z_napari_5555_OpenHCS_Napari_Visualization.png`;
the upper-left and right-side object-scale witnesses are, respectively,
`trials/parent_exploratory/20260926T142028486554Z_napari_5555_OpenHCS_Napari_Visualization.png`
and
`trials/parent_exploratory/20260926T142138146330Z_napari_5555_OpenHCS_Napari_Visualization.png`.
Positive: some broader AF647-positive profiles are masked. Failure: numerous
masks are small, irregular patches on spatially uneven signal, especially in
the punctate right-side region; the visual evidence does not establish they
are cytosolic RBPMS-positive somata rather than background or the underlying
cell layer Liz warned about. **Reject this detector as transferable or a
biological RGC count.** No held-out field was used. The temporary QA viewer
was closed after retaining these witnesses to release roughly 0.8 GiB RAM.

On 26 September, a development-only stage probe retained the unchanged R0096
detector settings while projecting its existing post-split and post-minimum-size
label variants. The versioned diagnostic source and full pipeline are
`trials/parent_exploratory/rbpms_primary_variant_diagnostic_function_v5.py`
and `trials/parent_exploratory/rbpms_r0096_cp_stage_variants_probe_v5.py`.
MCP artifact inspection reported no errors, one selected axis, and two steps;
compile `24407a20-6dad-4175-88b4-a31d5a8ba619` and execution
`8bb862c5-b55e-4249-87be-d4ff61ae44bb` completed. The output is retained
under `trials/parent_exploratory/development_cp_rbpms_stage_variants_probe_v5/`.
Its single image TIFF is pixel-identical to the v3 raw output TIFF, and all
three persisted label rasters are pixel-identical to their v3 partial-run
counterparts. The 2586-by-2586 int32 rasters have 6,359 nonzero unedited IDs
(1,255,245 foreground pixels), 312 after-minimum-size IDs (927,478 pixels),
and 306 final IDs (844,964 pixels). These are stage diagnostics, **not
confirmed RGC counts**. The earlier v2 run failed a stack-shape assertion;
v3 materialized the same label stages but failed on an unnecessary declared
stage-image filename; v4 failed the runtime output ABI because ordinary object
labels participate in main flow. All failed attempts and artifacts remain
retained. V5 declares the two diagnostic stages as QA sidecars and preserves
the input image as the sole main-flow image. A managed native raw-plus-overlay
viewer launch returned `interactive_viewer_unavailable` because no authoritative
graphical session was available; no biological accept/reject decision was made
at that point, and no held-out field was opened.

The native viewer gate was subsequently retried through MCP after an OpenHCS
GUI registered a live UI bridge. The v5 raw TIFF and final step-0 ROI archive
were streamed to the managed Napari viewer on port 5555. Its state showed one
visible 2586-by-2586 R0096 channel-1/Z1/time-1 raw image layer and one visible
ROI Shapes layer (573 polygon features, **not** 573 cells). The raw layer's
1st–99.7th percentile window resolved to 4–114. Same-coordinate full-field,
upper-left (native viewport center y/x 650/650, zoom 1), and right-side
(1000/2100, zoom 1) witnesses were saved. The object-scale overlay/raw-only
pairs are `20260926T221835602538Z_napari_5555_OpenHCS_Napari_Visualization.png`
/ `20260926T221857800151Z_napari_5555_OpenHCS_Napari_Visualization.png` and
`20260926T221912431196Z_napari_5555_OpenHCS_Napari_Visualization.png` /
`20260926T221930091046Z_napari_5555_OpenHCS_Napari_Visualization.png`, all in
`trials/parent_exploratory/`. The authoring agent opened and visually inspected
these bitmaps. A few masks overlap plausibly broad AF647 profiles; however,
many masks are irregular patches on weak diffuse signal, while some compact
bright foci remain unmasked and are ambiguous (possibly the underlying layer,
not automatically missed RGCs). **Reject v5's final 306 IDs as a biological
RGC count or transferable detector.** The v5 stage projection is technically
complete, but it did not change the earlier rejected detector. No held-out
field was used. The GUI bridge disappeared after its GUI process exited with
SIGTERM; the separate MCP-managed viewer remained reachable for this review.

The follow-up R0096 review exposed a channel-selection gap before any detector
retuning: the v5 output plate contains only channel 1, while the physical CZI
has three channels. The original Bio-Formats inventory enumerated all three
R0096 planes, and bounded native samples of channels 1 and 2 succeeded. The
retained AF647/channel-1 and Hoechst/channel-3 native screenshots above were
reopened, but AF488/channel 2 has not yet been visually assessed against the
same cell bodies. An MCP attempt to stream all three source planes, and a
second attempt to stream only channel 2, both returned
`plate_file_stream_failed` / `StorageResolutionError` for synthetic virtual
TIFF paths; neither mounted a new raw channel. Do not infer that channel 1 is
the best cell-body segmentation source from its RBPMS alias or tune its
threshold until all relevant raw channels are compared at matched native
coordinates. The existing rejection of 306 final IDs stands, and the
held-out reserve remains untouched.

Follow-up on 2026-09-26: the source-plane streaming failure above was fixed by
forwarding the inventory-owned CZI `SourcePixelRef` through the viewer stream;
the focused plate-streaming and viewer-streaming tests passed (41 tests). A
fresh current-source MCP session then streamed all three physical R0096 CZI
planes to viewer port 5555. The authoring agent opened matched-coordinate
native screenshots of channels 1, 2, and 3, plus a whole-field channel-2
witness at `trials/parent_exploratory/20260926T232358752187Z_napari_5555_OpenHCS_Napari_Visualization.png`.
Channel 3 visibly contains many nuclei, while channel 1 contains puncta and
broader weak profiles; channel 2 shows broad, spatially variable structure
whose biological identity is still unverified. The apparent left/right
gradient is not merely an automatic display-window claim: at native y=900,
two 32-by-32 samples at x=400 versus x=2100 had medians of 23 versus 13 in
channel 3, 100 versus 20 in channel 2, and 24 versus 26 in channel 1. These
tiny samples can mix tissue and background and do not establish illumination
as the cause. Further whole-field and matched native-crop review under
multiple display windows is required before any correction or threshold
change. The OpenHCS skill was amended to require that review. The 306-ID
result remains biologically rejected; the held-out reserve remains untouched.

Multiscale correction and QA continuation on 2026-09-26: the purported
whole-field channel-2 witness at zoom 0.5 above was a **central-band** view;
the Napari canvas clipped the top and bottom. A viewport center of native
(y,x)=(1293,1293) at zoom 0.15 fit the complete 2586-by-2586 field. The
agent personally opened the full-field raw screenshots for channels 1, 2,
and 3 at `20260926T233026612699Z`, `20260926T233027084731Z`, and
`20260926T233027588013Z` (same trial directory; `_napari_5555_OpenHCS_Napari_Visualization.png`
suffix). Channel 3 nuclei and channel 2 structure fade toward the right;
channel 1 contains broad weak profiles and scattered sharp puncta with a
different spatial pattern. This is not evidence that the gradient is purely
illumination rather than tissue/focus/staining variation.

Matched native-crop centers (y,x)=(900,400) bright-left, (900,2100)
dim-right, (1293,1293) center, and (2100,2100) lower edge were then reviewed
in all three channels at the same zoom 1. Whole-field percentile windows
1–99.7 and 1–95 resolved respectively to channel 1: 4–114 and 4–42,
channel 2: 1–255 and 1–130, channel 3: 0–87 and 0–40. The 1–95 windows
make faint structure more visible but saturate bright cells and raise haze;
they are display comparisons, not analytical preprocessing. The agent opened
all 24 captured bitmaps. Representative channel-3 witnesses are
`20260926T233109251115Z` (left 0–87), `20260926T233219127279Z` (right 0–87),
`20260926T233219515177Z` (right 0–40), `20260926T233606281217Z` (center
0–87), and `20260926T233709523687Z` (lower edge 0–87), with the same suffix
and directory above. A right-crop display-only 0–20 Hoechst witness at
`20260926T233413892260Z` reveals additional faint nuclear profiles but
also raises noise. The bright-left AF488/channel-2 crop at
`20260926T233108488142Z` and dim-right crop at
`20260926T233218316505Z` show a large spatial signal difference; AF488's
target antibody/marker remains unknown, so its biological role is not
assigned from intensity alone. The right-side AF647/channel-1 crop at
`20260926T233217523489Z` shows both a broad weak profile and sharp foci;
the lower-edge view at `20260926T233707950476Z` is dominated by sharp foci.
Same-coordinate raw AF647 plus v5 ROI overlay at
`20260926T233454158864Z` shows irregular colored masks over diffuse
profiles and unmasked compact foci. Those foci could be non-RGC signal;
neither omission nor identity is asserted from this view. This reinforces
**reject v5**, does not yet support a channel switch or background correction,
and does not open the held-out reserve. The next diagnostic must establish
AF488 identity and local raw-cell-to-background support before authoring a
replacement detector.

R0096 nuclear-stage diagnostic on 2026-09-26: physical CZI metadata was
queried for both R0001 and R0096. R0001 declares channel 1 `AF647-T1` and
channel 2 `H3342-T3`; R0096 declares channel 1 `AF647-T1`, channel 2
`AF488-T2`, and channel 3 `H3258-T3`. The mixed channel-2 labels explain why
an unfiltered Bio-Formats compile over the development directory failed with
`Conflicting label for channel='2'`; a dataset-wide channel-number-to-marker
mapping is unsafe. The antibody or biological target of R0096 AF488 is still
unknown. The registered `inspect_metaxpress_round_objects` diagnostic was
therefore applied to **R0096 Hoechst/channel 3 only**, with AF647/channel 1
retained in the same source stack and no AF488 input. Its source is
`trials/parent_exploratory/rbpms_r0096_nuclear_stage_probe.py`. It transfers
the earlier R0001 nuclear diagnostic settings (5–30 µm object width, local
background difference 5) as a stage probe, not as an accepted nuclear or RGC
detector. Binding-local source filters constrain both aliases to R0096;
the pipeline-level source filter alone did not prevent duplicate source
projection addresses during Bio-Formats workspace initialization. The final
MCP artifact plan had exactly one R0096 axis and two physical source planes,
with channel-1 and channel-3 plane references and the recorded
0.12353054911059548 µm/pixel spacing.

The first execution submission timed out during 30-second preparation and
explicitly reported that **no execute request was sent**. A retry with a
120-second submit budget completed as execution
`4b0b102e-09f4-46b2-b500-afc435b033a2` in approximately 170.6 seconds,
under `trials/parent_exploratory/development_nuclear_stage_probe/`. The
runtime log reports 39.425 seconds in the diagnostic function and 74.394
seconds in step finalization; before the selected-axis compile, Bio-Formats
opened all 16 development CZI containers. The persisted widths CSV contains
297,177 data rows. The stage summaries report 188 accepted and 10,121
prefilter ROI objects **before archive encoding**, while the respective
ROI ZIPs contain 27,627 and 108,281 entries. These are not biological cell
counts; the large expansion requires label/ROI identity and geometry review.
The performance/fidelity investigation is tracked publicly as
`OpenHCSDev/openhcs#132`, without private inputs. No nuclear or RGC result from
this probe has passed a same-coordinate raw-plus-overlay visual gate, no
replacement RBPMS detector has been accepted, and the held-out reserve remains
sealed.

The archive identity check now explains the entry expansion without equating
ZIP members to cells: PolyStore extracts one parent ROI per nonzero label, then
encodes each contour polygon as a separate ImageJ ROI member. The accepted
archive has 27,627 members but exactly 188 distinct parent labels. Parent
label 97 alone has 2,422 contour members, all carrying the same parent area
of 76,866 pixels and bounding box Y=0–375, X=2053–2544. At the declared
spacing, that area is about 1,173 µm² and the box spans about 46 by 61 µm.
The agent reopened the live native viewer through MCP and personally inspected
R0096's raw Hoechst/channel-3 crop centered at Y=162, X=2299, zoom 1, with
the verified 0–40 display limits. Its witness is
`trials/parent_exploratory/20260927T003558201158Z_napari_5555_OpenHCS_Napari_Visualization.png`.
Several separated nuclear profiles are visible in this parent-label region;
the single giant, highly fragmented parent cannot be treated as a plausible
one-nucleus count. **Reject the 188 as a nuclear count.** The ROI overlay was
not loaded because expanding 27,627 shapes in the memory-pressured viewer
would be disproportionate; this raw-only witness is not a raw-plus-overlay
acceptance pass and does not assign particular raw pixels to label 97.
The source of the merged/fragmented mask remains a detector-stage question,
not proof of an ROI-exporter defect. The next bounded diagnostic must inspect
accepted, prefilter, weak-core, adjacent-satellite, and width evidence at
matched coordinates before changing a threshold or considering a replacement.

Follow-up native-viewer QA on 2026-09-27 UTC (same development probe; no
parameter change): the bounded ROI backend streamed all 2,422 contours of
parent label 97 through MCP without expanding the full ZIP. The first overlay
capture was invalid: its older raw-image route had spatial scale 1.0, whereas
the ROI route used the trial plate's 0.12353054911059548 µm/pixel. Re-streaming
the trial's own AF647/channel-1 and Hoechst/channel-3 raw TIFFs gave both raw
and ROI routes the same physical scale. At the same viewer center (Y=20 µm,
X=282 µm), zoom 25, the retained witnesses are `qa/20260927T012218834460Z_napari_5555_OpenHCS_Napari_Visualization.png`
(Hoechst raw, 0.5–99.5 percentiles = 0–79),
`qa/20260927T012334771985Z_napari_5555_OpenHCS_Napari_Visualization.png`
(Hoechst raw, 0.5–97.5 = 0–52),
`qa/20260927T012237439390Z_napari_5555_OpenHCS_Napari_Visualization.png`
(AF647 raw, 0.5–99.5 = 3–92), and
`qa/20260927T012352757676Z_napari_5555_OpenHCS_Napari_Visualization.png`
(Hoechst 0–52 plus label-97 overlay). These paths are relative to
`trials/parent_exploratory/development_nuclear_stage_probe/`. The agent opened
each bitmap. Several distinct bright Hoechst nuclear profiles are clear in
the raw crop; sparse bright AF647 profiles occupy different portions of it.
The pink accepted-stage parent instead covers a broad, irregular swath of
lower-signal tissue/background and many tiny fragments around those nuclei.
No individual label-97 contour can be accepted as one nucleus or one RGC; a
faint nucleus under this merged parent remains ambiguous, not a scored miss.
**Reject this stage output and the 188-label figure as biological counts.**
The held-out reserve and colleague reference remain unopened. The next
diagnostic remains the matched-coordinate accepted/prefilter/weak-core/
adjacent-satellite/width stage comparison, not a threshold change inferred
from the attractive bright foci alone.

The retained `round_object_widths` table further localizes that failure.
Accepted labels 97 and 98 both descend from threshold-stage source component
178, which watershed divided into only two outputs. Their areas are 76,866
and 45,433 pixels; the latter touches the right image border. Their major
axes are 62.90 and 55.59 µm, but their minor axes are 29.82 and 18.87 µm.
The current `round_object_segmentation_stages` admission gate checks **only
the minor axis** against the declared 5–30 µm width interval, explaining
why these long irregular regions survive it. Of the 188 accepted labels,
107 descend from a source component that generated more than one output;
10 accepted labels exceed 10,000 pixels. This is not a mere unsplit-object
or export-count error: a large threshold-stage component formed, watershed
ran, and its few descendants still passed the minor-axis gate. The exact
pixel bridge and seed failure cannot be determined from the CSV alone. Do
not treat a stricter minor-width or global-intensity setting as a justified
repair; the earlier R0001 one-factor width/threshold probes already lost
supported faint nuclei while leaving another giant region. A different
declared detector or stage-specific correction needs a bounded raw-plus-stage
comparison in both bright and dim development regions before any expansion.

The saved R0096 widths table provides a further bounded check: all 297,177
measurement rows have `weak_core_candidate=False` and
`rejected_as_adjacent_satellite=False`; exactly 188 pass the recorded 5–30 µm
minor-axis interval. Within label 97's Y=0–375, X=2053–2544 bounding box,
9,423 prefilter-object centroids occur, but only label 97 is accepted. The
largest other centroid-in-box object has 833 pixels and a 3.80 µm minor axis,
below the 5 µm gate. The empty weak-core and adjacent-satellite ROI summaries
are therefore consistent with the table, not evidence of an exporter miss.
These measurements locate the admission bottleneck but do not reveal which
threshold pixels connected the giant parent or why watershed made only two
descendants; that requires a matched-coordinate threshold/seed diagnostic.

During the same viewer review, a sparse-axis control mismatch was isolated:
the R0096 raw route has channels 1 and 3 at route-local indices 0 and 1,
whereas the shared viewer axis also contains channel 2 at index 1. Native
navigation used the route index, but intensity-window selection used the
shared index. The source fix now derives both directions from the route's
`ViewerLayerAxisProjection`, including ROI-element selection; the affected
viewer tests passed (193 across the broader focused suite). The already-running
viewer process predates this fix, so its live control behavior is not claimed
as revalidated until a fresh viewer process loads the changed source.

On 2026-09-27 UTC, a fresh MCP client (health current; PID 1723719) streamed
only prefilter parent label 6601 from the retained R0096 ROI archive. The
archive sidecar and viewer agree on 37 contour members, one parent label,
area 833 pixels, and bbox Y=72–125, X=2389–2434. Its widths row identifies
source component 6601 with one output (not giant source component 178) and a
3.80 µm minor axis, below the 5 µm admission minimum. Both this ROI route and
the paired trial Hoechst raw route report 0.12353054911059548 µm/pixel,
zero XY translation, and physical channel 3. At native viewport center
`[0,12,298]`, zoom 25, raw contrast limits 0–52, the retained overlay and
raw-only captures are
`trials/parent_exploratory/development_nuclear_stage_probe/qa/20260927T013903499329Z_napari_5555_OpenHCS_Napari_Visualization.png`
and
`trials/parent_exploratory/development_nuclear_stage_probe/qa/20260927T013923031541Z_napari_5555_OpenHCS_Napari_Visualization.png`.
The agent opened both bitmaps. The selected contour fragments lie over dim,
diffuse Hoechst texture; brighter distinct nuclear profiles lie nearby, but
the selected object is not a clear nucleus. **Do not relax the width gate on
this evidence.** This one prefilter label is an ambiguous fragment, not a
validated false negative, and it does not explain the giant accepted parent
97. The held-out reserve and reference remain unopened.

Source inspection narrows the next diagnostic contract: the current detector
forms source components with `ndi.label` on the local-background response
threshold, then uses either smoothed response peaks or distance peaks to seed
watershed. Source 178 yielding exactly two output labels implies that the
retained split used two seeds; the saved widths table does **not** say which
seed surface was selected, where the seeds fell, or which threshold pixels
connected the large source region. A first-class, source-component-targeted
diagnostic should expose those exact stages without changing the detector or
materializing every component as an ROI. Until then, neither a threshold
change nor a claim about the specific bridge is supported.

Additional raw-only R0096 visual grid on 2026-09-27 UTC used the current MCP
viewer, physical AF647/channel 1 and Hoechst/channel 3, matched stage-center
coordinates `[Z,Y,X]` in µm, and gamma 1.0. The agent opened every bitmap in
the grid. Witnesses below share the directory
`trials/parent_exploratory/development_nuclear_stage_probe/qa/`; each short ID
expands to `20260927T<ID>Z_napari_5555_OpenHCS_Napari_Visualization.png`.
The windows are display limits, **not detector thresholds**.

| Center `[Z,Y,X]`; zoom | Hoechst ch3: window → witness | AF647 ch1: window → witness |
| --- | --- | --- |
| `[0,159.7,159.7]`; 1.1 (whole field) | 0–52 → `014432035510`; 0–79 → `014520431077` | 3–92 → `014545831344`; 3–65 → `014602682998` |
| `[0,80,80]`; 8 (bright interior) | 0–52 → `014658182121`; 0–79 → `014658524626` | 3–65 → `014647435828`; 3–92 → `014647780520` |
| `[0,230,220]`; 8 (dim interior) | 0–79 → `014752838210`; 0–52 → `014753178649` | 3–92 → `014753563748`; 3–50 → `014753905464` |
| `[0,45,275]`; 8 (dark upper-right edge) | 0–79 → `014937363147`; 0–52 → `014937734079` | 3–50 → `014936643822`; 3–92 → `014936978992` |
| `[0,270,45]`; 8 (bright lower-left edge) | 0–52 → `015010786786`; 0–79 → `015011122248` | 3–92 → `015011541969`; 3–50 → `015011878784` |
| `[0,230,220]`; 20 (dim object scale) | 0–79 → `015049666220`; 0–52 → `015049934689` | 3–92 → `015049045288`; 3–50 → `015049348490` |
| `[0,45,275]`; 20 (dark object scale) | 0–52 → `015144498571`; 0–79 → `015144771574` | 3–92 → `015145181984`; 3–50 → `015145488040` |

At whole-field scale, nuclei are brighter and denser toward the upper-left
than the lower-right, with a conspicuous dark upper-right region. Hoechst
still resolves multiple nuclei at the dim-interior site, but its 0–52 window
clips bright centers relative to 0–79; at the upper-right object-scale site,
the dark region remains nearly empty under both windows, with nuclei only at
its margin. AF647 has sparse bright puncta and broad, spatially variable
texture. Its lower upper limits make mottled background more prominent and
clip puncta, especially at the bright lower-left edge; these changes cannot
establish additional cell bodies. The channels therefore cannot be
interchanged for this diagnostic, and one global display impression is not
representative. No cause of the uneven background, revised threshold,
biological count, or held-out result is inferred. The R0096 nuclear-stage
probe remains **REJECT** pending matched-coordinate threshold/seed evidence
and raw-plus-overlay object review.

An exact component trace now resolves one cause of that rejection. The
declaration-owned `inspect_metaxpress_round_object_component` diagnostic ran
via MCP on development R0096 with physical AF647/channel 1 and
Hoechst/channel 3 bound together; only Hoechst was segmented. The compiled
plan selected two source planes, and isolated execution
`1907ecb9-6f82-481b-8904-878cf0457128` completed in
`trials/parent_exploratory/development_component178_trace_v7/`. At response
threshold 5, source component 178 spans 122,299 pixels and bounds
`Y=[0,761), X=[2053,2586)`. The production splitter selected two *distance*
seeds, `(Y,X)=(92,2235)` and `(401,2501)`, no intensity seeds, and produced
two descendants. This agrees with the prior stage-probe descendants 297120
and 297121 (76,866 and 45,433 pixels); it is not evidence of two nuclei.
The V7 decision/seed tables, three channel-3 ROI archives, and response and
seed-surface checkpoint TIFFs were retained. The object-subject relation is
declared on both measurements, but the multi-source CSV still omits a channel
column; the compiled bindings and `w3` ROI/checkpoint filenames establish
physical channel 3. V7 checkpoint TIFF hashes match the visually reviewed V6
run byte-for-byte.

V6 MCP viewer witnesses in `development_component178_trace_v6/qa/` were
opened at matched coordinates. At `[Z,Y,X]=[0,30.8,292.5]` µm, zoom 8,
raw Hoechst 0–79 (`025312633764`) and 0–52 (`025457087458`) show several
distinct bright profiles and dim inter-profile signal. The source mask
(`030606698548`) joins a broad region across those profiles; the split and
seed overlay (`025250270009`) divides that region only into two large parts.
At seed-centered zoom 20, raw-plus-seed witnesses `025600782341` and
`025630178968` place the markers in diffuse signal, not clearly isolated
nuclear centers. Matched AF647 at the second site, 3–92 (`025713599372`)
versus 3–50 (`025740080624`), gains texture and clips bright puncta without
resolving a cell boundary. The displayed windows are not detector thresholds.
Reject this component as a biological nuclear object; no RGC count or
whole-field threshold change follows from it. Streaming the checkpoint TIFFs
to Napari did not settle, so their pixels were not visually accepted as
viewer layers; the raw/ROI gate above is the visual evidence.

The manual checkpoint replay defect was traced to a missing singleton
`plane_component_values` projection, not to a longer viewer timeout. The
persisted source-artifact projection already declares the channel-3 plane and
the fixed execution coordinates. The replay path now derives the one remaining
pixel-plane component from that typed projection and fails closed when it is
ambiguous. Focused streaming/component tests pass (71/71). A fresh MCP replay
of the V7 response checkpoint mounted on the existing Napari viewer with
channel 3, shape `[1,2586,2586]`, 122,299 nonzero pixels, and no pending
update; targeted viewer validation passed. The stream API still returned a
global settlement error because that shared viewer retains two earlier,
unmounted routes from the bad payloads. Replaying the old V6 route did not
clear its invalid items. The new route proves transport of this checkpoint,
not biological acceptance; the earlier raw-plus-ROI reject decision stands.
The receiver's settlement check now scopes failures to routes touched in the
current stream cycle while retaining earlier route errors for diagnostics; a
failed route in the current cycle still fails closed. A receiver-level test
confirms that a later valid image batch returns successful settlement while
the earlier route failure remains inspectable. The affected Napari
settlement/streaming suites pass (177 tests). The running user-owned viewer
predates this edit and the embedded MCP client still reports stale source, so
the stream API's live return value has **not** been revalidated after this
change. Do not describe the shared viewer as repaired on test evidence alone.

To localize the conspicuous broad-profile misses in R0001, the next
development-only ablation changed only `exclude_size` from `True` to `False`
in `trials/parent_exploratory/rbpms_r0001_cp_soma_peak45_no_size_probe.py`.
The complete MCP artifact plan compiled for exactly one AF647 channel-1 plane,
and execution `07126ae8-f77b-49e7-ad0e-fb17732ff409` completed with labels,
ROIs, and measurements in `R0001_cp_rbpms_peak45_no_size_probe/`. Its label
TIFF contains 5,644 nonempty diagnostic IDs, but 5,323 have area below the
declared 30-pixel minimum-diameter equivalent, while 14 exceed the original
120-pixel maximum-diameter equivalent; the median area is only 22 pixels.
**Reject disabling size rejection outright:** the resulting field is dominated
by fragments, not a plausible cell count. This was a gate-localization run;
no biological number or pixel-level visual acceptance is claimed from its
unreviewed no-size overlay. The retained artifacts remain available for
further exact-coordinate review.

The targeted follow-up retained size rejection and changed only
`max_diameter` from 120 to 180 pixels (about 14.8 to 22.2 µm at the recorded
0.12353054911059548 µm/pixel):
`trials/parent_exploratory/rbpms_r0001_cp_soma_peak45_max180_probe.py`.
Its MCP artifact plan again selected one AF647 source plane and execution
`57499b53-7818-48af-8308-f2cffff71cec` completed. The source TIFF SHA-256
matches the 120-pixel variant exactly
(`7ad70b565439a7f022872897bc54401b56e344c3efb427669b0ae80334749987`).
Retained labels rose from 307 to 321, with 204,299 newly masked pixels and
zero removed pixels; all 14 added objects are above the old maximum-area
threshold. The ROI ZIP rendered 480 polygon shapes, which is not a cell count.
The personally inspected raw-plus-ROI witness at the same native viewport
`[0,80,80]`, zoom 4, and AF647 1st–99.7th percentile limits 4–70 is
`trials/parent_exploratory/20260926T145217665917Z_napari_5555_OpenHCS_Napari_Visualization.png`.
Positive: several previously unmarked broad bright profiles are now covered.
Failure or ambiguity: some adjacent broad profiles are still split into
multiple identities, and the raw AF647 morphology alone does not establish
that every newly admitted bright region is an RGC soma rather than bleed-through
or another cell. **Reject as a final RGC detector.** The size gate explains a
bounded subset of misses, but not identity or split correctness. Held-out
images remain unopened. The temporary viewer was closed after the witness to
recover approximately 0.8 GiB resident RAM.

A read-only pixel audit of the three retained R0001 label rasters confirms the
mechanism more narrowly: every pixel in the 307 masks accepted at the
120-pixel maximum remains foreground at 180. The 14 newly admitted masks,
totaling 204,299 pixels, each match one complete mask in the no-size run
pixel-for-pixel. Thus this size
setting changes final admission, not the candidate pixels or declumping for
those 14 objects. They span the field; representative native-coordinate
review targets are `(Y,X)=(259,956)` (new label 23), `(704,2157)` (76),
`(1743,2187)` (198), and `(2325,55)` (286, border). Their AF647 within-mask
medians are respectively 34, 38, 27, and 32 digital levels, against local
10-pixel-band medians 19, 18, 13, and 17. These are prioritization statistics,
not evidence of RGC identity or acceptance. At the next current-source MCP
viewer session, review raw AF647 and Hoechst at matched coordinates, whole-field
and object scale, under multiple numeric windows with the 180-pixel labels;
retain and personally inspect the bitmaps before any further detector change.
The earlier R0001 calibration trial's AF647 TIFF has the same SHA-256 as this
probe, so its channel-2 nuclear-label raster can be used to prioritize those
views without treating it as ground truth. Of the 14 new AF647 masks, labels
23, 118, and 141 each contain at least 25% of two distinct diagnostic nuclear
labels; labels 25, 57, and 286 overlap none. The 25% rule is deliberately
permissive and that nuclear detector has not passed biological QA. These
observations flag possible merges or unsupported masks for matched-channel
review, not six established errors or a revised RGC count.
Across a fixed 3-by-3 grid of this R0001 AF647 field, raw median intensity
ranges 14–19 and the 180-pixel mask covers 19.8%–32.7% of pixels per grid
region. These spatial summaries motivate distributed viewing; neither metric
distinguishes staining, focus, tissue, or illumination effects.

On 2026-09-27, the restarted MCP server reported current source and the
authoring agent personally reviewed native-viewer bitmaps from both physical
R0001 planes: channel 1 `AF647-T1` and channel 2 `H3342-T3`, each at
0.12353054911059548 µm/pixel. The same 3-by-3 field positions were sampled
in 256-pixel raw crops in both channels; AF647 crop medians ranged 13–24 and
Hoechst 1–4 digital levels. Whole-field views and zoom-4 and zoom-12 crops
at center, southeast, new-mask labels 23 and 198, and border label 286 were
also inspected. AF647 display windows 4–70 and 4–45 and Hoechst windows
0–42 and 0–22 were compared at matched positions. These are *display-only*
windows: the tighter settings reveal dim structure but saturate bright
interiors. In the southeast, AF647 shows broad profiles while Hoechst resolves
many distinct nuclei; spatial brightness and morphology vary across the field.
Neither channel alone establishes RGC identity.

The max-180 ROI route mounted 321 object identities represented by 480 polygon
members, with no reported coordinate gaps; raw planes and ROI shapes share the
native scale and origin. At `(259,956)` label 23 (area 19,502 pixels; two
polygons including a hole) covers several adjacent AF647 lobes, a concrete
merge/split concern. At `(1743,2187)` label 198 (13,710 pixels) spans a
two-lobed profile. Label 286 (12,703 pixels) touches the left image border,
where the Hoechst view is weak or ambiguous. These are visual audit flags, not
verified errors or cell counts. Selected same-coordinate witnesses, relative
to `trials/parent_exploratory/`, are the raw southeast AF647/Hoechst zoom-4
views `20260927T041704829895Z_napari_5555_OpenHCS_Napari_Visualization.png`
and `20260927T041706031670Z_napari_5555_OpenHCS_Napari_Visualization.png`,
and raw-plus-ROI label-23 and label-198 zoom-12 views
`20260927T041413464828Z_napari_5555_OpenHCS_Napari_Visualization.png` and
`20260927T041437635635Z_napari_5555_OpenHCS_Napari_Visualization.png`.
The shared viewer predates the receiver settlement fix: stream calls returned
a settlement error or timed out despite later target-state checks confirming
these new routes mounted. The live stream return-path fix remains unvalidated.
**Keep max-180 rejected as a final detector** and held-out images sealed.

A further same-session overlay pass kept raw AF647 at 4–70 and compared the
max-180 ROIs at center and southeast (zoom 4) and near new label 76
`(704,2157)` (zoom 4 and 12). The center and southeast fields contain
covered bright profiles but also small isolated colored fragments and
different identities on adjacent bright lobes; these are review flags, not
verified individual-cell classifications. At label 76, raw AF647 shows a
broad irregular bright profile, whereas matched Hoechst at both 0–42 and
0–22 shows one prominent nuclear region in that crop. **Do not classify label
76 as a proven merge merely from its large AF647 mask.** Matched zoom-12
witnesses are the overlay
`trials/parent_exploratory/20260927T042323498774Z_napari_5555_OpenHCS_Napari_Visualization.png`,
raw AF647
`trials/parent_exploratory/20260927T042341150583Z_napari_5555_OpenHCS_Napari_Visualization.png`,
and Hoechst 0–42
`trials/parent_exploratory/20260927T042354935120Z_napari_5555_OpenHCS_Napari_Visualization.png`.
The viewer was left open on the center raw-plus-ROI view; no detector
parameters, held-out inputs, or references were changed.

The next bounded development-only declumping diagnostic is
`trials/parent_exploratory/rbpms_r0001_cp_soma_peak30_max180_probe.py`.
Relative to peak-45/max-180 it changes only the allowed local-maxima distance
from 45 to 30 pixels and writes to a separate output plate
`trials/parent_exploratory/development_cp_rbpms_peak30_max180_probe/`.
MCP compile `00b1f355-f108-4b5e-99ad-e3ef45c77d08` and one-well execution
`ba3afbac-ff5f-4fb2-82d2-44578fce2f2c` completed on R0001. The retained
raw AF647 TIFF has the same SHA-256 as peak-45/max-180
(`7ad70b565439a7f022872897bc54401b56e344c3efb427669b0ae80334749987`).
The new summary reports 404 ROI object IDs versus 321 before, **not 404
verified cells**. The viewer payload independently resolves 404 IDs from
567 polygon members and identifies the new output path. Its ROI and raw
routes both report channel 1, R0001, native XY scale 0.12353054911059548,
and zero translation. The shared route key is the same as the earlier ROI
basename, so the payload path—not layer title or key—identifies which probe
is mounted.

Read-only, full-resolution label-tile comparison at fixed source coordinates
found no foreground gain or loss in the sampled tiles. All 19,502 pixels of
old label 23 map to four new IDs (8,024, 7,064, 2,793, and 1,621 pixels);
old label 76 maps to two (12,251 and 1,660); old label 198 maps to three
(6,261, 5,473, and 1,976). These numbers establish repartitioning of these
*sampled* masks, not full-field foreground identity or biological correctness.
The authoring agent opened raw-plus-new-ROI native-viewer bitmaps at center,
southeast, and labels 23, 76, and 198. Positive: some broad clustered AF647
regions receive separate identities. Failure/ambiguity: a small new sliver
splits from label 76's broad AF647 profile despite only one prominent nuclear
region in the matched Hoechst crop; center and southeast retain many small
fragments. Key zoom-12 witnesses, relative to `trials/parent_exploratory/`,
are `20260927T043507486596Z_napari_5555_OpenHCS_Napari_Visualization.png`
(23), `20260927T043507796206Z_napari_5555_OpenHCS_Napari_Visualization.png`
(76), and `20260927T043508094924Z_napari_5555_OpenHCS_Napari_Visualization.png`
(198). **Reject peak-30/max-180 as a final detector.** The new ROI stream
call timed out at the old viewer, but subsequent target-state and payload
checks confirmed its new route mounted; this does not validate the receiver
return-path fix. No held-out images or colleague reference were opened.

The related CZI calibration, exact-plane viewer loading, and sparse-axis
navigation changes passed 179 affected Bio-Formats/Napari tests plus 17
viewer-replay tests on 26 September. Those tests establish the infrastructure
behavior exercised here; they do not validate the biological masks. The
viewer was a pre-fix process for sparse-axis navigation. It was closed after
the later diagnostic to recover memory; its prior QA screenshots remain on
disk.

After the PC restart on 27 September, the OpenHCS GUI was relaunched and its
Plate Manager restored the neutral development root, the peak-30/max-180
diagnostic output, and the matched R0001 calibration output as separate rows.
The development row initialized; no detector was rerun. A fresh Napari viewer
on port 5555 mounted the retained AF647 image, peak-30 ROIs, and Hoechst
image. The rejected probe's saved PipelineDocument remains at
`trials/parent_exploratory/rbpms_r0001_cp_soma_peak30_max180_probe.py`;
it was not imported into the empty GUI editor because its declared output
path points at the retained diagnostic destination. Viewer state confirmed
R0001, channel 1 versus 2, one Z plane,
2586-by-2586 raw images, equal 0.12353054911059548-µm XY scale and zero
spatial translation. Same-center object-scale bitmaps were personally opened:
`trials/parent_exploratory/20260927T174628129744Z_napari_5555_OpenHCS_Napari_Visualization.png`
(AF647 4–70 with peak-30 ROIs) and
`trials/parent_exploratory/20260927T174644194122Z_napari_5555_OpenHCS_Napari_Visualization.png`
(Hoechst 0–42). The earlier rejection remains; this is restored QA state,
not an accepted count.

The first selected-plate stream MCP call exceeded the client's 10-second
`tools/call` boundary, but the viewer process and both requested routes later
proved live. A second stream into that warm viewer returned in 0.6 seconds.
The current capability calls `PlateStreamingService.stream_files` synchronously;
its cold path waits up to 30 seconds for viewer readiness, then loads and
settles image/ROI payloads before returning. It has no operation receipt or
pollable stream status, so a client timeout is ambiguous and should be
reconciled against viewer endpoints/routes rather than retried blindly.

## Diagnostic failure and acceptance gate

The first Sol-authored R0001 pipeline compiled and executed but is rejected:
its native-coordinate AF647/ROI overlay missed conspicuous broad AF647-positive
profiles and colored small fragments instead. The initial viewer capture had
the raw layer hidden, so it was not valid QA evidence. The corrected witness is
retained in `mcp_outputs/liz_retina_blind_20260925/trials/sol/` with the attempt
log. The output also reported a 1.0 pixel-size value despite the Bio-Formats
source header's 0.12353054911059548 µm/pixel; its old physical-area values
remain invalid even though the later parent diagnostic resolved calibration.

A separate parent-authored RBPMS-only diagnostic on R0001 produced a closer
looking overlay, but its 247 candidate IDs are provisional. It is neither an
independent model trial nor a validated count. The retained ROI archive expands
247 IDs into 36,281 polygons, so ROI entries cannot be counted as cells; the
exact label raster and ROI projection still need reconciliation. The current
single-Z diagnostic also does not define a policy for the multi-Z files.
Its retained generic ROI summary wrongly calls 36,281 polygons “cells”; the
writer has been fixed for future outputs, while the diagnostic artifact is
preserved unchanged.

For every candidate, the acceptance gate is a retained, same-native-coordinate
witness with the verified AF647 channel and labels visible together at a scale
where individual profiles can be judged. Review spatially separated sparse,
dense, bright, and dim regions; record clear misses, unsupported detections,
splits and merges. Verify channel, Z plane, component registration, display
limits, persisted label IDs, and physical calibration before a count is quoted
or the run widens. A successful compile, execution, or plausible aggregate is
not a substitute. The authoring agent must open and visually inspect each
captured witness itself, log a clear positive and possible miss or ambiguity,
and record an explicit accept/reject decision. A viewer-state JSON or another
agent's summary cannot substitute for this. The installed OpenHCS skill and
MCP image-analysis guide now state this gate explicitly.

## Question and input

Can separate AI models use the same OpenHCS skill and MCP surface to build a
reviewable RBPMS-positive retinal ganglion cell counting workflow from Liz's
whole-mount images? The source ZIP has 97 retinal CZI files and 29 CTB optic
nerve CZI files, plus two prior-results workbooks. This first study concerns
RBPMS counting. CTB regeneration is a separate assay with a separate endpoint.

The completed ZIP passed `7z t`; its SHA-256 is
`417a9b9a89b214e9cdedbd45f4f7c157ead672de434e6bf85f82b748cb5899e1`.
The neutral source preparation is implemented by
`benchmark/prepare_liz_retina_blind.py`. It selected one image from each of 16
specimen/condition folders for development using a fixed hash seed and reserved
81 for evaluation. Original names and split mapping are in a private receipt
outside the authoring root. The workbooks remain in the ZIP and are withheld.

OpenHCS Bio-Formats inspection of all 97 neutral CZI files found AF647 in
channel 1 and Hoechst in channel 2 or 3 depending on whether AF488 is present.
Images have one to six Z planes. Every channel-layout and single-plane versus
Z-stack class in the evaluation reserve also occurs in development. The
reported physical pixel size is 0.12353054911059548 µm. The per-file header
inventory is retained with the private split receipt.

## Independent authoring protocol

### Independent RBPMS comparator option (not yet executed)

Two published/open-source RBPMS counting implementations are plausible
*comparators*, not reference truth. The [Libby Lab Cellpose repository](https://github.com/abigailbishop/LibbyLabCellpose)
ships distinct RBPMS models trained for 10× Keyence whole-retina images and
40× images; its documented script works with Cellpose 2/3, not Cellpose 4.
[RGCode](https://gitlab.com/NCDRlab/rgcode) is a separate RBPMS retinal
flatmount counting pipeline with command-line use and optional overlay output,
described in its [primary paper](https://pmc.ncbi.nlm.nih.gov/articles/PMC7804414/).
The Libby Lab 10×/40× labels do **not** establish that either model matches
Liz's CZI objective, cell scale, stain, or bleed-through. The known 0.12353
µm/pixel spacing alone is not enough to establish acquisition equivalence.

Before testing either implementation, record its exact source/weight digest,
license, dependency version, input channel and pixel-scale contract, and
isolate its environment from OpenHCS. Use only neutral development images;
retain same-coordinate raw-plus-mask witnesses and apply the same biological
accept/reject gate as an agent-authored OpenHCS pipeline. An external model
would be a pre-trained baseline, not an independently authored agent trial
or cell-level ground truth. This study has not installed or run either model,
no model result has been scored, and the held-out reserve stays sealed.
[Guymer et al.](https://pmc.ncbi.nlm.nih.gov/articles/PMC7409150/)
also show why manual review of poor-boundary/background cells and clumps is
needed when judging RBPMS counts rather than relying on agreement of totals.

Run each model in a fresh context with the same installed OpenHCS skill,
biological brief, 16 neutral development images, time/call budget, and output
requirements. Keep trial outputs separate. The models may use registered
OpenHCS functions, MCP knowledge and examples, typed source bindings,
compilation, ordinary execution, and viewer QA. They must not read the source
ZIP, original filenames, held-out inputs, workbooks, another model's pipeline,
or repository implementation source. Record all attempts and runtime errors.

The sealed, result-free authoring brief for a fresh session is
`mcp_outputs/liz_retina_blind_20260925/independent_trial_brief.md`.
On 2026-09-27 the parent MCP's development source inventory returned 23
*projected AF647/channel-1* planes across the 16 neutral wells: 13 single-Z
files, two two-Z files (`R0013`, `R0025`), and one six-Z file (`R0069`).
Every projected plane reports XY spacing 0.12353054911059548 µm. This
projection is **not** a physical-channel inventory; it cannot establish that
Hoechst or AF488 is absent. A one-plane R0001 diagnostic does not establish
a Z policy or support freezing a workflow for the other development layouts.
A fresh-context phase-1 agent was started with only the neutral biological
brief and development root, but its session did not expose
`openhcs_health_check`. It stopped before opening an image or writing a
pipeline. That attempt has no result, count, or QA status and is **not** an
independent model trial; restart it only in a fresh MCP-enabled session.
Trial A was then started in a separate non-interactive Codex CLI session
`01a0e3fe-d02a-75a1-88ce-312fc6aa32c0` using model `gpt-6-sol`, the same
sealed brief, and isolated output directory
`mcp_outputs/liz_retina_blind_20260925/trials/independent_a_20260927/`.
Its first OpenHCS MCP health check succeeded (server PID 847279, current
source). The attempt stopped before execution: CLI approval policy `never`
denied config creation and viewer capture. Its log is retained in that trial
directory; no count or accepted result exists.
The brief now explicitly forbids using the running desktop UI or replacing its
viewer on port 5555.
Trial B started concurrently in separate CLI session
`01a0e402-37dc-7f91-8b38-e45a14e2852f` using model `gpt-6-astra`, the same
brief and phase-1 limit, isolated output directory
`mcp_outputs/liz_retina_blind_20260925/trials/independent_b_20260927/`, and
viewer port 5851. Its first OpenHCS MCP health check succeeded. Both trials
were blocked by the same CLI approval policy before detector authoring; B's
`TRIAL_STATUS.md` and `mcp_evidence.json` retain the exact failures. The
parent MCP session independently captured a viewer bitmap, and a separate
`--approve-for-me` CLI smoke session successfully captured the same dedicated
viewer on port 5851. Thus the first two attempts were infrastructure failures,
not biological/segmentation assessments. Two new fresh-context attempts with
that tested CLI mode began as `gpt-6-sol` session
`01a0e407-c69a-7961-b3f5-35d8d25a4407` in `independent_a2_20260927`
(viewer port 5577) and `gpt-6-astra` session
`01a0e407-c6b6-79e2-8b80-ee5667293742` in `independent_b2_20260927`
(viewer port 5861). Both phase-1 attempts then ended without an accepted
count. A2 exhausted its 60-call budget after a CellProfiler
`IdentifyPrimaryObjects` reconstruction failure at compile; no run or result
was produced. B2 compiled, but execution failed while materializing label
artifacts outside the output-plate root; its partial cell-body and nuclear
labels were all background in the personally inspected AF647/result witness.
B2 rejected the visible missed bodies and did not widen or tune. Exact
pipelines, job IDs, errors and QA witnesses are retained in each trial root.
Neither agent opened held-out or reference data. These are operational and
diagnostic failures, not two completed scientific comparators.

The biological target is a per-image RBPMS-positive RGC candidate count from
AF647, with Hoechst used as context. Variable stain and bleed-through from a
smaller, denser underlying layer must be assessed in raw images and overlays.
Each candidate workflow must retain labeled objects, per-object measurements,
per-image counts, and explicit uncertainty or exclusion rules. Z handling and
channel selection must be declared and checked against the source metadata.

Freeze the complete PipelineDocument, parameters, OpenHCS/source revision,
development image IDs, execution receipts, candidate counts, and visual-QA
notes before disclosing the 81-image evaluation reserve. Execute the frozen
pipeline without scientific edits on that reserve. Any repair after disclosure
is a separately named version and cannot replace the first prospective score.

## Evaluation decided before reference disclosure

First report operational completeness: images accepted, successfully compiled,
executed, and producing a count; missing or failed images remain in the
denominator. Review raw/label overlays at fixed native coordinates, sampling
dim RBPMS cells, dense regions, bright background, and putative smaller-layer
bleed-through. Count obvious misses and unsupported detections separately.

After both models are frozen, inspect Liz's workbooks for matching per-image
manual counts or annotations. If exact field identities and counting definitions
match, report per-image absolute error and signed bias, plus animal-level
aggregates where identities permit. Matched manual counts can evaluate count
agreement but cannot establish per-cell segmentation accuracy without spatial
annotations. If the workbooks supply only aggregate outcomes, report the
comparison at that level and do not turn unmatched fields into a score.
Retain the first-run predictions, source identities, evaluation script, and
all exclusions. Models are independent authoring trials; images within an
animal are not independent model trials or biological replicates.

## Manuscript boundary

This study can add a prospective, multi-model OpenHCS use case with direct
biological review and count agreement if a matching reference exists. It does
not replace the CellProfiler parity or throughput evidence. Two model trials
show feasibility and failure modes, not a reliable estimate of success
probability across assays.
