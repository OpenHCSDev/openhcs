# Full blinded neurite-outgrowth analysis

The user requested a full blinded analysis before comparing the results with
MetaXpress or interpreting treatments. This takes priority over further dataset
candidate research. The original images and existing results remain unchanged.

## Blinding and input preparation

- Prepare neutral plate, well and field identities on the external drive.
- Keep the original identities, treatment layout and commercial measurements
  in a separate private evaluation location, outside the author's input root.
- TIFF descriptions contain treatment information. Use lossless copies with
  identifying metadata removed or recoded, not links to the original files.
- Verify identical pixel arrays and retain acquisition calibration, channel
  identities and other non-identifying settings needed for analysis. Preserve
  the original metadata and the identity mapping in the private receipt.
- Expected inventory: two plates, 60 acquired wells per plate, nine sites per
  well and two channels per site; 1,080 fields and 2,160 source images overall.

Preparation is complete. The [safe readiness receipt](../../benchmark/own_neurite_blind_20260915_preparation.md)
records neutral paths, verified counts/calibration, nonidentity-metadata audit,
input fingerprint, focused tests and exact task-copy cleanup totals. No private
identity key or commercial measurement is included in that receipt.

## Authoring and execution

Use a fresh Sol author context with neutral paths and channel information only.
Neither the treatment key nor MetaXpress measurements may inform pipeline
selection, parameter tuning, exclusions or visual QC. The coordinating context
has previously seen the layout, so it must not make label-informed tuning
decisions on behalf of the blinded author.

Use the current OpenHCS GUI and its declaration-owned MCP capabilities.
Choose a reproducible development subset without treatment information, record
all development attempts, then freeze the pipeline and software identity.
Stitch the nine acquired sites of each well into channel-registered mosaics
before segmentation and neurite measurement. Preprocess the channels for
registration, composite them into one reference tile per site, and compute one
shared positions artifact. Re-enter the original input to assemble each
non-composited channel with those same estimated positions. Registration-only
preprocessing must not replace the original pixels used for assembly.
Derive layout, ordering and overlap from retained neutral acquisition metadata,
preserving calibration and source provenance. Analyze each complete well mosaic once so overlapping tiles do not
duplicate cells or truncate neurites at field boundaries.

First test one development well (P002/A21), then assess all six development
wells (A01, A21 and A41 in each coded plate) before freezing the candidate.
Inspect stitching seams, channel registration and duplicated or disconnected
objects alongside biological QC. Execute the frozen pipeline across all 120
acquired well mosaics. Retain failed or missing source fields and incomplete
mosaics explicitly. Save per-cell measurements where supported, mosaic/well
summaries, masks, traces, ROIs and execution records on the external drive.

This user-requested amendment supersedes the initial separate-field development
design. A001-A004 remain unchanged diagnostic records; their single-field
outputs are not the final stitched-well analysis. The source-binding metadata
repair now derives acquisition layout and calibrated source geometry from
source provenance. The existing shared-composite stitching workflow uses
Ashlar CPU to estimate registration positions; acquisition coordinates are
not an image-registration result. Before submitting the stitched candidate, validate the
existing assemblers' signed fractional placement and canvas coverage, refresh
the GUI/server source generation, and exercise normal GUI/MCP compilation and
execution. Acquisition coordinates provide placement, not image-correlation
registration; inspect alignment and seams in the native viewer. Do not manually
patch generated metadata or supply runtime-only artifacts as function parameters.

Visual QC must examine soma/nucleus correspondence, faint neurites, disconnected
traces and crossing ownership across a reproducible sample from both plates.
Record errors without consulting the commercial measurements. Any subsequent
algorithm change creates a separately identified run, not an overwrite.

## Freeze and later comparison

Before unblinding, save the accepted code document, parameter values, source and
software identities, source-field and mosaic completion inventories,
measurements and QC findings.
Only then join the private key and compare matched well summaries with
MetaXpress. Its workbook contains well-level summaries, not cell-by-cell ground
truth. Confirm units and aggregation definitions before claiming numerical
agreement; otherwise distinguish observed trends from unmatched quantities.

Do not introduce dose labels or treatment plots during the blinded stage.

## Initial calibration checkpoint

All 2,160 coded TIFFs are verified ready; see the preparation receipt linked
below. The fresh author initialized P001 and confirmed 60 wells, nine sites and
two channels. Before execution it found that source spacing was 1.3556 but the
plate-level pixel-size artifact still resolved to 1.0: workspace materialization
hardcoded that scalar. Scientific execution is paused while the calibration
owner is repaired and the current UI state is saved for a fresh restart.
Relative CellProfiler spacing and absolute micrometer calibration must remain
distinct; anisotropic spacing remains a valid ingestion input even when it
cannot satisfy a scalar physical-pixel-size request.

The earlier manager-selection concern was a discovery miss: the existing
desktop navigation capability selects rows through the manager's nominal
selection driver. No new selection API is required.

## Development attempt A001

After the calibration and explicit-source reinitialization repairs, both live
plates resolved 1.3556 micrometers per pixel with all 1,080 source images per
plate. The first scientific execution used the unchanged candidate on P002
wells A01, A21 and A41, across their nine sites.

Execution `053b6a2d-2e32-4fc3-888d-7397160e3b6f` is terminal: the runtime
record reports failure and an end time, and the owning server reports worker
cleanup. A01 and A41 exported 18 fields. A21 stopped at site 005 when a
nonempty, edgeless skeleton reached Skan's path constructor. Earlier A21
fields were computed but not exported; retain that distinction in the
completion inventory. The complete trace, field identities/hashes, partial
inventory, terminal status and native QC captures remain in
`/run/media/ts/0BA20E780BA20E78/slas-neurite-coded-results-20260915/attempts/A001`.

The author is parked for a coherent source-generation restart. A retry must have
a separate A002 output root and a coherent source-generation identity.
Neither the candidate nor the full analysis is frozen or accepted. Native
QC must also resolve fragmented nuclear overlays and zero-cell fields; a
dark default fluorescence display is not evidence of absent signal.

An independent measurement audit found that the previous compact neurite table combined
CellProfiler seed-relative trunk counts/total length with rescaled rooted-path
median/max lengths. These are different populations. The repaired function
derives all process-length statistics from the final rooted topology; graph
projection retains those same owners, and branch events require at least three
incident paths of one final owner. It does not remeasure or rescale through
CellProfiler seed propagation. Historical tables remain unchanged.

The coherent affected regression command passes 116 tests in 19.02 seconds
with six workers and a 60-second per-test bound. The exact A21/site005 raw
field completes its native diagnostic with unchanged candidate settings and
the identical isolated-pixel intermediate. That diagnostic is not the
execution-server retry or scientific acceptance. New unit help is declared at
the spacing owner; configuration-reference and knowledge-base tests pass.
The commercial measurements and treatment key stay withheld.

## Development attempt A002

Execution `a5c97e66-019d-48f1-9e72-cfc9eb3819c8` completed all 27 P002
development fields in 375.2 seconds, with a null runtime error and worker
cleanup complete. Its 27 field-summary CSVs and 251 output files remain under
`/run/media/ts/0BA20E780BA20E78/slas-neurite-coded-results-20260915/attempts/A002`.
The formerly failing A21/site005 produced two cells. Their native pixel areas
89 and 79 correspond exactly to exported physical areas after multiplication
by 1.3556 squared, proving calibration in the executed measurements.

Visual acceptance is pending. The native fluorescence display lacks direct
MCP contrast/gamma control, and contour ROIs do not retain exact label pixels
(one observed contour area was 88.5 for an 89-pixel object). The next coherent
source batch adds native image-presentation control and complete integer TIFF
masks alongside existing ROI materialization. It also separates declared
knowledge-resource access from scientific-file permissions. These repairs do
not change the blinded biological candidate. Any repeated computation under
the new materialization contract is A003, preserving A002 unchanged.

P001 development, pipeline freeze and the full 1,080-field run remain pending.
