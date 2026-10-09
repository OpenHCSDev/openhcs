Laboratory neuronal morphology: independent image analysis
=========================================================

Analyse the released fluorescence images autonomously using OpenHCS MCP and
the frozen packaged use-openhcs skill. Choose the analysis from your own image
inspection and the current function contracts. No prior analysis, accepted
settings, treatment identities, response expectations or reference results
are supplied. Do not consult other trials or the manuscript.

Acquisition and released scope
------------------------------

The released images comprise twenty coded wells, nine fields per well and two
channels per field: 360 TIFF files, 180 paired fields. Channel w1 is the DAPI
nuclear stain and channel w2 is the FITC neuronal signal. Each image is a
1024-by-1024 two-dimensional plane at one Z position and one timepoint. The
declared XY spacing is 1.3556 micrometres per pixel. Fields within a well can
overlap; do not present a sum of field areas or lengths as a deduplicated
whole-well census. Preserve coded well, site and channel identities.

The released coded wells are A52, A49, A30, A37, A31, A17, A34, A02, A32,
A24, A59, A27, A47, A25, A54, A08, A29, A28, A60 and A11. Site numbers are
1 through 9. Filenames encode these acquisition identities as
WELL_sSITE_wCHANNEL_z001_t001.tif. Only these images are authorised.

Biological outputs
------------------

Report detected cell counts, image-supported soma-connected arbor lengths
including supported daughter branches, branching events, and per-cell process
summaries. Retain per-cell and per-field measurements and explicit per-well
aggregation rules. State the operational definition of a process and a branch,
the inclusion rules, and the limits of ownership at crossings or overlaps.
Do not count a crossing as a branching event without supporting evidence.
Do not join structures through unsupported background merely to increase
length or branch counts. Assess genuine dim processes as well as bright ones.
Do not manufacture labels, measurements, treatment effects or biological truth.
Treatment decoding and reference comparison occur after your final freeze;
report coded measurements, not inferred treatment labels or expected responses.

Independent review and freeze
-----------------------------

Inspect distributed raw channels and matched raw-only, result-only and combined
native views yourself. Record supported positives, plausible misses, nuisance
paths, soma/path allocation and ambiguous ownership. Select your final pipeline
from your own QA, not from an evaluator's reference score. Preserve the first
completed prediction, rejected candidates, final source and settings, source
identities, execution receipts, representative QA and measurement exports.
Freeze the final chosen pipeline and its scientific outputs with hashes before
any evaluator accesses treatment identities or comparison responses. Report
limitations honestly; successful execution alone is not biological acceptance.

Use the existing launch packet and your assigned runtime/viewer resources.
Start bounded development before expanding to the full released collection.
Keep scientific payloads and temporary arrays on the declared HDD destination;
keep only small sources, receipts and author history in the HOME workspace.
Retain useful diagnostic stages, not every intermediate array gratuitously.
Do not copy the entire payload tree into a second final directory. Measure
actual resource headroom before expansion. No software installation, new model,
new provider, additional author or independent runtime replay is authorised.
If external scientific or technical correction becomes necessary, retain the
unassisted outcome and mark any ensuing continuation as assisted.

Before operating, read the unchanged launch packet at
$FLEET_INPUT/AUTHOR-PACKET.rst and follow its recorded-client, resource,
freeze and exact owned-process cleanup instructions. This is a fresh author
with no parent scientific history. The configured scientific interval is
undeclared; do not import a historical time limit.
