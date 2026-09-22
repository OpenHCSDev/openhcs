# NeuronCyto II image 1 reference audit

Checked 15 September 2026. This is a retrospective inspection of retained
outputs and published references, not a new execution or an accuracy benchmark.

## Sources

- [Ong et al., 2016, NeuronCyto II](https://doi.org/10.1002/cyto.a.22872).
- [Full article and supplementary-file index](https://pmc.ncbi.nlm.nih.gov/articles/PMC5089663/).
- [Europe PMC supplementary download](https://www.ebi.ac.uk/europepmc/webservices/rest/PMC5089663/supplementaryFiles), successfully retrieved as a ZIP. The small DOCX tables were read in memory; no additional microscopy or video archive was retained.
- [Official testing-image download page](https://sites.google.com/site/neuroncyto/resourcesdownload).

The manuscript supplement records the extracted image 1 values. Source files
and SHA-256 checksums:

| Europe PMC filename | Publisher filename | SHA-256 |
| --- | --- | --- |
| CYTO-89-747-s008.docx | cytoa22872-sup-0008-suppinfo08.docx | `038c28102a467eb56ec30d9c4404a8301b2889629dfb6b16c35a359c0ed645c0` |
| CYTO-89-747-s009.docx | cytoa22872-sup-0009-suppinfo09.docx | `8062f1e9b9cf8bba021b877ba48d0b8dff0cd9b6434991d26f011e444b847c0b` |
| CYTO-89-747-s010.docx | cytoa22872-sup-0010-suppinfo10.docx | `9671c84dc50a7a4e971bbad061f8ab2cc93c58da2964589782fde563a320e7b8` |

Supplement 9 groups eight per-cell GT entries under image sequence 1 before
starting image 6. It does not give spatial cell identifiers or a separate
assertion that every visible cell was annotated. Eight traced cells versus
nine detected neurons is therefore a discrepancy to resolve by spatial
matching, not a measured false-positive rate. The table headers do not state
physical units. Supplement 8's reported total is preserved as printed rather
than recomputed from rounded per-cell entries.

## Input and ROI identity

The fixture is `website/assets/agent/cold-start-workflow-record.json`; Figure 3
is built from the original 0.7.13 video by `paper/figures/build_slas_agent.py`.
Both fixture TIFFs were checked byte-for-byte against their field 1 members in
the cached official archive at
`~/.cache/openhcs/datasets/neuroncyto_ii/Testing image.zip`.
That archive contains 52 `.tif`, eight `.tiff` files and `Thumbs.db`, with no
manual tracing files.

Retained ROI files were inspected under
`mcp_outputs/website-agent-demo/candidate-20260804-13/outputs/plate_openhcs/images_results/`:

- `1_s001_w1_z001_t001_cell_bodies_step1_rois.roi.zip`: `ROI_8` and `ROI_9`
  occupy the bottom soma, with outline-vertex means near (355, 668) and
  (372, 688), in image (x, y) pixels.
- `1_s001_w2_z001_t001_nuclei_step1_rois.roi.zip`: `ROI_8`, `ROI_9` and
  `ROI_10` occupy that region, with outline-vertex means near (358, 685),
  (359, 670) and (372, 683).

These positions locate objects, rather than supplying area-weighted centroids.
ROI ZIPs contain metadata as well as ImageJ ROI records; only `.roi` members
were decoded. The local retained result table contains six branches, matching
the later recapture rather than the original eight-branch summary. The original
and later run identities must therefore remain distinct.

## Corrected implementation run, 15 September 2026

The baseline was reproduced through the current 0.8.5 GUI/MCP execution path.
It retained nine cell-body ROIs and ten nuclear ROIs, including two bodies and
three nuclei at the bottom soma. The new run uses identical raw images and
pipeline settings, with separate outputs under
`mcp_outputs/slas-validation-20260915/neurite/corrected/`.

The nuclear splitter now requires distance peaks with prominence at the
declared minimum object-radius scale. This suppresses pixel-scale maxima along
one nuclear medial ridge while retaining the touching-nuclei regression.
Component distance transforms include exterior background padding.

The final filled neuron artifact now projects cell bodies and expanded final
trace ownership. It no longer publishes the earlier CellProfiler secondary
propagation labels, which could contradict the topology at crossings.

The actual GUI run completed with eight cell bodies and eight nuclei. The
bottom soma and nucleus each have one ROI: body outline mean (364.63, 681.59),
nucleus outline mean (363.55, 679.14), in image (x, y) pixels. Native MCP viewer
captures with only the neuron ROIs and source image visible were inspected;
the bottom soma is intact and the filled crossing ownership agrees with the
thin traces at the two reported locations.

The summary records total outgrowth 1860 pixels, 49 processes, six branches
and one resolved crossover. These are implementation-run measurements, not
agreement with the published manual total of 3832.601 in unspecified source
units. Spatial trace matching and the substantial length discrepancy remain
to investigate before reporting biological accuracy. Matching eight listed
reference cells alone does not establish segmentation or tracing accuracy.

Execution identity: `b2a64589-6fc1-4ac2-8b2b-551818f6273b`.
Native isolated-neuron capture:
`mcp_outputs/slas-validation-20260915/neurite/corrected/captures/20260915T210113074374Z_napari_5613_OpenHCS_Napari_Visualization.png`
(SHA256 `421177bc31e9ce1faa9fe3d4ae1a7c3dfd98ae3e0ad80905f9edd0e077412426`).

Validation: 48 segmentation/topology tests and 68 additional demo/artifact/
synthetic-plate tests passed, using multiprocessing. The additional suite ran
with a 60-second per-test timeout, as did the final 48-test suite. The nuclear
regression includes twelve rotations of one elongated nucleus. Historical
recordings are unchanged.

### Subsequent filled-neurite gap

User review found a short gap in the cyan neuron's left filled neurite. Saved
graph coordinates and a diagnostic plot of the actual enhanced image,
local-background response and detector foreground establish that the measured
path already bridges the detector gap. The filled expansion still clipped that
path against the earlier detector foreground. Its projection now retains final
owned trace support as well as the detector foreground. A regression failed on
the old projection and passes with this fix; a full two-neuron crossing
regression also passes. The post-fix native GUI rerun remains pending the
coordinated MCP/viewer-infrastructure restart.

The expanded segmentation, topology, synthetic-plate, artifact and example
regression command subsequently passed all 118 tests in 24.30 seconds, with
six workers and a 60-second per-test timeout. A later fresh GUI replay supplied
the required live image, label, ROI and graph review; its separate execution
identity, retained files and measurements are recorded in
`current_neurite_replay_summary.md`.

## Remaining reference matching

Locate the manual spatial traces or create independently reviewed annotations
with explicit provenance. Match cells spatially and evaluate crossings
separately from branches. Align length definitions and units before numerical
comparison.
Any corrected run should have a separate pipeline, software revision, outputs
and evaluation record; preserve the original unattended run.

## Measurement ownership audit, subsequent source generation

The retained corrected table combines seed-relative CellProfiler skeleton
counts and total length with a different rooted-path population for median
and maximum process length. A native straight-neurite regression reports five
processes, total 83 pixels and median 83 pixels under that implementation.
Those statistics cannot describe the same five nonnegative lengths. A second
synthetic fixture publishes an 85-pixel owned path but reports 42 pixels after
seed-relative remeasurement. These are implementation discrepancies, not
evidence about agreement with the published manual reference.

The compact neurite function now derives process count, total, mean, median
and maximum from one final rooted-path partition. It does not reassign or
rescale that topology through independent CellProfiler seed propagation.
The separate CellProfiler-compatible skeleton function is unchanged.
Graph projection likewise retains the final topology's owners instead of
re-voting them from a raster: shared path endpoints can only hold one raster
label, whereas the graph retains each crossing path's identity. Its existing
cycle-break projection retains every path rather than deleting loop geometry.

An additional native T-junction audit found that physical junction adjacency
was counted as a branch of the majority owner even when its three arms
belonged to three separately rooted neurons. Branch events must instead require
three incident paths of the same final owner. The topology now retains
`branch_nodes_by_cell`, with each owner's qualifying nodes merged independently
by geometry. Native three-arm regressions cover three owners, two owners and
one owner through both propagated and explicitly assigned ownership.

Read-only NRA context analysis included the OpenHCS package and its external
source dependencies, with tests excluded by the default discovery contract.
It completed in 111.541 seconds, in `exact_compact_global` mode with all 79
detectors analyzed and none omitted. It reported no accepted findings in the
neurite-file report scope. That does not prove numerical or biological
correctness: the native counterexamples above establish obligations beyond
those source detectors. The scan result is retained as
`/run/media/ts/0BA20E780BA20E78/slas-neurite-coded-results-20260915/ownership_scan_20260915.json`.

The fresh, separately identified GUI replay is execution
`e5d9067c-334b-46b7-853b-ca986f94137d`. Its immutable image, label, ROI, graph
and measurement evidence is recorded in `current_neurite_replay_summary.md`.
It must remain distinct from the historical run and does not establish
manual-reference accuracy without compatible spatial annotations and units.
The coherent segmentation/topology/example/artifact/synthetic-plate regression
command passed 116 tests in 19.02 seconds, with six workers and a 60-second
per-test bound. The separate blinded own-data sparse-field diagnostic is
retained as
`mcp_outputs/slas-validation-20260915/diagnostics/A001_sparse_topology_native.md`;
it is supporting development evidence rather than part of the public replay.
