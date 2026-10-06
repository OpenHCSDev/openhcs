Dirty main checkout reconciliation
==================================

Integration owner: this coordinator. Viewer audit: Singer. Benchmark and
scientific-source audit: Hypatia. Source preservation is complete; selective
integration, issue acceptance and checkout cleanup remain in progress.

The live checkout at /home/ts/code/projects/openhcs remains based on
2bc579ca9e5d3d70a130bec96ee6f001f3dd5c74 (24 September). Direct tool-call history
from this conversation establishes edits there on 26--28 September. This is
historical work, not evidence that the latest manuscript changes bypassed /wt.
Its 57 historical tracked regular-file edits are now stashed after verifying
their preservation, as described below. Its original baseline has not advanced;
submodule edits and untracked inputs/results remain in place.

Lossless source checkpoint
--------------------------

Published branch: recovery-main-checkout-source-20261006.
Commit: 1f9910e560010c984a01979c0add23d366fa66a5.
Parent: the exact original live checkout HEAD above, not current main.
This is an archival checkpoint, NOT an implementation ready to merge.

An isolated Git index in this existing /home/ts/wt checkout captured 70 modified
tracked regular files and selected untracked source/document/lock files.
Separate PolyStore and python-introspect binary patches and the untracked
ObjectState lockfile are retained under docs/validation/main-checkout-recovery-
20261006 in that commit. The manifest records each source size/hash, dependency
HEAD, patch hashes and excluded untracked paths. All committed payloads were
compared byte-for-byte with their captured originals, and the original source
files were checked again before reporting success. Total captured payload:
5178360 bytes. The ordinary live index and files were not used as write targets.

Dataset ZIP, partial browser download and historical benchmark/results files
were excluded and remain at their original paths. The parent commit retains
unchanged tracked source. No dataset, scientific output, history or UNKNOWN
input was removed. Frozen scorers are recoverable as exact Git blobs.

Tracked-source cleanup
-----------------------

All 70 captured source files still matched their recorded hashes immediately
before cleanup. The original index was empty. The 57 dirty tracked regular
files alone were stashed, excluding external repositories and every untracked
path. Stash commit3979d3ad96c8620f369d2b67c6175e12e69a832f is named
"Historical Sept26-28 source; published recovery-main-checkout-source-20261006".
Comparing its 57 files with the published recovery tree returned no differences.
The recovery branch is the durable publication; the stash is additional local
recovery, not the only copy. The checkout remains on its original September24
HEAD rather than being updated over colliding untracked source.

The observed processes whose cwd was this checkout run agent_comms.worker in
a separate Toad environment, not an OpenHCS runtime. No process was stopped.
All312 original untracked files remain. The PolyStore and python-introspect
patch hashes still exactly match their archived patches; they were not stashed
or changed. ObjectState's untracked lockfile also remains. Source classification
and remaining issue disposition continue independently of this completed
tracked-source custody operation.

Determining dispositions
-------------------------

* Exact reverse-patch checks at main79c09a62c proved all local changes in seven
  files already integrated: function_contract_metadata, function_reference,
  lib_registry/registry_service and four website gallery assets/records.
  Refresh this result against the current head before cleanup.
* CustomFunctionSourceNamespace and source-lifetime validation are integrated;
  later canonical changes mean whole-file equality is not the correct test.
* Both execution-session edits are integrated: InProcessCompileInspectionGateway
  compiles the declared pipeline without its former explicit full-catalog
  initialization, and artifact-plan inspection admits plate/managed metadata
  writes before source evaluation and initialization. Later main reports actual
  initialization/compilation stages through EndpointStartupStatus. The old
  latency test refers to the previous gateway API and remains archival, not an
  instruction to move compilation work owned by the other machine.
* Old ViewerWindowGeometry is superseded by ViewerNativeWindowGeometry and
  ViewerNativeDimensions.canvas_size. Do not restore the old declaration.
* BioFormats physical spacing is superseded by the canonical Java decoder,
  which converts OME units and retains optional Z spacing. The old micrometre-
  only helper is not an unmerged fix.
* Inventory source_ref_override is superseded by _inventory_source_projection
  and load_image/project_source_axes. Sole-image ROI component inference is
  superseded by typed ROIArchiveSourceMetadata, not missing functionality.
* ROI parent-label archive filtering is unpublished. Native data_index selection
  after loading is not an equivalent implementation. No specific open bug has
  been established as fixed by this capability.
* The historical singleton checkpoint reader workaround is superseded for the
  original selected-plane producer: bb76b5e44 consumes the explicitly selected
  singleton at SourcePlaneSelectionImageOutput.resolve_source_context, returning
  the plane with its provenance instead of persisting a redundant leading axis.
  Current source retains that behavior and the affected materialization test.
  The old reader inferred an axis from remaining metadata; do not restore that
  inference for an output the current producer no longer emits. Any independently
  created legacy checkpoint remains archived, not silently migrated.
* Sparse route-local index translation and settlement-cycle error isolation are
  unpublished historical patches. Their old methods are absent from main; that
  alone does not establish a current user failure. Preserve their exact tests
  and establish current consumers before considering integration.
* The old ROI summary correction is superseded by 6dce327e6: current materializer
  reports parent labels, not cells. Archive member count and biological count
  remain distinct. No wording transplant is needed.
* PlateStreamingService's historical source-reference override is superseded
  by _inventory_source_projection, which carries record source references,
  metadata and projection entries through the existing workspace projection
  owner. Current code still uses this on ordinary inventory streaming. The
  associated ROI parent-label selective-read extension remains separately
  unpublished; do not mistake it for the already delivered physical-channel fix.
* Round-object component inspection is unpublished. Its production split-stage
  diagnostic needs current-owner adaptation, not wholesale old-file copying.
* Strict workload-count finalization is a historical unpublished benchmark/MCP
  patch, not evidence of a present benchmark defect. The current benchmark
  implementation and final records belong to the agent on Tristan's other
  machine. Compare its current workflow and subsequent main history before
  proposing any change; competing implementation has been stopped. The exact
  old patch remains independently recoverable from the recovery branch.
* score_instance_labels.py and score_point_centres.py plus their tests are
  unpublished sources required by published H001/H002 evidence. Existing
  instance matching does not establish equivalent diagnostic contracts.
* Haase/Liz preparation scripts and preset notes are unpublished acquisition
  provenance, not fixes for runtime preparation cost or viewer QA issues.

Dependency source dispositions
------------------------------

Current main pins python-introspect 83c1efe5ff9933b0fbd8586d2af5c9e7dbbe80ff.
Reading that exact upstream source confirms DocstringExtractor.extract consumes
inspect.getdoc and calls _parse_docstring directly, without reading source.
Its history contains 4e8f8bde5f750d9a50eacac80acd3806123addd8 (PR3), which removed
the same redundant source/AST parsing as the dirty patch. Upstream comparison
establishes that the pinned commit descends from that implementation. The old
production edit is integrated, not an outstanding startup-performance fix.
The local source-unavailability test remains safely in the archival patch.

Current main pins PolyStore a03ce43969170c1974d048668d1cb43d5febfb8f. Its exact
upstream roi.py still exposes load_rois_from_zip(zip_path) without parent-label
selection. Thus the archived selective-reader addition is not integrated there;
its value and callers must be considered separately from existing archive
identity repairs. Do not change borrowed submodule checkouts to perform this
comparison: their checked-out revisions differ from main's pinned revisions.

Recovered scientific tools
--------------------------

The two frozen scorers, their original tests, and the Haase/Liz preparation
scripts are restored unchanged from the recovery commit. These retain the
implementation behind existing scientific records, not a new benchmark
execution path or a recommendation to restart completed studies. The scoring
tests pass (11 cases) using existing NumPy/SciPy/tifffile dependencies and the
actual restored modules. No images were extracted or scientific scores rerun.
This establishes recovery and the original covered scorer behavior; it does
not establish algorithmic optimality for every possible matching problem,
validate arbitrary existing extraction files, or certify biological accuracy.

Issue closure decisions
-----------------------

Current audited remote head: bb3180e04372a1ba33a269fe37b6512c1dc18da7.
PR1072 implements artifact retirement, not any of the source leftovers above.

Issue663 CLOSED: ObjectState PR15 implementing5c6ac06 (mergeddbc3c64) repairs
the exact nested nominal-config merge defect. OpenHCS requires >=1.2.0.
Merged OpenHCS PR664 retains independent receiving of the unchanged recipe:
31 steps, origDNA/origMito/origMemb aliases and VolumeSourceSpatialDomain survive.
The historical failed bundle carried1.1.9. The closure comment identifies this
cause/fix and does not claim every recipe or biological endpoint is validated.

Issue226 is NOT closed merely because PR227 merged: its explicit comment and
receipt retain fresh installed callable/compile/execute acceptance. Current
source registration and primitive parity are established; locate later evidence
or exercise that small actual path before closure.

Issue424 is implemented by PR425 and controls cover both consumers, generated
MCP schema and PipelineDocument roundtrip. Its qualification explicitly leaves
fresh installed catalog/native acceptance distinct. It is not an unpublished
checkout change. Determine that remaining path before recording full closure.

Issues131 and580 retain specific causal-memory and upstream triangulation/
orthogonal acceptance gaps. Related merges alone do not close those gaps.
The rest of the open-issue census is still under commit-level audit.

Issues445 and152 CLOSED after reading current main6c388681f and subsequent owner
history, not just original PR associations. Physical acquisition inventory and
sampling retain exact source references independently of pipeline projection;
PR454's installed C1/C3 and composite acceptance covers the original access
defect. Native navigation derives display order from semantic presentation and
validates the visible graph before mutation. PR748's installed saved scalar/
fractional-Points journey exercised XY/XZ/YZ with source transforms intact.
The actual native stack was Napari0.6.1. Unsupported planar Shapes cross-sections,
simultaneous linked canvases and separate late-WM/triangulation failures are not
claimed fixed. The closure comments retain these precise limits.

Issue620 CLOSED: current FunctionOutputIdentity.component_metadata preserves
acquisition facts separately from filename storage extension (87e190f6a).
The original registered public CPPipe completed with automatic AND named image
publication enabled, four unique images, 720 exact public element comparisons,
unchanged calibration and acquisition hashes. Full original failed/accepted
evidence is automatic-image-publication-620-20261004.rst. The strict persisted
metadata comparison remains intact.

Issue421 CLOSED: current McpDevStdioSession.request uses SDK ProgressNotification
and renews its existing inactivity deadline only for its matching request token;
resident sockets inherit it. Actual generated stdio/socket journeys exercised
2.4-second cold work with a 1.6-second idle allowance, original errors and warm
reuse. Later affine qualification covers successive resident connections.
Evidence: mcp-progress-ack-20261002.rst and mcp-affine-inspection-436-20261002/
receipt.rst. No arbitrary third-party timeout-policy claim is made.

Issue502 remains OPEN with corrected scope: PR503's exact removed-object return
and installed/public default/removed-enabled acceptance are delivered. The
remaining additional-object cardinality case is not covered by its topology
tests: current ABI validation excludes the callable's variadic annotation and
requires an exact return-slot count. The issue comment points to these actual
current declarations rather than asking anyone to redo removed-object repair.

Next delivery
-------------

Adapt useful unpublished families through existing owners in released /wt
checkouts, preserving this recovery branch independently. Tests and affected
real application checks follow coherent implementation. No new environment,
arbitrary memory cap, broad code transplant or routine contributor PR is needed.
Stashing historical source is a final custody operation, not the implementation
or scientific-provenance deliverable. Keep data/history separate and preserve
dependency edits independently before changing the live checkout.
