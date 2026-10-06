Dirty main checkout reconciliation
==================================

Integration owner: this coordinator. Viewer audit: Singer. Benchmark and
scientific-source audit: Hypatia. Source preservation and tracked/dependency
checkout cleanup are complete; selective integration and issue acceptance
remain in progress. Original untracked inputs/results are preserved in place.

The live checkout at /home/ts/code/projects/openhcs remains based on
2bc579ca9e5d3d70a130bec96ee6f001f3dd5c74 (24 September). Direct tool-call history
from this conversation establishes edits there on 26--28 September. This is
historical work, not evidence that the latest manuscript changes bypassed /wt.
Its 57 historical tracked regular-file edits are now stashed after verifying
their preservation, as described below. Its original baseline has not advanced;
dependency edits are independently stashed, and untracked inputs/results remain
in place.

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
All312 original parent untracked files were initially retained. The dependency leftovers were
subsequently stashed independently: PolyStore a2284ef8d9a08487219a9ea4b08f5af7e3c35b7a
and python-introspect adcbec4729250a4739be743f81c4054c83a3b3df. Each complete
stash patch was compared with the published patch hash and matched exactly.
ObjectState's sole untracked uv.lock was stashed explicitly, without other
untracked paths, as439eba29305141b5a58bf6e2b29333b29fb03e1a; its untracked-parent
blob matches the archived file hash exactly. All three original dependency
HEADs remain unchanged. Main and its dependencies now have no tracked dirty
entries. Source classification and remaining issue disposition continue.

After source-family classification, the13 historical untracked source/document/
lock files were checked again against the published manifest: all13 hashes
matched. Only those exact paths were stashed with include-untracked in
d4faf47ed31d8ce36721a28efe5492153202f0c7. Its third-parent tree contains exactly
those13 files and compares byte-identically with the recovery branch. The
remaining299 untracked paths compare exactly with the manifest's excluded
data/download/result inventory. No dataset/output was included in the stash,
and the historical HEAD remains2bc579ca9e. Both tracked and untracked historical
source are now stashed, independently recoverable from published Git custody.

The observed live MCP interpreters use this checkout's venv, but that venv's
OpenHCS editable finder and PolyStore path refer to separate /wt source trees,
not these original dependency checkouts. No interpreter, installed package,
live endpoint or backing /wt source was changed. A referenced old OpenHCS
editable path is absent on disk; no missing-path runtime was restarted or
uncertain operation replayed as part of cleanup.

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
* score_instance_labels.py and score_point_centres.py plus their tests were
  unpublished sources required by published H001/H002 evidence. Their exact
  original bytes are now delivered on main in8522309d1, together with the
  Haase/Liz preparation scripts; all six match the archival blobs. The11
  original scorer controls passed. This preserves the original scientific
  methods, not a universal matching-optimality or biological-accuracy claim.
* Haase preset notes and the Liz prospective study plan remain historical
  acquisition/study provenance in the recovery branch, not fixes for runtime
  preparation cost, viewer QA or a statement of current manuscript completion.

Dependency source dispositions
------------------------------

Remaining historical-source classification
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Hypatia completed the remaining source-family comparison against main888756;
the coordinator checked the determining current declarations/history. The
70-file manifest is the exact archived inventory, not a list of70 missing fixes.

The old README addition and installed-smoke assertions belong to the archived
generic CLI/MCP expected-axis-count exposure. Current measured-run submission
and finalization already accept expected_axis_count, reject mismatches before
writing a success receipt, and retain expected/observed counts. The older
generic capability exposure is not a reason to compete with the current
benchmark integration owner. Historical benchmark tests and the wrapper plan
remain attached to that archived enhancement.

Capability edits for artifact-plan write admission and camera/canvas visibility
are integrated or superseded by the current typed declaration owners. The
historical QA, context and packaged skill edits are retained through the later
canonical guides, including analytical normalization and foreground/marker
evidence; they are not a second skill version awaiting installation. Associated
agent/server/context tests belong to those migrated families. The old geometry
and compile-latency tests target replaced APIs and remain archival.

Metadata partitioning is integrated on
StreamImagePayloadMetadataProjector.partition_item_fields. The historical
viewer-control wording belongs to the separately preserved sparse route-index
enhancement; missing old method names do not establish a present consumer bug.
BioFormats storage/adapter tests follow the producer-side singleton and current
unit-decoder dispositions above. Runtime, streaming, materialization and ROI
tests remain with their exact archived implementation families; no old tests
were transplanted into current APIs or discarded to claim parity.

The excluded untracked inventory contains exactly two acquisition/download
files and297 benchmark/results paths. None is another excluded source tree.
The13 selected untracked source/document/lock files are included in the
published70-file custody inventory and are now stashed as described above.
Untracked results and both original
downloads remain untouched. Derived lockfiles are historical installation
metadata, not a request to downgrade the current dependency graph.

Useful unpublished implementation is limited to the component-level
seed/surface/split diagnostic and parent-label selective archive reader, plus
the route-index/settlement patches whose current applicability remains
unresolved. Their original source and tests are published in the recovery
branch. No established current defect requires a wholesale transplant.

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

Issue424 CLOSED: PR425's declared lower soma gate is retained by both consumers;
13 original controls cover lower-value admission, independent negatives,
generated MCP settings, describe_function and document roundtrip. The later541
installed/public pixel neurite workflow compiled and executed PixelCellBodySettings,
which inherits the same field/gate. That native run used its inherited default;
lower-value behavior is the focused-controls claim, not an invented new native
experiment. This is control exposure, not biological tuning or vendor parity.

Issue907's source repair is merged on main in ed1bbed73. SourceVoxelSpacing now
owns shared declared-frame projection; OpenHCS/BioFormats metadata handlers
consume their actual typed source spacing and no longer promote numeric defaults
to physical calibration. The legacy numeric-to-physical fallback is deleted.
Unknown, relative and conflicting frames remain distinct from a physical scalar;
explicit physical/anisotropic coordinates are preserved. Singer's27 affected
checks passed, including the actual calibrated_metadata/native-coordinate
projection. Saved-reopen installed/public acceptance remains outstanding; no
detector rerun, package activation or biological acceptance is claimed.

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

Current runtime and reporting residuals
--------------------------------------

Issues302 and417 CLOSED against their original acceptance, not extra later
activation notes. For302, the final factored source had two real MCP/native
compile/execute/reset/inventory/reopen journeys with matched raw/result/combined
captures and physical transforms; current mounted-route reset retains this
behavior. This is actual source-qualified application evidence, not repair of
the separate old H002 source-skew installation. For417, the original generic/
selection ownership correction and31 checks include the actual named/ordinary
checkpoint writer/reopen flow. Neither closure claims all viewer states,
installed native acceptance or biological accuracy.

Issue1077 was already automatically closed by merged1078. Its original stale
supplementary benchmark consumers were corrected by the other-machine owner;
no competing benchmark patch or duplicate closure was created.

Issue516 remains a real importer batch-context defect. Public kwarg projection
uses the pre-batch context, but subsequent verification advances context after
the first filter. That can erase Objects selection and recreate competing
RetainedEnabled lineage. Hypatia owns the existing lowerer/projection repair;
the original explicit object relation and complete five-module CPPipe remain
the acceptance target. The strict combiner is not the defect.

Issue529's source relation is repaired by84ba215d6: the object-domain policy
projects invocation payload AND plane projection from the labels binding.
Its original installed SOURCE_BINDING singleton/two-source publication/following
consumer acceptance remains unverified. No output guard weakening or competing
axis fix is assigned.

Issue226 CLOSED after actual installed primitive acceptance. With PYTHONPATH
unset and module origin asserted in the existing0.8.7 site-packages, the original
explicit Centrosome three-pixel reproducer returned exact labels1/1/2 and
-1/-1/-2 for signed markers; process96164 exited0. The existing six provider/
public-primary and eight independent reference controls remain the broader
source evidence. No install, download, native server or scientific replay was
performed. Preliminary attempts stopped before computation: source cwd shadowed
the requested target, then the retired target had no package files. Neither
was counted as acceptance. This closes registered-provider/kernel availability,
not whole-pipeline/native-viewer or biological parity.

Issue132's selected-source and fragmented-ROI fidelity changes are retained on
current main. Its remaining scope is phase-level real-container and dense ROI
profiling, not missing filtering or a claim that archive fragments are cells.
Historical runtime numbers have not been presented as measurements of main.

Issue432 CLOSED after following its remaining native blocker through448:
PR437's singleton composition declaration is retained, the original installed
public pipeline produced exact C2/65535 values and calibration, and449's actual
native acceptance reopened that SAME failed singleton output. All64 pixels
were sampled exactly and matched raw/result/combined camera/canvas captures
were reviewed. This does not claim the separate grayscale-renaming recipe or
raw-integer units. The final native receipt is448 comment5951807619.

Issue169's source cause is implemented in current pinned ArrayBridge1e53d03d:
ThreadGPUContext owns thread-local runtime storage outside the by-value callable
globals. The real ObjectState/PipelineObjectStateBinding continuous save/load/
undo test retains the unpickleable runtime handle and executes the restored
historical callable. Its explicit installed desktop capture/restoration
acceptance remains separate and unverified. The disposed H001 history cannot
be reconstructed; Tristan accepted current-declaration export and closure.
The issue now states that remaining scope, rather than calling its old source
implementation missing or conflating it with131 causal retention.

At main888756bbd, issue385 is a real OpenHCS consumer gap. Reading the EXACT
main-pinned ZMQRuntime29e2a869f confirms VisualizerProcessManager already retains
EndpointProcess and delegates its exact-child stop. The borrowed submodule
checkout is a different revision and was not used as current-source evidence.
OpenHCS launch_detached_viewer still returns a raw Popen, and
terminate_owned_viewer_process clears self.process in finally. After failed
acquisition/cleanup, StreamingViewerLifecycle constructs a launch failure from
the request/log, without the original child identity or stop disposition.
PlateStreamingService publishes the log path only. The dependency owner exists;
its launch/failure consumer migration remains. Historical missing evidence is
not recoverable from a later successful viewer, and no operation was replayed.

Issue407 is narrower than its original whole-family receiving note. PR413 and
later672e7c4c7/6b76266c4/7ee00fda5 delivered original typed summaries, sample/ROI
records, receipt admission and their presentation consumers. Current
ViewerNavigationRenderer and ViewerSnapshotRenderer still use raw maps;
RuntimeServerRenderer still reconstructs runtime counts from raw responses.
These concrete remaining readers keep407 open, not an assumption that completed
native geometry or segmentation is broken. Both issue comments now identify
the current owners and remaining consumers explicitly.

Next delivery
-------------

Adapt useful unpublished families through existing owners in released /wt
checkouts, preserving this recovery branch independently. Tests and affected
real application checks follow coherent implementation. No new environment,
arbitrary memory cap, broad code transplant or routine contributor PR is needed.
Stashing historical source was a custody operation, not the implementation
or scientific-provenance deliverable. That custody is complete. Keep the
original data/history separate; do not pull current main over colliding
untracked source or replace another worker's installed backing paths.
