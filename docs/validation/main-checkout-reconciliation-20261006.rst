Dirty main checkout reconciliation
==================================

Integration owner: this coordinator. Viewer audit: Singer. Benchmark and
scientific-source audit: Hypatia. Source preservation is complete; selective
integration, issue acceptance and checkout cleanup remain in progress.

The live checkout at /home/ts/code/projects/openhcs remains based on
2bc579ca9e5d3d70a130bec96ee6f001f3dd5c74 (24 September). Direct tool-call history
from this conversation establishes edits there on 26--28 September. This is
historical work, not evidence that the latest manuscript changes bypassed /wt.
Its files and index have not been reset, cleaned, restored or stashed.

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

Determining dispositions
-------------------------

* Exact reverse-patch checks at main79c09a62c proved all local changes in seven
  files already integrated: function_contract_metadata, function_reference,
  lib_registry/registry_service and four website gallery assets/records.
  Refresh this result against the current head before cleanup.
* CustomFunctionSourceNamespace and source-lifetime validation are integrated;
  later canonical changes mean whole-file equality is not the correct test.
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
* Historical singleton checkpoint replay, sparse route-local index translation
  and settlement-cycle error isolation remain candidate regressions. Preserve
  their exact tests; determine whether current producers/owners still expose
  the reported behavior before adapting old code.
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

Next delivery
-------------

Adapt useful unpublished families through existing owners in released /wt
checkouts, preserving this recovery branch independently. Tests and affected
real application checks follow coherent implementation. No new environment,
arbitrary memory cap, broad code transplant or routine contributor PR is needed.
Stashing historical source is a final custody operation, not the implementation
or scientific-provenance deliverable. Keep data/history separate and preserve
dependency edits independently before changing the live checkout.
