# Haase notebook → OpenHCS translation candidates

Date: 2026-09-15. Scope: primary-source inventory and proposed evidence protocol, not completed analysis. No notebook was executed, no dependency installed, no function registered, and no GUI state or dataset manifest changed during this inventory. Small source/fixture files were inspected in memory, including TIFF geometry; no large archive was downloaded.

## Recommendation

Use the deterministic contact-graph example first, followed by APOC object-class inference. They test quantitative graph semantics and learned morphology classes rather than another nuclei-segmentation demonstration. Both expose genuine gaps between a notebook and the current declared function catalog. Keep btrack as the higher-effort temporal candidate: the inputs are modest, but reference-track export and faithful backend integration are prerequisite work.

| Candidate | Modest input | Endpoint | Evidence status |
| --- | --- | --- | --- |
| Directed contact portions/asymmetry | Authored 8 × 8 label array; notebook scales it to 80 × 80 | Pairwise contact counts, directed portions, asymmetry | Explicit synthetic numerical oracle; not biological accuracy |
| APOC object classes | 286,676 bytes for image, sparse annotations, and published model | Three morphology classes per segmented object | Supplied learned-model computation and training strokes; no independent biological test set |
| btrack cell migration | 4,883,316 bytes for image and labels, plus 1,771-byte configuration | Temporal links and trajectories over 48 frames | Algorithm-generated labels; notebook log/visualization, not annotated lineage truth |

The demonstration should say **fresh-agent notebook translation with independently checked saved outputs**, not “blind discovery from raw images.” Notebook code, feature definitions, supplied annotations, and published model files are authorized inputs for this distinct task. Do not conflate it with the separate raw-input annotated-dataset pilots.

## Pinned sources and licensing

The inspected BioImageAnalysisNotebooks repository revision is `68845a1afaf53bf601958a3fa7d86f3cf8a43219`. Its [readme](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/readme.md) and [book introduction](https://haesleinhuepf.github.io/BioImageAnalysisNotebooks/intro.html) identify Robert Haase and contributors. The repository states CC BY 4.0 and BSD 3-Clause unless otherwise noted; retain both [content](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/LICENSE-CC-BY) and [code](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/LICENSE-BSD3) license notices and attribution. No per-file override was found for the blobs fixtures. That is a repository-level license assessment, not proof of otherwise undocumented upstream provenance.

Dependency sources inspected, distinct from historical notebook environments:

- [pyclesperanto_prototype](https://github.com/clEsperanto/pyclesperanto_prototype/tree/7c62c1c5a78f5e228d50d3679a4c0f2dea10b201): revision `7c62c1c5a78f5e228d50d3679a4c0f2dea10b201`, BSD 3-Clause.
- [APOC](https://github.com/haesleinhuepf/apoc/tree/cb7667987dc4da966dc6efd3e4d7adedcc22e5c3): revision `cb7667987dc4da966dc6efd3e4d7adedcc22e5c3`, BSD 3-Clause; current inspected source reports 0.14.0. The supplied model instead records APOC 0.6.2. No latest GitHub release was returned by its release endpoint; that does not establish absence of package releases.
- [btrack](https://github.com/quantumjot/btrack/tree/2de42c911253e021b3814191fd1a049a6c0e2628): revision `2de42c911253e021b3814191fd1a049a6c0e2628`, MIT; latest GitHub release inspected was v0.7.0. A source HEAD pin is not a claim that it equals that release or the historical notebook environment.

### 1. Directed contact portions and asymmetry

Primary notebook: [pinned source](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/docs/25_neighborhood_relationships_between_cells/touch_portion_explained.ipynb), [rendered explanation](https://haesleinhuepf.github.io/BioImageAnalysisNotebooks/25_neighborhood_relationships_between_cells/touch_portion_explained.html).

The quantitative worked example explicitly constructs five integer labels in an 8 × 8 array and scales X/Y by 10 with `auto_size=True`. Its saved contact-count matrix includes background row/column zero and five object rows. For labels 4/5, the directed percentages are approximately 16.6667% and 25%, hence asymmetry 1.5. The full 6 × 6 integer count matrix is embedded in the notebook output. The prototype [count implementation](https://github.com/clEsperanto/pyclesperanto_prototype/blob/7c62c1c5a78f5e228d50d3679a4c0f2dea10b201/pyclesperanto_prototype/_tier3/_generate_touch_count_matrix.py) and [portion implementation](https://github.com/clEsperanto/pyclesperanto_prototype/blob/7c62c1c5a78f5e228d50d3679a4c0f2dea10b201/pyclesperanto_prototype/_tier4/_generate_touch_portion_matrix.py) establish that portions normalize the contact-count matrix by column sums. Portions are not necessarily symmetric, image-border contacts are excluded, and the documented operation assumes isotropy.

Pilot boundary: use only that deterministic section. The notebook's separate biological section uses a 100 MB Lund/Tribolium volume from another repository. Attribution is present, but that repository returned no license metadata in this inventory. Neither downloading it nor treating its segmentation as manual truth is needed for this pilot.

Geometry receipt: source scaling defaults to nearest-neighbor interpolation; acquire/freeze the author-generated 80 × 80 label fixture and its exact count matrix before the agent starts. Do not silently substitute a resampler whose centering/output geometry differs. Notebook size: 280,381 bytes; SHA-256 `2ef5ce1a46c8244c8034787892586235dce007b44130723c113ec1786ea9f771`.

Existing OpenHCS mapping, verified from local declarations and read-only live catalog:

- `openhcs:cellprofiler_neighbors_measure_object_neighbors`, declared by `MeasureObjectNeighborsModule`, already measures neighbor counts, aggregate percent touching, and nearest-neighbor distances. Its aggregate percent-touch feature is not the notebook's directed **per-pair** portion matrix.
- `openhcs:cellprofiler_object_filtering_filter_border_objects` exists, but removing objects would change this worked example; do not insert it merely because border handling matters.
- The local modern `pyclesperanto` 0.19.0 module has `generate_touch_matrix`, but not the prototype count/portion/weighted-mesh functions. Native module availability and an MCP-declared function are different claims.

Genuine custom step: one declared pairwise-contact calculation with typed object-pair identities, integer counts, directed portions, and explicit undefined/background handling. Use schema-bearing measurements/relationship contracts; only use a spatial-graph artifact if its declared identities and features actually represent this graph. Derive graphical projections from that same authoritative result, not a second computation or a parallel registry. No learned classifier or new segmentation is necessary.

Proposed independent checks: exact integer matrix equality; directed normalization on nonzero denominators with a predeclared numeric tolerance; the 4/5 asymmetry; symmetry of counts but not portions; saved table object-pair identities. A second author-provided [unit-test fixture](https://github.com/clEsperanto/pyclesperanto_prototype/blob/7c62c1c5a78f5e228d50d3679a4c0f2dea10b201/tests/test_generate_touch_count_matrix.py) is 2 × 2 × 6 and includes background contacts with a fixed 4 × 4 oracle. Declare it as a frozen verification fixture, not unseen biological validation. This candidate supports computational correctness and topology transport, not per-cell biological accuracy.

### 2. APOC three-class object morphology

Primary notebook: [pinned source](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/docs/27_cell_classification/apoc_object_classifier.ipynb).

The notebook applies Otsu thresholding and connected-component labeling to the blobs image, then trains `apoc.ObjectClassifier` using sparse strokes for elongated, roundish, and small objects. Its three features are area, mean/max distance-to-centroid ratio, and intensity standard deviation. It predicts classes, rotates image and labels by 90°, reloads the classifier, and predicts again. The [published model](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/data/blobs_object_classifier.cl) records three classes, three features, depth 2, ten trees, and APOC 0.6.2. Current APOC training defaults instead use 100 trees; copying current defaults is not reproduction of that model.

| Pinned fixture under `data/` | Bytes | TIFF geometry / role | SHA-256 |
| --- | ---: | --- | --- |
| [blobs.tif](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/data/blobs.tif) | 23,089 | 254 × 256, uint8, YX | `71d29715e85659bf43c2c90bab59359fa2797c95a2ebeb997e15c6294e8b2a05` |
| [label_annotation.tif](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/data/label_annotation.tif) | 260,368 | 254 × 256, int32, YX; sparse class strokes, not instance truth | `c71254915517f0b5a91df7c9839a5dc063b06d63e370d66a8ccf8e81dc87e88e` |
| `blobs_object_classifier.cl` | 2,219 | Frozen supplied OpenCL learned model | `c5cf1b52d94aae0e70c1b3758ac1ce6fbb577ec07524e4c581bdc7c412897462` |

Notebook: 81,022 bytes; SHA-256 `f482c825573fb40e637616806be7f7e4fd1d1a25d33fde0d0211e48514a6bcf2`.

OpenHCS mapping: native object size/shape and intensity measurements cover area and intensity statistics, but their existence does not prove equivalence of the mean/max centroid-distance feature. Current MCP classification functions use rules/intensity bins, not this learned random forest. Faithful frozen-model inference therefore needs a typed APOC bridge or a verified exact implementation. Do not substitute a shape threshold and call it notebook parity.

Suggested scope: reproduce inference with the published model first. Training can be a separately version-pinned workflow whose resulting model is a saved, hashed resource. Bind resources explicitly through supported contracts; do not let a compute function discover a model via arbitrary filesystem access. Preserve instance-label identity separately from a class-valued projection: values 1–3 on the class image are not unique object IDs.

Proposed independent checks: freeze reference instance labels, per-object feature values, class assignments, and rotated assignments using a recorded reference environment before agent authorship. Compare saved assignments by object identity, not class-map color or label numbering. Require exact class agreement and declared feature tolerances; compare rotated identities through the known rotation. Sparse-stroke agreement is training consistency only. The rotated training image is a metamorphic check, not held-out generalization. No generalization claim is justified without a new independently annotated image.

### 3. btrack cancer-cell migration

Primary notebook: [pinned source](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/docs/34_timelapse_analysis/tracking.ipynb), [rendered notebook](https://haesleinhuepf.github.io/BioImageAnalysisNotebooks/34_timelapse_analysis/tracking.html).

The notebook loads raw and labeled movies, extracts objects using area and mean intensity, configures `btrack.BayesianTracker` with `btrack.datasets.cell_config()`, appends detections, sets the spatial volume, runs `track_interactive(step_size=100)`, and exports Napari track data/properties/graph. Its embedded log reports 650 objects across 48 frames. The historical API warning already says `track_interactive` is deprecated. No saved machine-readable reference-track export was found among the referenced input fixtures; the screenshot and log do not establish lineage accuracy.

| Pinned book fixture under `data/` | Bytes | Geometry | SHA-256 |
| --- | ---: | --- | --- |
| [cancer_cell_migration_crop.tif](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/data/cancer_cell_migration_crop.tif) | 1,630,458 | 48 × 130 × 130, uint16 | `1b0e0aa3aafa0003467d1bcb6516f2185368175e164005a1b91c921874648610` |
| [cancer_cell_migration_voronoi_otsu_labeling_crop.tif](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/data/cancer_cell_migration_voronoi_otsu_labeling_crop.tif) | 3,252,858 | 48 × 130 × 130, uint32 | `d82f06d3a6ffd8e60ccaa37ab959a3ffd74eff81638813ee9b8b8108300d09f0` |

TIFF axes are QYX, not an explicit time designation. The notebook proves the leading dimension is temporal; ingestion must map it into OpenHCS `TIMEPOINT`, never reinterpret it as Z. Notebook: 284,505 bytes; SHA-256 `14ee77ddaa2c6d3283f1968fa1f97f9e0391379401d5d3f0f9b4bdee3cc4fece`.

The [fixture provenance note](https://github.com/haesleinhuepf/BioImageAnalysisNotebooks/blob/68845a1afaf53bf601958a3fa7d86f3cf8a43219/data/cancer_cell_migration_source.md) credits Tinevez and Jacquemet, describes the X/Y/time crop, and says labels were produced with Voronoi–Otsu in napari (`spot_sigma=5`, `outline_sigma=3`). Original dataset [Zenodo version v1, DOI 10.5281/zenodo.5206107](https://zenodo.org/records/5206107), published 2021-08-16, explicitly licenses the data CC BY 4.0. Its full raw movie (~86 MB) and TrackMate XML (~53 MB) are unnecessary for the crop pilot; TrackMate output is an algorithm comparator, not manual lineage truth. Crop offsets and XML correspondence were not established here.

Freeze the configuration rather than copying the notebook's dynamic fetch. Current [btrack datasets source](https://github.com/quantumjot/btrack/blob/2de42c911253e021b3814191fd1a049a6c0e2628/btrack/datasets.py) uses a remote Pooch registry with a known hash. Inspected [btrack-examples](https://github.com/lowe-lab-ucl/btrack-examples/tree/e3db13fd482ca7749b26706952d0dbf4e2a69432) revision `e3db13fd482ca7749b26706952d0dbf4e2a69432` is MIT; `examples/cell_config.json` is 1,771 bytes, SHA-256 `328693c3b838b7def852681718d66418b2a37dc621bf74c3f0e7084e4a857bac`. Record the actual reference runtime and configuration, not merely the latest source identity.

Existing OpenHCS tracking is real: `openhcs:cellprofiler_tracking_track_objects`, declared by `TrackObjectsModule`, requires variable `TIMEPOINT` and supplies typed measurement rows and directed object-parent relationships. Its implemented methods are OVERLAP and DISTANCE; module validation rejects unsupported LAP/MEASUREMENTS choices. They are not btrack's Bayesian algorithm. Native tracking can be a separately named method comparison; faithful notebook translation needs a typed btrack integration, with declared frame/object identity and configuration resources. Do not infer that a generic spatial graph alone proves temporal track semantics.

Proposed independent checks: obtain and freeze a machine-readable notebook/reference rerun first, including detections, links, track memberships, feature rows, configuration hash, and runtime versions. Compare frame/object membership and link sets modulo track-ID renaming; compare features with declared tolerances. Report reference disagreement separately from biological correctness. Predeclare deterministic/runtime limits if tracking is stochastic. The provided labels support tracking-only parity but not segmentation validation; raw-to-label regeneration is a separate endpoint. No biological identity-switch or division-accuracy score is justified without annotated lineages.

## Common execution gate and remaining gaps

Local source evidence: `openhcs/processing/backends/cellprofiler/{neighbors,tracking}.py`, the library registries, `openhcs/agent/dto/functions.py`, and `openhcs/agent/services/llm_context_service.py`. Read-only MCP search/describe checks were made on 2026-09-15; recheck after the parent's running-server upgrade. Local optional dependencies `apoc`, `btrack`, and `pyclesperanto_prototype` were absent. This inventory does not authorize or establish installation, execution, or compatibility.

Before trials:

1. Freeze licensed inputs, reference outputs, source/model/configuration hashes, and the reference environment. Separate computation-reference evidence from annotations.
2. Give the fresh Sol agent the notebook and input contract, but withhold the frozen scoring outputs. Record notebook exposure, human interventions, and custom-code attempts.
3. Use existing OpenHCS capability-owned registration for genuine missing computation. A custom function is exactly one typed compute callable, with serializable declared parameters and outputs; measurement rows use `ColumnarRows`. It must not copy notebook GUI, downloading, arbitrary filesystem, or training side effects into compute execution. If resource or artifact contracts cannot express the required computation, stop and document that missing capability instead of inventing dictionary/state conventions.
4. Refresh search/describe after persistence, validate and compile through the normal pipeline path, then save outputs and score them independently. Capture fresh/live process boundaries, errors, retries, resource use, and the resulting registered-source hash.
5. Publish only completed endpoints. Contact matrices and frozen-model parity can be strong autonomous computational evidence without claiming manual biological ground truth. Tracking remains conditional until a frozen track reference and compatible typed bridge exist.

Rejected as first choices: another APOC folder-training example reuses BBBC007 and lacks a new independent test endpoint; random artificial-tissue neighbor examples lack an explicit seed; the RedLionfish Richardson–Lucy tutorial contains a GPU dependency error and no saved deconvolved-array oracle. These are not necessarily unusable, but provide weaker immediate evidence than the three scoped candidates above.
