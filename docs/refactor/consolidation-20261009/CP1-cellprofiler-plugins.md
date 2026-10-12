# CP1: CellProfiler plugin modules

Branch `feature/CP1-cellprofiler-plugins`. Measured 2026-10-12 at `5235c1a95`.

Two goals from the owner: converting a `.cppipe` that uses plugin modules works; plugin
usage is the demand list for what OpenHCS supports natively.

## What is wrong

- **One unknown module discards the pipeline.** `import_cellprofiler_pipeline` calls
  `CellProfilerModule.require_module(name)` for every block. For a name with no
  declaration it raises `KeyError("No CellProfiler module declaration is registered for
  'X'.")` from `source_bindings_for_modules` (`module_declarations.py:440`), before any
  step exists. Observed with `GaussianFilter, SomeLabsPlugin, GaussianFilter`: no steps
  returned. The GUI shows the message in a critical box; MCP returns
  `load_pipeline_file_failed`. Recorded by
  `tests/unit/test_cppipe_corpus.py::test_cppipe_import_rejects_unknown_module_at_nominal_boundary`.
- **No plugin module is declared.** 55 module names exist in
  CellProfiler/CellProfiler-plugins; none has a `CellProfilerModule`.
- **A declared module with an absent optional dependency has no owner.** The function
  catalogue leaves out a file whose `REQUIRED_DISTRIBUTIONS` is absent
  (`_module_in_this_catalog`), but module classes register through package discovery,
  which swallows `ImportError` (the class silently vanishes and the module looks unknown)
  or raises `ModuleNotFoundError` depending on which discovery ran first.
  `openhcs_registry_functions()` hands the catalogue every registered class's callable
  regardless of `REQUIRED_DISTRIBUTIONS`.
- **Built-in gaps.** CellProfiler 4.2.8.1 (the pinned native environment
  `.venv-cellprofiler39`) has 98 module files, 94 user-facing (4 are test fixtures:
  `injectimage`, `inject_objects`, `measurementfixture`, `setting_validation`). 90 of 94
  have a declaration. Missing: `LoadData`, `LabelImages`, `SaveCroppedObjects`,
  `CreateBatchFiles`. `LoadData` is why the in-tree `ExampleFly.cppipe` is listed
  `KNOWN_INVALID`.
- **Restated per-module facts.** Adding a module is already one file (class plus
  function) but two rosters restate the family:
  `openhcs/processing/backends/cellprofiler/contracts.json` (89 hand-kept entries, no
  reader) and `tests/unit/test_cellprofiler_compatibility_matrix.py:24`
  (`len(report.modules) == 91`).

## Evidence: what people use

Sources, each with what it counts.

1. **GitHub code search**, REST `search/code`, query
   `"<Module>:[module_num" extension:cppipe`, run 2026-10-12 for all 55 plugin names.
   Count is indexed files; "repos" is distinct repositories among the first 100 hits.
   Every hit was fetched and checked for the real header line. Total indexed `.cppipe`:
   1708 (`CellProfiler Pipeline extension:cppipe`). Undercounts: default branches only,
   files under 384 kB, forks excluded, private repositories invisible. Overcounts: copies
   of one pipeline across repositories (61 RunCellpose files are 51 distinct blobs).
   `.cpproj` queries returned 0 for every module (5 `.cpproj` indexed at all).
   Baselines: IdentifyPrimaryObjects 1120, MeasureObjectIntensity 1100, GaussianFilter 75,
   Watershed 66, RunImageJMacro 5.
2. **Local caches** (`~/.cache/openhcs/cellprofiler_examples`,
   `~/.cache/openhcs/benchmark_datasets`, `benchmark/`, `tests/`): 101 unique `.cppipe`
   by SHA-256. Modules without a declaration: RunCellpose 1, Runilastik 1 (both tutorial
   bonus pipelines), LoadData 1. The 22-source community corpus described in
   `docs/plans/cellprofiler_community_cppipe_corpus_acquisition_20260719.md` is not on
   this machine (`community_sources/` is absent), so its 275 unique files are not counted.
3. **CellProfiler's own pipelines** (code search restricted by repo/org): CellProfiler/examples
   43 files, no plugin; CellProfiler/tutorials 40 files: RunCellpose 6, RunStarDist 2,
   Runilastik 1. `org:broadinstitute`: CallBarcodes 36, CompensateColors 22, RunCellpose 18.
4. **image.sc forum: counts are missing, not zero.** `forum.image.sc/search.json`
   answered HTTP 403 "Crawler is not allowed!" to every request. To run by hand, per
   module: `https://forum.image.sc/search?q=<ModuleName>%20after%3A2024-10-12` (topics in
   the last two years) and without the `after:` term; for generic names add
   `%23cellprofiler`.
5. **Published statements** (no per-module tally was found). Weisbart et al.,
   arXiv:2306.01915v1: "As seen in Figure 2, Cellpose is a highly-requested plugin for
   CellProfiler, due to its easy-to-tune segmentation networks."; "modules such as
   CallBarcodes … are typically designated as plugins because, in our experience, only a
   small fraction of CellProfiler users are performing this type of experiment."

### Ranked demand list

Classification is the plugin repository's own (active = `active_plugins/`, "supported";
unmaintained = `unmaintained_plugins/`). The repository has no LICENSE file (GitHub
reports `license: null`); individual files carry BSD-3, MIT-style or GPL headers.
OpenHCS implementations here are written against the algorithm and the library calls,
not copied.

| # | Module | GitHub files (repos) | Other counts | Algorithm | Dependencies | Plugin tier | Licence notes | Native OpenHCS support |
|---|---|---|---|---|---|---|---|---|
| 1 | RunCellpose | 61 (19) | tutorials 6, broadinstitute 18, local 1; revisions seen r3 45, r4 24, r5 9, r6 13 | Cellpose segmentation | cellpose, torch; plugin defaults to Docker | active | Cellpose code BSD-3; weights: Cellpose-SAM tagged BSD-3, v1 to v3 not established; README says training data is CC-BY-NC | declared module wired to the Cellpose function behind an extra |
| 2 | HistogramEqualization | 44 (6) | | global or adaptive (CLAHE) equalization | scikit-image | active | | catalogued function |
| 3 | CallBarcodes | 36 (4) | all in broadinstitute | sequencing-by-synthesis barcode calling against a CSV library | numpy, csv | active | | catalogued function with the CSV as a declared input file |
| 4 | DistanceTransform | 32 (4) | | Euclidean distance transform | scipy | active | | catalogued function |
| 5 | CompensateColors | 23 (5) | broadinstitute 22 | channel bleed-through compensation | numpy, scipy | active | | catalogued function |
| 6 | HistogramMatching | 9 (2) | | match histogram to a reference image or frame | scikit-image | active | | catalogued function |
| 7 | RunStarDist | 9 (4) | tutorials 2 | StarDist star-convex segmentation | stardist, tensorflow, csbdeep | active | code BSD-3; weights not established | declared module behind an extra; needs a model function |
| 8 | DeclumpObjects | 6 (2) | | seeded watershed split of objects | scikit-image | active | | catalogued function |
| 9 | MeasureRadialEntropy | 6 (1) | carpenter-singh-lab 6 | entropy of intensity across radial wedges | numpy | unmaintained | | catalogued function |
| 10 | EnforceObjectsOneToOne | 4 (3) | | one-to-one primary/secondary relabelling | numpy | active | | catalogued function |
| 11 | RunImageJScript | 4 (2) | | run an ImageJ script through PyImageJ | pyimagej, JVM | active | PyImageJ Apache-2.0 | declared module behind the `fiji` extra |
| 12 | LaplacianOfGaussian | 3 (1) | | LoG filter | scipy | unmaintained | | catalogued function |
| 13 | TopHatTransform | 3 (1) | | top-hat | scikit-image | unmaintained | | catalogued function |
| 14 | FilterObjects_StringMatch | 2 (1) | | filter objects by a string measurement | numpy | active | | catalogued function |
| 15 | EdgeDetection | 2 (2) | | Sobel | scikit-image | unmaintained | | catalogued function |
| 16 | CalculateMoments, ConvertOutlinesToObjects, EnhancedMeasureTexture, PixelShuffle, Runilastik, BlobDetection, ClassifyPixels-Unet | 1 each | Runilastik: tutorials 1, local 1 | | Runilastik: ilastik (GPL v2+), Docker or local install; ClassifyPixels-Unet: tensorflow | mixed | | |

Two apparent hits are not plugin use: `MergeObjects` 361 are all the built-in
`SplitOrMergeObjects`; `RunImageJ` 2 are the CellProfiler 2 built-in. The other 31
plugin names returned 0, including RunOmnipose (Omnipose NonCommercial License) and
RunVISTA2D (weights CC-BY-NC-SA-4.0).

Full inventory (55 names: 40 dependency-free, 2 light, 13 heavy; 24 active, 31
unmaintained-only) was produced from a shallow clone by AST parsing, never importing the
plugin code. It is not committed; the per-module settings it extracted are restated only
in each module's declaration.

## Target

- A plugin module is one more `CellProfilerModule`: one file with the class and its
  function. Converter, settings parsing, declared outputs and forms derive from it.
- Optional dependencies are declared once, as the file's `REQUIRED_DISTRIBUTIONS`. The
  catalogue exclusion, the class's registration and the "cannot run: install X" message
  all derive from it. A pipeline naming such a module converts to its real step with its
  settings; compilation of that step fails naming the distribution and the extra.
- A module name with no declaration converts to one step carrying the written name,
  revision and settings, connected in the dataflow (outputs derived from what later
  modules consume), blocking compilation with a message, replaceable by any function.
- No roster of modules outside the family.

## Guards

- `tests/unit/test_cellprofiler_undeclared_and_unavailable_modules.py`
- `tests/unit/test_cellprofiler_plugin_modules.py` (settings from real blocks, execution
  against the real plugin's output, declared outputs)
- official30 parity stays 30/30 (the converter changed).

## Correctness of a plugin conversion

Plugins are outside the official30 native references. The pinned native environment
`.venv-cellprofiler39` (CellProfiler 4.2.8.1) can load dependency-free plugins with
`--plugins-directory`, so each native implementation is compared with the real plugin's
output on a small image; fixtures record the plugin repository commit. Heavy plugins
(Cellpose, StarDist, ilastik) cannot be run there without installing their dependency
into that environment, which was not done; their procedure is the same once a pinned
environment with the dependency exists.

## Status

See "Done" and "Remaining, in order" below; kept current after each commit.

### Done

(nothing yet)

### Remaining, in order

1. Mechanism: undeclared-module step; dependency-absent declared module; delete
   `contracts.json`; derive the `== 91` count.
2. Pure plugins by rank: HistogramEqualization, CallBarcodes (barcode CSV as a declared
   input file), DistanceTransform, CompensateColors, HistogramMatching, DeclumpObjects,
   MeasureRadialEntropy, EnforceObjectsOneToOne, LaplacianOfGaussian, TopHatTransform,
   FilterObjects_StringMatch, EdgeDetection, CalculateMoments, ConvertOutlinesToObjects,
   EnhancedMeasureTexture, PixelShuffle, BlobDetection, then the zero-count ones: AddNoise,
   BoxObjects, Gaussian_BySlice, MaskTopAndBottomZ, RescaleIntensitySlicewise,
   VarianceTransform, and the unmaintained dependency-free ones (Active contour model,
   CalculateHistogram, ConstrainObjects, GammaCorrection, IdentifyLinearObjects,
   ImageGradient, MeasurePopulationContext, MeasureTrackQuality, MergeObjects, Random
   walker algorithm, RescaleMeanSD, RescaleModePercentile, SeedObjects, ShollAnalysis,
   SpectralAnalysis, TestAllThresholds, Transforms). Each: settings from a real `.cppipe`
   block with its source repository and commit recorded, and a check against the plugin's
   own code.
3. Built-ins to 94 of 94: LoadData (work out its meaning for source bindings), LabelImages,
   SaveCroppedObjects, CreateBatchFiles (a declared no-op that says why).
4. Heavy: RunCellpose (declaration and full settings mapping onto the Cellpose surface of
   branch `feature/cellpose-full-surface`; no second wrapper), RunStarDist, Runilastik.
