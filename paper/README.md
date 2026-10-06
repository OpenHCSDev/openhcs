# OpenHCS manuscript

Working author-review draft for **SLAS Technology**:
*OpenHCS: shared microscopy workflows for scientists and AI agents*.

## Versioned sources

- [Manuscript source](manuscript.md): the sole complete working text.
- [Supplementary material](supplementary/README.md): explanatory figures,
  historical timing and prospective validation plots, source tables and
  evaluation records.
- [Additional CellProfiler workflows](supplementary/complex_cellprofiler_workflows.md):
  generated step sequences for public advanced-segmentation and 3D examples.
- [OpenHCS 0.8.5 CI evidence](supplementary/ci_official30_085/README.md):
  preserved hosted execution and selected-value comparison records, source
  revision, reference inventory and checksums.
- [Bibliographic metadata](openhcs_references.json) and [citation style](styles/README.md).

## Editorial guidance

Use the canonical paper-writing style guide in the sibling `papers` repository:
`docs/papers/writing_style_guide.md`. Keep that guide as the substantive source
rather than copying it here. For this experimental software paper, apply its
plain-language, evidence-order, stable-vocabulary and claim-scope rules to the
text, tables and captions. Theory-specific theorem and proof organisation does
not determine the SLAS manuscript structure. Keep run history and detailed
verification records in the supplementary evidence, with the results needed
to understand the scientific findings in the main text.

## Figures and validation

The seven main figures show the shared workflow, matching UI/code/MCP authoring,
the recorded agent analysis and benchmark results, followed by task-only
first/final analysis, full-corpus coverage and native views of autonomous local
repair and fresh retinal detection. Seventeen supplementary figures explain runtime composition,
process boundaries, compiler preparation, connected outputs and custom functions.
They also report historical timing observations and three prospective
agent-authored assays on held-out public data. The two newer native-view figures
show a task-only local repair with regression and scope controls, and a separate
same-context volumetric development example; neither substitutes for reference
evaluation. Two further native-view figures retain retinal soma development
and a local BBBC013 nuclear repair with unresolved compartment ownership;
these same-author development examples are separate from autonomous scores.
Figures 13–14 show a fresh nuclear core/boundary repair and residual
crowded-region uncertainty in the independent retinal result shown in main
Figure 7. Figures 15–16 retain the source-derived CellProfiler import example
and native Fiji/napari viewer demonstrations. Supplementary Table 1 retains the
reusable-library roles and source links.
Figure 17 adds native XY/XZ/YZ review of an independent volume result, retaining
ordinary-body support and unresolved multi-lobed identity separately.

[Supplementary Data 8](supplementary/task_only_analysis.md) retains the newer
task-only authoring results separately from those prospective held-out assays.
Figure 5 consumes the exact post-freeze evaluation receipts, without rerunning
microscopy analyses or scoring. Regenerate its native repair and three score
panels with `PYTHONPATH=paper/figures python -c 'from build_slas_visual_story import task_only_story; task_only_story()'`
in an existing matplotlib-capable environment. The existing
`build_slas_task_only.py` owns evaluation loading and score plots; the shared
`FigureSheet` owns retained-image placement, crops and source/output hashes.
The earlier score-only rendering and plotted observations remain retained.

Generators, editable artwork, native captures and provenance receipts are in
`figures/`. Scientific examples in this revision use public CellProfiler workflows
and the retained public NeuronCyto II demonstration. Figure receipts distinguish
historical analysis from later authoring and viewer checks.

Earlier split drafts and planning notes remain as working history. Historical
links to `openhcs_nature_methods_draft.md` now reach a pointer to the sole source.
This is an author-review draft, not a submitted manuscript. Software releases
are tracked separately.

## Build a reading copy

Read [current manuscript PDF](current/openhcs_manuscript.pdf) and
[current supplement PDF](current/openhcs_supplement.pdf). Editable DOCX files, input/tool
provenance (`build.json`) and complete command output (`build.log`) are beside them.
`current` switches only when both documents build and validate successfully.
PDF and DOCX filenames use the paper's declared `openhcs` prefix so they can be
uploaded alongside other papers without renaming. Source filenames are unchanged.

Create a build-only environment (not the OpenHCS runtime environment). Install
Pandoc, LibreOffice and Poppler on Linux, then install the pinned shared package:

```sh
python -m venv /path/to/paper-build-env
/path/to/paper-build-env/bin/python -m pip install -r paper/requirements-build.txt
/path/to/paper-build-env/bin/python paper/build_paper.py build
/path/to/paper-build-env/bin/python paper/build_paper.py status
/path/to/paper-build-env/bin/python paper/build_paper.py snapshot --label pi-review
```

These commands work from any directory when given the script's absolute path.
`status` rederives the current source/preparation dependency set and checks input
and output hashes, active executable identities/versions and the installed
runtime dependency closure. It exits nonzero for stale/missing builds; an older
provenance schema requires rebuilding, without removing its reading copies.
`build --candidate` validates without switching `current`. A failure keeps the
previous paired package available, with diagnostics under `build/run-*`.
Snapshots copy one resolved successful package and its linked local support.
They are frozen reading copies, not another manuscript source.

The build-only requirement pins the reviewed papers Git commit. Installation
imports that package; no sibling checkout, vendored copy or manual code syncing
is required. Shared-code development may use an editable papers installation in
this build-only environment; build records retain actual source hashes.

Figure generation also requires the linked source assets and archived benchmark
inputs. Receipts record their identities; source files are not fabricated when
an external input is unavailable. The checked-in figure outputs support building
reading copies without rerunning scientific analyses. Automatic
`--refresh-figures` deliberately fails: no safe historical-input/live-UI refresh
is declared. Figure generation remains a separate explicit workflow.

The overview and archived May benchmark figures can be regenerated independently
from their declared source assets and CSV tables:

```sh
PYTHONPATH=paper/figures python -c \
  'from build_slas_visual_story import architecture; architecture()'
python paper/figures/build_slas_benchmark.py \
  --data-dir benchmark/results/labmeeting_20260513/official30_well_throughput/data \
  --output-dir paper/figures/slas
```

The archived benchmark mode reproduces the May distribution figure, supplementary
workflow heatmap and plotted-row CSVs. It retains the original one-observation
tables, historical timing scopes and unresolved wound-healing exclusion.

For fresh measurements, first qualify the complete matched reports and convert
them to execution or total summaries with their original `summary_custody.json`.
Then use the same paper builder's explicit measured input mode:

```sh
PYTHONPATH=. python paper/figures/build_slas_benchmark.py \
  --summary-source '1 well / 1 worker=QUALIFIED/execution_summary.csv' \
  --scope execution --output-dir paper/figures/slas/measured/execution
PYTHONPATH=. python paper/figures/build_slas_benchmark.py \
  --summary-source '1 well / 1 worker=QUALIFIED/total_summary.csv' \
  --summary-source '8 assignments / 2 workers=QUALIFIED/8a2w/total_summary.csv' \
  --summary-source '16 assignments / 4 workers=QUALIFIED/16a4w/total_summary.csv' \
  --cohort-manifest SELECTED_THREE_CASE_MANIFEST.json \
  --scope total --output-dir paper/figures/slas/measured/scaling-total
```

This delegates to the existing measured benchmark figure owner, preserving each
mode's actual native baseline, per-pipeline ratios of engine medians, original
clock boundaries and repetition counts. Supplied modes must cover the same
pipeline cohort and source revision. Repeated assignments are independent copies
of one selected source sample, not additional acquired biological wells. No
projected native throughput or unmeasured RAM panel is generated. The execution
scope also renders the accepted scientific-comparison fraction. See
[the measured report contract](../benchmark/reports/README.md) for timing scopes
and output panels.

An explicit `--cohort-manifest` selects its ordered cases from every supplied
mode without editing the qualified summaries. Each selected case must match the
original qualified manifest through the existing benchmark case owner, including
resolved inputs, pipeline parameters and well selection. Every mode must contain
every selected case. The figure provenance retains the selection manifest and
original manifest digests; the default still requires identical complete cohorts.

Both input modes emit the existing `figure2_provenance.json` checksum contract.
Measured outputs retain the exact summary and custody inputs plus the delegated
plotting implementation's digest. Use a distinct measured output directory so
archived figure assets and their provenance remain identified as historical.
The plotting entry consumes qualification established by the matched-report
producer; it does not independently rerun or qualify the scientific comparison.

Each local document figure must have exactly one receipt output declaration;
missing, empty, malformed or ambiguous coverage fails closed. All outputs owned
by each selected receipt are checked, not only its embedded PNG. Historical
source-receipt differences are explicitly reported as reused evidence, not fresh
reproduction. Sources and conversion resources are captured as observed bytes;
dependency sets and tools are checked again after conversion. This is not a
whole-filesystem lock or a guarantee of detecting changes reverted between checks.
Run a fresh CLI process after editing implementation code. Custom builder,
preparation and layout owners need readable Python source origins; their MRO
defining files are tracked, not arbitrary imported helper closures. Other local
helper/configuration inputs must be observed by preparation. Dependency-version
checks do not detect in-place patches retaining the same installed version.

The old `build_docx_from_markdown.py SOURCE OUTPUT.docx` command is a thin shared
delegate for isolated DOCX copies. It also resolves the old main-source filename;
it never changes the managed paired `current` package.

Dated PDF/DOCX reading copies, reviewer reports, UI debugging captures and
withdrawn-case history remain local under `review/`. They are not part of the
versioned draft package.

## Tracking and retention

Track author sources, figure generators, directly related tests, small required
provenance/results receipts and intentionally selected main artifacts. Generated
`current`, `build` runs, profiles and reviewer snapshots remain ignored. Do not
newly track raw microscopy images, bulk data, archives, intermediate renders or
old output variants. Existing tracked historical assets are unchanged.

The generated [history index](review/INDEX.md) exposes successful runs, frozen
snapshots and labelled legacy folders. `history` refreshes it without rebuilding.
`cleanup` reports exact older owned candidates and byte footprint without changes;
current, previous successful, newer candidates, frozen snapshots and unmanaged
folders are protected. Optional `cleanup --archive` journals and recoverably
moves old owned runs, keeping their original URLs via relative symlinks. This
organises live runs, not disk reclamation; a multi-run interruption can leave a
partial recoverable archive. Migration does not execute it automatically or
delete historical reports. `review/latest` is a compatibility
link to `current`, with its former manually copied pair preserved in a frozen
directory. For a consistent multi-file read, resolve `current` once or use a
snapshot. Native Windows publication is not implemented or claimed as tested.


Single-core measured amortization uses the same qualified figure owner, separately
from multiworker scaling. Supply the execution summaries for actual1/8/16
assignments on one CPU/worker per engine, all from one qualified source head:

```bash
python paper/figures/build_slas_benchmark.py \
  --summary-source "1 assignment / 1 worker=/qualified/one/execution_summary.csv" \
  --summary-source "8 assignments / 1 worker=/qualified/eight/execution_summary.csv" \
  --summary-source "16 assignments / 1 worker=/qualified/sixteen/execution_summary.csv" \
  --scope amortization --cohort-manifest /qualified/selected-three-case-manifest.json \
  --output-dir /qualified/figures/single-core-amortization
```

Counts and paired non-execution overhead come from the existing summary custody,
not labels. Curves show measured seconds per assignment; lines do not project
unmeasured counts. Compile-plus-run totals include OpenHCS per-job compilation;
CellProfiler totals exclude one-time pipeline loading. Both exclude service/library
readiness. Single-sample total targets native parity; the execution headline
excludes compilation. Multiworker efficiency requires the same assignment count
on one and several workers, rather than treating amortization as parallel speedup.
