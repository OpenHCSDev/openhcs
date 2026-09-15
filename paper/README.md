# OpenHCS manuscript

Working author-review draft for **SLAS Technology**:
*OpenHCS: shared microscopy workflows for scientists and AI agents*.

## Versioned sources

- [Manuscript source](manuscript.md): the sole complete working text.
- [Supplementary material](supplementary/README.md): five explanatory figures,
  historical timing plots, source tables and evaluation records.
- [Additional CellProfiler workflows](supplementary/complex_cellprofiler_workflows.md):
  generated step sequences for public advanced-segmentation and 3D examples.
- [OpenHCS 0.8.5 CI evidence](supplementary/ci_official30_085/README.md):
  preserved hosted execution and selected-value comparison records, source
  revision, reference inventory and checksums.
- [Bibliographic metadata](openhcs_references.json) and [citation style](styles/README.md).

## Figures and validation

The six main figures show the shared workflow, matching UI/code/MCP authoring,
the recorded agent analysis, CellProfiler translation, benchmark results and
viewer inspection. Supplementary figures explain runtime composition, process
boundaries, compiler preparation, connected outputs and custom functions.

Generators, editable artwork, native captures and provenance receipts are in
`figures/`. Scientific examples in this revision use public CellProfiler workflows
and the retained public NeuronCyto II demonstration. Figure receipts distinguish
historical analysis from later authoring and viewer checks.

Earlier split drafts and planning notes remain as working history. Historical
links to `openhcs_nature_methods_draft.md` now reach a pointer to the sole source.
This is an author-review draft, not a submitted manuscript. Software releases
are tracked separately.

## Build a reading copy

Read [current manuscript PDF](current/manuscript.pdf) and
[current supplement PDF](current/supplement.pdf). Editable DOCX files, input/tool
provenance (`build.json`) and complete command output (`build.log`) are beside them.
`current` switches only when both documents build and validate successfully.

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
