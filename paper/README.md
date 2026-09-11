# OpenHCS manuscript

Working author-review draft for **SLAS Technology**:
*OpenHCS: interoperable, agent-guided microscopy analysis*.

## Versioned sources

- [Manuscript source](openhcs_nature_methods_draft.md): the complete working text.
  The filename retains the earlier journal target.
- [Supplementary material](supplementary/README.md): five explanatory figures,
  historical timing plots, source tables and evaluation records.
- [Additional CellProfiler workflows](supplementary/complex_cellprofiler_workflows.md):
  generated step sequences for public advanced-segmentation and 3D examples.
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

Earlier split drafts and planning notes remain as working history. The linked
complete manuscript identifies the current version. This is an author-review
draft, not a submitted manuscript. Software releases are tracked separately.

## Build a reading copy

From the repository root, with Pandoc and Python available:

```sh
python paper/build_docx_from_markdown.py paper/openhcs_nature_methods_draft.md paper/review/openhcs_current.docx
python paper/build_docx_from_markdown.py paper/supplementary/README.md paper/review/openhcs_supplement_current.docx
```

Figure generation also requires the linked source assets and archived benchmark
inputs. Receipts record their identities; source files are not fabricated when
an external input is unavailable. The checked-in figure outputs support building
reading copies without rerunning scientific analyses.

Dated PDF/DOCX reading copies, reviewer reports, UI debugging captures and
withdrawn-case history remain local under `review/`. They are not part of the
versioned draft package.
