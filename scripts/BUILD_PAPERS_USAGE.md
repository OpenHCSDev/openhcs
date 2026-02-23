# Unified Paper Build System

## Overview

Replaced fragmented shell scripts with a single orthogonal Python builder.

**Files:**
- `scripts/build_papers.py` - Main builder
- `scripts/papers.yaml` - Metadata (single source of truth)

## Usage

```bash
# Build all papers (all formats)
python3 scripts/build_papers.py all

# Build specific format
python3 scripts/build_papers.py markdown all    # All markdown
python3 scripts/build_papers.py latex all       # All LaTeX PDFs
python3 scripts/build_papers.py lean all        # All Lean proofs
python3 scripts/build_papers.py arxiv all       # All arXiv packages
python3 scripts/build_papers.py metadata all    # Zenodo/arXiv copy-paste metadata
python3 scripts/build_papers.py claim-check all # Claim-to-Lean mapping coverage
python3 scripts/build_papers.py scaffold all    # Scaffold missing boilerplate for all paper entries

# Build specific paper
python3 scripts/build_papers.py markdown paper1
python3 scripts/build_papers.py latex paper3
python3 scripts/build_papers.py lean paper2
python3 scripts/build_papers.py arxiv paper1    # Package paper1 for arXiv
python3 scripts/build_papers.py metadata paper4_toc  # Generate copy-paste metadata only
python3 scripts/build_papers.py release paper2_it --claim-check  # Enforce mapping coverage in release
python3 scripts/build_papers.py scaffold paper6 # Create folder/file boilerplate from papers.yaml
python3 scripts/build_papers.py scaffold paper6 --overwrite # Rewrite scaffold files if needed
```

## arXiv Packaging

The `arxiv` build type creates complete submission packages:

```bash
python3 scripts/build_papers.py arxiv all
```

Each package contains:
- **PDF**: The compiled paper
- **Markdown**: Full text for LLM consumption
- **Lean proofs**: All source files (build artifacts excluded)

Output: `docs/papers/paper{N}_{name}/paper{N}_{name}_arxiv.tar.gz`

Example contents:
```
paper1_typing_discipline/
  main.pdf                          # Compiled PDF
  paper1_typing_discipline.md        # Full markdown
  proofs/
    PrintAxioms.lean
    abstract_class_system.lean
    axis_framework.lean
    ... (11 Lean files total)
```

## Architecture

### Single Source of Truth: `papers.yaml`

```yaml
papers:
  paper1:
    name: "Typing Discipline"
    dir: "paper1_typing_discipline"
    latex_dir: "toplas"
    latex_file: "main.tex"
    # Optional:
    # proofs_dir: "proofs"
    # archive_prefix: "paper1"
    # assumption_ledger_sources:
    #   - "DecisionQuotient/ClaimClosure.lean"
    # claim_mapping_file: "content/11_lean_proofs.tex"
    # arxiv_comments: "Submitted to ... (N pages)."
```

Paper structure metadata is centralized in one place. Lean line/theorem/sorry
counts and LaTeX content ordering are auto-discovered at build time.

### Generic Builders

```python
def build_lean(paper_id):      # One function, all papers
def build_latex(paper_id):     # One function, all papers
def build_markdown(paper_id):  # One function, all papers
def scaffold_paper(paper_id):  # Create required boilerplate from metadata
```

No special cases. All papers treated identically.

### Copy/Paste Metadata

`build_papers.py` now auto-generates release metadata for direct upload forms.

- Generated file: `releases/<paper_id>_copy_paste.txt`
- Sections included:
  - one shared title
  - one `Unicode` abstract (Zenodo copy/paste)
  - one `MathJax` abstract (arXiv copy/paste)
  - arXiv comments
  - machine-readable YAML block
- Regenerated automatically during:
  - `build-markdown`
  - `arxiv`
  - `release`
- You can also run it directly:
  - `python3 scripts/build_papers.py metadata <paper_id>`

### Fail Loudly

- Validates prerequisites (pdflatex, pandoc, lake)
- Checks file existence before reading
- Propagates errors clearly
- No silent failures or fallbacks

## Principles

✓ **Orthogonal**: One function per build type
✓ **Declarative**: YAML metadata replaces imperative code
✓ **Generic**: Eliminates 8 nearly-identical functions
✓ **Fail Loud**: No `|| true`, errors propagate
✓ **Uniform**: All papers have identical structure
✓ **Config-driven deployment**: archive/package naming can be configured per paper
✓ **Coverage gate**: theorem-label to Lean mapping can be enforced in release builds
✓ **Bootstrapped onboarding**: new YAML entries can be scaffolded into valid folder structure

## Claim Mapping Autofill

Claim mapping tables can now be auto-generated.

- Generated file: `content/claim_mapping_auto.tex`
- Source extraction:
  - claim labels from `\label{thm:...|prop:...|cor:...|lem:...}`
  - Lean handles from inline `\nolinkurl{...}` anchors inside the same theorem/proposition/corollary/lemma block
- Configure a paper to use autofill by setting:
  - `claim_mapping_file: "content/claim_mapping_auto.tex"` in `scripts/papers.yaml`
- The autofill file is regenerated automatically during:
  - `build-latex`
  - `build-markdown`
  - `build-submission`
  - `claim-check`

## Restructuring

Papers 3-5 were restructured to match papers 1-2:

```
paper3_leverage/
  shared/
    content/
      01_introduction.tex
      02_foundations.tex
      ...
      abstract.tex
```

This was done automatically by `scripts/restructure_papers.py`.

## Results

✓ All markdown builds pass (5/5)
✓ All LaTeX builds pass (5/5)
✓ Lean builds work (separate configuration)
✓ Reduced complexity: 642 lines → 250 lines + 100 lines YAML
✓ No edge cases, no special handling
