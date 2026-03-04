# Paper 4 Statement Distribution Ledger

- Seed date: 2026-03-04
- Reviewed pass: intro previews normalized; mixed abstraction-boundary theorem rerouted away from Paper A/B full ownership
- Source: `docs/papers/paper4_decision_quotient/latex_toc/content/*.tex`
- Full ledger: `docs/papers/paper4_decision_quotient/reviews/2026-03-04_paper4_statement_distribution_ledger.tsv`
- Total statement rows: 304

## Current editorial rules

- Paper A and Paper B are treated as fully non-physical by default.
- Intro statements from `latex_toc/content/01_introduction.tex` are treated as previews; downstream papers should use `cite only` or short recap treatment there.
- Physics/engineering/stochastic/sequential/regime/integrity content is routed to Paper C unless manually revised to `TOC-only`.
- Shared foundations are canonically owned by Paper A in the ledger unless the item is explicitly quotient/Bayes/`srank`-centric for Paper B.
- Mixed statements that contain both non-physical and physical clauses should not remain full statements in Paper A or Paper B.

## Counts by downstream owner

- A: 45
- B: 13
- C: 246
- TOC-only: 0

## Counts by dependency class

- shared-foundation: 19
- A-only: 26
- B-only: 13
- physical: 246

## Counts by treatment

- full statement: 260
- shortened recap: 21
- cite only: 23
- retire from downstream papers: 0

## Counts by TOC file

- `01_introduction.tex`: 20
- `02_formal_foundations.tex`: 122
- `02a_physical_grounding.tex`: 15
- `02b_stochastic.tex`: 5
- `02c_sequential.tex`: 3
- `03_complexity_dichotomy.tex`: 87
- `03b_substrate_cost.tex`: 1
- `03d_temporal_integrity.tex`: 1
- `04_tractable_special_cases.tex`: 3
- `05_mathematical_justification_of_engineering_practice.tex`: 8
- `06_implications_for_software_architecture.tex`: 30
- `07_simplicity_tax.tex`: 8
- `10_lean_4_proof_listings.tex`: 1

## High-priority next audit

- Manually review the shared-foundation rows in `latex_toc/content/02_formal_foundations.tex` that Paper B must restate independently.
- Decide whether any Paper C-owned engineering corollaries should instead be marked `TOC-only` to keep Paper C tighter.
- Add actual target citation locations once `paper4`, `paper4b`, and `paper4c` section files stabilize.
