# Paper 4 A/B Foundation Split Checklist

- Source ledger: `docs/papers/paper4_decision_quotient/reviews/2026-03-04_paper4_statement_distribution_ledger.tsv`
- Purpose: give a working checklist for the non-physical split between Paper A and Paper B.
- Scope: only statements currently seeded to `A` or `B`.

## Paper A

- Full-statement rows: 40
- Non-full rows (`cite only` / `shortened recap`): 5

### `02_formal_foundations.tex`

- `def:decision-problem` — definition — Decision Problem
- `prop:zero-epsilon-reduction` — proposition — Zero-$\varepsilon$ Reduction
- `prop:selector-separation` — proposition — Selector-Level Separation Witness
- `def:minimal-sufficient` — definition — Minimal Sufficient Set
- `def:relevant` — definition — Relevant Coordinate
- `prop:minimal-relevant-equiv` — proposition — Minimal-Set/Relevance Equivalence
- `def:exact-identifiability` — definition — Exact Relevance Identifiability
- `def:decision-equiv` — definition — Decision Equivalence
- `def:projection` — definition — Projection
- `prop:sufficiency-char` — proposition — Sufficiency Characterization
- `def:optimizer` — definition — Optimizer Map
- `def:sufficient` — definition — Sufficient Coordinate Set
- `prop:empty-sufficient-constant` — proposition — Empty-Set Sufficiency Equals Constant Decision Boundary
- `prop:insufficiency-counterexample` — proposition — Insufficiency Equals Counterexample Witness
- `def:selector` — definition — Deterministic Selector
- `def:selector-sufficient` — definition — Selector-Level Sufficiency
- `prop:set-to-selector` — proposition — Set-Level Target Dominates Selector Targets
- `def:epsilon-sufficiency` — definition — $\varepsilon$-Optimal Set and $\varepsilon$-Sufficiency
### `03_complexity_dichotomy.tex`

- `prop:query-subproblem-transfer` — proposition — Subproblem-to-Full Transfer Rule
- `prop:query-randomized-robustness` — proposition — Randomized Robustness (Seedwise)
- `prop:query-randomized-weighted` — proposition — Randomized Robustness (Weighted Form)
- `prop:query-state-batch-lb` — proposition — State-Batch Query Lower Bound
- `thm:dichotomy` — theorem — Explicit--Succinct Regime Separation
- `prop:query-finite-state-generalization` — proposition — Finite-State Empty-Subproblem Generalization
- `prop:query-tightness-full-scan` — proposition — Adversary-Family Tightness by Full Scan
- `prop:query-weighted-transfer` — proposition — Weighted Query-Cost Transfer
- `prop:oracle-lattice-transfer` — proposition — Oracle-Lattice Transfer: Batch $\Rightarrow$ Entry
- `prop:oracle-lattice-strict` — proposition — Oracle-Lattice Strictness: Opt vs Value Entries
- `UNLABELED:03_complexity_dichotomy:36` — corollary — Regime Separation (by Encoding)
- `prop:query-regime-obstruction` — proposition — Finite-State Query Lower-Bound Core via Empty-Set Subproblem
- `prop:checking-witnessing-duality` — proposition — Checking--Witnessing Duality on the Empty-Set Core
- `cor:information-barrier-query` — corollary — Information Barrier in Query Regimes
- `def:complexity-classes` — definition — Complexity Classes
- `thm:six-subcases` — theorem — Six Tractable Subcases Are Complexity Classes
- `thm:topology-motion` — theorem — Topology and Motion
- `thm:complexity-dichotomy` — theorem — Complexity Dichotomy
- `cor:query-obstruction-bool` — corollary — Boolean-Coordinate Instantiation
- `prop:query-value-entry-lb` — proposition — Value-Entry Query Lower Bound
### `04_tractable_special_cases.tex`

- `thm:tractable` — theorem — Tractable Subcases
- `prop:heuristic-reusability` — proposition — Heuristic Reusability

### Intro / recap-only rows

- `thm:checking-duality` — cite only — Checking-Witnessing Duality (`01_introduction.tex`)
- `rem:question-vs-problem` — shortened recap — Decision Questions vs Decision Problems (`02_formal_foundations.tex`)
- `UNLABELED:03_complexity_dichotomy:167` — shortened recap — Instantiation of Definitions~\ref{def:structural-complexity} and~\ref{def:representational-hardness} (`03_complexity_dichotomy.tex`)
- `UNLABELED:04_tractable_special_cases:101` — shortened recap — Heuristics and Integrity (`04_tractable_special_cases.tex`)
- `UNLABELED:10_lean_4_proof_listings:54` — cite only — TAUTOLOGY Reduction Correctness, Lean (`10_lean_4_proof_listings.tex`)

## Paper B

- Full-statement rows: 4
- Non-full rows (`cite only` / `shortened recap`): 9

### `02_formal_foundations.tex`

- `prop:srank-support` — proposition — Structural Rank as Relevant-Support Size
- `def:decision-quotient` — definition — Decision-Quotient Score
- `prop:optimizer-coimage` — proposition — Optimizer Quotient as Coimage/Image Factorization
- `prop:optimizer-entropy-image` — proposition — Optimizer Quotient Entropy as Image-Size Entropy

### Intro / recap-only rows

- `thm:bayes-from-counting` — cite only — Probability Axioms from Counting (`01_introduction.tex`)
- `thm:fisher-rank-srank` — cite only — Fisher Information = Structural Rank (`01_introduction.tex`)
- `thm:entropy-rank` — cite only — Entropy Bounded by Structural Rank (`01_introduction.tex`)
- `thm:wasserstein-bridge` — cite only — Wasserstein Distance = Structural Rank (`01_introduction.tex`)
- `thm:rate-distortion-bridge` — cite only — Rate-Distortion = Structural Rank (`01_introduction.tex`)
- `thm:nontriviality-counting` — cite only — Information Requires Nontriviality (`01_introduction.tex`)
- `thm:bayes-optimal` — cite only — Bayes Minimizes Expected Log Loss (`01_introduction.tex`)
- `thm:measure-prerequisite` — cite only — Measure-Theoretic Typing (`01_introduction.tex`)
- `thm:quotient-universal` — cite only — Universal Property of the Optimizer Quotient (`01_introduction.tex`)

## Copy-Into-B Candidates

- These rows are canonically owned by Paper A in the ledger but are likely to need concise restatement in Paper B for independence.

- `def:decision-problem` — definition — Decision Problem (`latex_toc/content/02_formal_foundations.tex:10`)
- `prop:zero-epsilon-reduction` — proposition — Zero-$\varepsilon$ Reduction (`latex_toc/content/02_formal_foundations.tex:108`)
- `prop:selector-separation` — proposition — Selector-Level Separation Witness (`latex_toc/content/02_formal_foundations.tex:117`)
- `def:minimal-sufficient` — definition — Minimal Sufficient Set (`latex_toc/content/02_formal_foundations.tex:122`)
- `def:relevant` — definition — Relevant Coordinate (`latex_toc/content/02_formal_foundations.tex:126`)
- `prop:minimal-relevant-equiv` — proposition — Minimal-Set/Relevance Equivalence (`latex_toc/content/02_formal_foundations.tex:135`)
- `def:exact-identifiability` — definition — Exact Relevance Identifiability (`latex_toc/content/02_formal_foundations.tex:166`)
- `def:decision-equiv` — definition — Decision Equivalence (`latex_toc/content/02_formal_foundations.tex:189`)
- `def:projection` — definition — Projection (`latex_toc/content/02_formal_foundations.tex:20`)
- `prop:sufficiency-char` — proposition — Sufficiency Characterization (`latex_toc/content/02_formal_foundations.tex:201`)
- `def:optimizer` — definition — Optimizer Map (`latex_toc/content/02_formal_foundations.tex:28`)
- `rem:question-vs-problem` — remark — Decision Questions vs Decision Problems (`latex_toc/content/02_formal_foundations.tex:315`)
- `def:sufficient` — definition — Sufficient Coordinate Set (`latex_toc/content/02_formal_foundations.tex:37`)
- `prop:empty-sufficient-constant` — proposition — Empty-Set Sufficiency Equals Constant Decision Boundary (`latex_toc/content/02_formal_foundations.tex:46`)
- `prop:insufficiency-counterexample` — proposition — Insufficiency Equals Counterexample Witness (`latex_toc/content/02_formal_foundations.tex:57`)
- `def:selector` — definition — Deterministic Selector (`latex_toc/content/02_formal_foundations.tex:75`)
- `def:selector-sufficient` — definition — Selector-Level Sufficiency (`latex_toc/content/02_formal_foundations.tex:79`)
- `prop:set-to-selector` — proposition — Set-Level Target Dominates Selector Targets (`latex_toc/content/02_formal_foundations.tex:86`)
- `def:epsilon-sufficiency` — definition — $\varepsilon$-Optimal Set and $\varepsilon$-Sufficiency (`latex_toc/content/02_formal_foundations.tex:95`)
