# 2026-03-04 — Handle Refactor Plan (Paper 1 Canonical Ownership)

## Decision
Use **Paper 1** as the canonical home for the graph-entropy handle layer if we proceed with refactor.

Rationale: Paper 2 already depends on Paper 1; we should keep dependency flow one-way and avoid any Paper 1 → Paper 2 edge.

---

## Structural Rule (Non-Negotiable)
1. `paper1/proofs` must remain dependency-root (no import from `paper2/proofs`).
2. `paper2/proofs` may depend on `paper1/proofs` only.
3. Stable handle IDs (`GPH*`) must not change once moved.

---

## Scope
### In scope
- Move canonical graph-entropy handle definitions to Paper 1.
- Make Paper 2 import Paper 1 canonical handles directly (no wrapper layer).
- Preserve current Lean handle IDs used in manuscript tags.

### Out of scope
- Renaming handle IDs.
- Reframing paper prose beyond minimal import/path updates.
- Any new theoretical claims.

---

## Execution Plan

## Operating Principle — Fail Fast
- Do **not** add migration shims/wrappers.
- Accept compile breaks during cutover as expected diagnostics.
- Use Lean errors as structural guidance; fix root cause immediately.

## Phase 0 — Baseline Freeze
- Record green baseline:
  - `lake build` in `paper1/proofs`
  - `lake build` in `paper2/proofs`
  - submission builds for `paper1_jsait` and `paper2_it`
- Snapshot generated handle tables for diffing after refactor.

## Phase 1 — Extract IT Core Proof Modules to Paper 1
- Create Paper 1-side neutral modules (no `Ssot.*` dependency), e.g.:
  - `paper1/proofs/InfoTheory/GraphEntropyCore.lean`
  - `paper1/proofs/InfoTheory/GraphEntropyAsymptotic.lean`
- Port declarations from current:
  - `paper2/proofs/Ssot/GraphEntropy.lean`
  - `paper2/proofs/Ssot/GraphEntropyAsymptotic.lean`
- Keep theorem names stable where possible.

## Phase 2 — Move Canonical Handle Ownership to Paper 1
- Add/extend Paper 1 handle module (recommended separate file):
  - `paper1/proofs/HandleAliasesIT.lean`
- Define canonical `GPH*` IDs there (`GPH2` … latest).
- Ensure Paper 1 graph export/decl export sees these aliases.

## Phase 3 — Direct Paper 2 Cutover (No Wrappers)
- Remove `GPH*` ownership from `paper2/proofs/Ssot/HandleAliases.lean`.
- Import Paper 1 canonical handle module(s) directly where needed.
- Update any broken imports/usages until `lake build` is green.
- Do not retain fallback aliases in Paper 2.

## Phase 4 — Build/Artifact Integration
- Re-run generation pipeline:
  - `lake build` (paper1, paper2)
  - `python scripts/build_papers.py submission paper1_jsait -q`
  - `python scripts/build_papers.py submission paper2_it -q`
- Confirm submission handle table still includes only used handles and links resolve.

## Phase 5 — Cutover Validation
- Validate no dependency inversion:
  - Paper 1 `lakefile.lean` has no Paper 2 requirement.
  - Paper 2 still only requires Paper 1 (`dep_paper1`) and mathlib.
- Validate handle stability:
  - Same handle IDs map to semantically same theorem statements.
- Validate manuscript stability:
  - No broken `\LH{...}` references.

---

## Acceptance Criteria
- Paper 1 is canonical owner of graph-entropy handle IDs.
- Paper 2 compiles without owning those canonical definitions.
- No circular package dependency introduced.
- Existing paper tags continue to compile and hyperlink correctly.
- Submission builds for Paper 1 and Paper 2 remain green.

---

## Risks and Mitigations
- **Risk:** Namespace drift during module move.  
  **Mitigation:** Keep theorem names stable; fix all call sites directly (no alias indirection).

- **Risk:** Handle auto-table churn.  
  **Mitigation:** Diff generated `lean_handle_ids_auto.tex` before/after.

- **Risk:** Silent dependency inversion.  
  **Mitigation:** Treat `lakefile` checks as a hard gate.

---

## Recommended Implementation Order
1. Move proof modules first.
2. Add Paper 1 canonical handle file.
3. Cut Paper 2 directly to Paper 1 imports (no wrappers).
4. Rebuild both papers and submission artifacts.
5. Keep only canonical ownership in Paper 1; remove all duplicate Paper 2 handle definitions.
