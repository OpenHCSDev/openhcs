# Plan: Epsilon-Grace Competence Extension

## Goal
Expand the IntegrityCompetence framework to include epsilon (grace) factors for approximate competence, while preserving integrity as the primary optimization objective.

## Current State (IntegrityCompetence.lean:1-162)

### Existing Definitions
- `Regime` - tuple of (inScope instances, encoding length, resource budget)
- `CertifyingSolver` - (solve, check, solveCost) 
- `SolverIntegrity` - soundness + checker correctness
- `CompetentOn` - integrity + non-abstaining coverage + budget bound
- `OverModelVerdict` - rational/irrational/inadmissible
- Matrix theorems showing 1 rational cell, 3 irrational cells

### Epsilon-Sufficiency Already in Paper
- `epsOpt(s)` - actions within ε of optimal
- `ε-sufficient` - projection equality implies ε-optimal-set equality
- `prop:zero-epsilon-reduction` - ε=0 is exact sufficiency

## Proposed Extensions

### 1. Epsilon-Certifying Solver
Add epsilon parameter to the checker for approximate correctness:

```lean
structure EpsilonCertifyingSolver (X Y W : Type) where
  solve : X → Option (Y × W)
  check : X → Y → W → ℝ → Prop  -- checker takes epsilon
  solveCost : X → ℕ
  epsilon : ℝ  -- grace parameter, ε ≥ 0
```

### 2. Epsilon-Integrity
Strengthen: checker must accept only if output is approximately correct within ε:

```lean
def EpsilonIntegrity (R : Set (X × Y)) (ε : ℝ) (Q : EpsilonCertifyingSolver X Y W) : Prop :=
  (∀ x y w, Q.solve x = some) → Q.check (y, w x y w ε) ∧
  (∀ x y w, Q.check x y w ε → (x, y) ∈ R_ε)  -- R_ε = ε-approximate relation
```

Where `(x, y) ∈ R_ε` means y is ε-approximately correct for x.

### 3. Epsilon-Competence
Extend competence with epsilon grace:

```lean
def EpsilonCompetentOn (R : Set (X × Y)) (ε : ℝ) (Γ : Regime X) 
    (Q : EpsilonCertifyingSolver X Y W) : Prop :=
  EpsilonIntegrity R ε Q ∧
  (∀ x, x ∈ Γ.inScope → ∃ y w, Q.solve x = some (y, w)) ∧
  (∀ x, x ∈ Γ.inScope → Q.solveCost x ≤ Γ.budget (Γ.encLen x))
```

### 4. Epsilon-Relation Definitions
Define what "ε-approximately correct" means for the decision relevance setting:

```lean
def ApproxSufficient (ε : ℝ) (I : Set ℕ) (D : DecisionProblem) : Prop :=
  ∀ s s' : D.State, 
    (proj I s) = (proj I s') → 
    (epsOpt ε s).1 = (epsOpt ε s').1
    -- or set equality of ε-optimal action sets
```

### 5. Integrity-Primary Theorems
Key theorems to prove:

1. **Integrity is non-negotiable**: Even with epsilon grace, integrity cannot be relaxed
   ```lean
   theorem epsilon_competence_requires_integrity (R Γ ε Q) :
       EpsilonCompetentOn R ε Γ Q → EpsilonIntegrity R ε Q
   ```

2. **Exact competence implies epsilon competence**: ε=0 recovers original
   ```lean
   theorem exact_implies_epsilon_competence (R Γ Q) :
       CompetentOn R Γ Q → EpsilonCompetentOn R 0 Γ Q
   ```

3. **Epsilon expands the rational zone**: More cells become rational with epsilon
   ```lean
   theorem epsilon_expands_rational_zone (ε > 0) :
       -- show that approximate competence available → more rational verdicts
   ```

4. **Grace factor preserves integrity**: Epsilon relaxation doesn't compromise integrity
   ```lean
   theorem epsilon_integrity_preserves_soundness (R ε Q h) :
       -- If checker passes with ε, output is ε-approximately correct
   ```

### 6. New Matrix with Epsilon
Extend the OverModelVerdict to include epsilon dimension:

```lean
def overModelVerdictEpsilon 
    (integrity attempted competenceExact competenceEpsilon : Bool) 
    (ε > 0) : OverModelVerdict :=
  if !integrity then OverModelVerdict.inadmissible
  else if attempted && !competenceExact && competenceEpsilon 
    then OverModelVerdict.rational  -- approximate competence saves us
  else if attempted && competenceExact 
    then OverModelVerdict.rational  -- exact is always fine
  else OverModelVerdict.irrational
```

### 7. Documentation/Comments
Add clear comments flagging:
- "Integrity is the optimization factor - never relaxed"
- "Competence is a plus, not a requirement"
- "Epsilon grace expands competence without compromising integrity"

## Files to Modify

1. `docs/papers/paper4_decision_quotient/proofs/DecisionQuotient/IntegrityCompetence.lean`
   - Add epsilon definitions
   - Add epsilon theorems
   - Add flag comments

## Flag Locations (for misread prevention)

Add explicit comments at:
- [ ] Top of file: "INTEGRITY IS PRIMARY. Competence is desirable but not required."
- [ ] Before each epsilon definition: "This relaxes COMPETENCE, never INTEGRITY"
- [ ] In the matrix theorems: "Note: integrity=true is prerequisite for rational/irrational; only competence is expanded"

## Verification
- All theorems must compile in Lean 4
- Must show: exact competence → epsilon competence (ε=0 case)
- Must show: epsilon competence requires integrity (cannot skip integrity even with grace)

## Integration with Paper
- Links to existing `epsOpt` and `epsilon-sufficiency` (paper lines 160-166)
- Links to `prop:zero-epsilon-reduction` (paper line 166)
- Mechanizes the "grace factor" concept discussed in review
