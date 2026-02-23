# Plan: Making Paper 5 as Airtight as Paper 4

## Current State of Paper 5 Lean

**Existing files:**
- Basic.lean: 438 lines - Definitions (Signal, Prior, Credibility, Domain)
- CheapTalk.lean: 286 lines - Theorems 3.1-3.4
- CostlySignals.lean: 235 lines - Theorems 4.1-4.2
- Impossibility.lean: 224 lines - Theorems 5.1-5.3
- Leverage.lean: 75 lines - Theorem 6.1
- CoherentStopping.lean: 179 lines - Additional coherence results

**Total: 1,437 lines of working Lean code**

## What's Missing (Gap Analysis)

### 1. Regime Typing
Paper 4 has explicit regimes (E, S, Q_fin, Q_bool). Paper 5 needs analogous typing:

**Add:**
```lean
/-- Credibility regime: specifies what the receiver knows about signal production -/
inductive CredibilityRegime
  | noPrior           -- Receiver has no prior information
  | knownPrior (p : ℝ)  -- Receiver knows prior p
  | knownDeception (d : ℝ)  -- Receiver knows deception rate
  | fullBayes (p d : ℝ)    -- Receiver knows both
```

### 2. Flag Comments (Misread Prevention)
Paper 4 has explicit markers. Add to Paper 5:

```lean
/-!
  IMPORTANT FLAG: Credibility bounds apply to CHEAP TALK only.
  Costly signals (with truth-dependent cost) can escape these bounds.
  See Theorem 4.1 (costly_signal_escape).
-/
```

### 3. Assumption Ledger
Paper 4 has explicit assumption tracking. Add:

```lean
/-- Assumption ledger for Paper 5 -/
structure CredibilityAssumptions where
  prior_positive     : 0 < p          -- Prior must be positive
  prior_le_one      : p ≤ 1          -- Prior is at most 1
  mimicabilityValid : 0 ≤ q ∧ q ≤ 1  -- Mimicability is a probability
  domainRationale   : CredibilityRegime  -- What receiver assumes
```

### 4. Cross-Paper Bridge (Paper 4 → Paper 5)
Add explicit bridge theorems:

```lean
/-- Bridge: Paper 4 integrity claims are cheap talk in Paper 5 -/
theorem integrity_claims_are_cheap_talk :
  -- "I act with integrity" has equal cost whether true or false
  isCheapTalk cost_integrity_true cost_integrity_false

/-- Bridge: Paper 4 competence demonstrations are costly signals -/
theorem competence_demonstrations_are_costly_signals (pf : Proof) :
  isCostlySignal (cost_of pf true) (cost_of pf false)

/-- Bridge: Paper 4 abstention maps to Paper 5 credibility bound -/
theorem abstention_credibility_bound :
  credibility (abstention_signal R) ≤ cheapTalkBound p q
```

### 5. Theorem Index Matrix
Paper 4 has a claim coverage matrix. Add analogous index:

| Theorem | Lean Definition | Paper Section | Status |
|---------|----------------|---------------|--------|
| 3.1 | `cheap_talk_bound` | Section 3 | ✓ |
| 3.2 | `magnitude_penalty` | Section 3 | ✓ |
| 3.3 | `emphasis_penalty` | Section 3 | ✓ |
| 3.4 | `meta_assertion_trap` | Section 3 | ✓ |
| 4.1 | `costly_signal_escape` | Section 4 | ✓ |
| 4.2 | `proof_as_ultimate_signal` | Section 4 | ✓ |
| 5.1 | `text_credibility_bound` | Section 5 | ✓ |
| 5.2 | `memory_iteration_futility` | Section 5 | ✓ |
| 6.1 | `brevity_principle` | Section 6 | ✓ |

### 6. Missing Theorem Proofs (Hand-wavy Parts)

**Theorem 3.3 (Emphasis Penalty)** - Already formalized but check:
- suspicion function defined ✓
- monotonicity proven ✓
- threshold exists (use k=0) ✓

**Theorem 3.4 (Meta-Assertion Trap)** - Currently trivial (0 ≤ ε):
- Needs stronger formalization
- Add: meta-assertion increases effective mimicability

### 7. Domain Independence Theorems
Paper 5 already has domain independence (lines 66-100 in Basic.lean):
- `domain_independence_math_not_implies_social` ✓
- `domain_independence_social_not_implies_math` ✓
- `machine_proof_domain_specificity` ✓

## Implementation Plan

### Phase 1: Regime Typing
Create `Credibility/Regime.lean`:
- Define CredibilityRegime inductive
- Add regime-specific credibility bounds
- Prove regime transfer theorems

### Phase 2: Flag Comments
Add to each file:
- Basic.lean: Flag cheap talk vs costly signal distinction
- CheapTalk.lean: Flag bounds apply to cheap talk only
- CostlySignals.lean: Flag this is how you escape the bounds
- Impossibility.lean: Flag these are impossibility results

### Phase 3: Cross-Paper Bridge
Create `Credibility/Paper4Bridge.lean`:
- `integrity_as_cheap_talk`
- `competence_as_costly_signal`
- `abstention_credibility_matrix`

### Phase 4: Theorem Index
Add comprehensive theorem index to paper markdown

### Phase 5: Tighten Theorem 3.4
Strengthen meta_assertion_trap to be non-trivial

## Files to Create/Modify

1. **NEW**: `Credibility/Regime.lean` - regime typing
2. **MODIFY**: `Credibility/Basic.lean` - add flag comments
3. **MODIFY**: `Credibility/CheapTalk.lean` - add flag comments  
4. **MODIFY**: `Credibility/Impossibility.lean` - strengthen 3.4
5. **NEW**: `Credibility/Paper4Bridge.lean` - cross-paper connections
6. **MODIFY**: paper5 markdown - add theorem index matrix

## Priority

1. **HIGH**: Add flag comments (prevent misreads)
2. **HIGH**: Create Paper 4 bridge (connect frameworks)
3. **MEDIUM**: Add regime typing (match Paper 4 structure)
4. **MEDIUM**: Tighten Theorem 3.4
5. **LOW**: Theorem index (document what exists)
