# Paper 5 Lean Formalization Gap Analysis

## Summary
Paper 5 claims "430 lines, 0 sorry" but the actual Lean formalization is minimal.
The paper contains proof *sketches* in the appendix, not actual working Lean code.

## Gap Analysis by Theorem

### Theorem 3.1: Cheap Talk Bound
- **Paper claim**: Formalized
- **Reality**: `cheap_talk_bound` in appendix shows `...` placeholder (lines 450-459)
- **Gap**: Not actually proven in Lean - just shows structure
- **Paper 4 connection**: Related to `IntegrityCompetence` - integrity claims are cheap talk

### Theorem 3.2: Magnitude Penalty  
- **Paper claim**: Formalized
- **Reality**: `magnitude_penalty` shows `...` placeholder (lines 462-468)
- **Gap**: Not actually proven in Lean
- **Paper 4 connection**: Maps to `prop:attempted-competence-matrix` - higher-stakes claims (higher magnitude) need more competence

### Theorem 3.3: Emphasis Penalty
- **Paper claim**: Formally stated
- **Reality**: `emphasis_penalty` has skeleton but suspicion_increasing is not defined/proven
- **Gap**: PROOF IS HAND-WAVY EVEN IN PAPER - no formal threshold k* given
- **Paper 4 connection**: None directly - this is new

### Theorem 4.1: Costly Signal Escape
- **Paper claim**: Formalized
- **Reality**: No Lean code shown for this theorem
- **Gap**: Not formalized
- **Paper 4 connection**: `prop:integrity-competence-separation` - integrity forces abstention, costly signals (proofs) escape

### Theorem 5.1: Text Credibility Bound
- **Paper claim**: Formalized  
- **Reality**: `text_credibility_bound` shows `...` placeholder (lines 486-498)
- **Gap**: Not actually proven in Lean
- **Paper 4 connection**: Related to `ClaimClosure` - claims about sufficiency require costly signals

## What Actually Exists in Lean

The header states: "Lean: 430 lines, 0 theorems" but the file at `docs/papers/proofs/paper5_*.lean` appears to be empty or minimal.

## Recommended Formalization Plan

### Phase 1: Core Definitions (Paper 5 → Paper 4 bridge)
Define in Lean:
```
/-- Signal with content, truth value, production cost -/
structure Signal where
  content : String
  truthValue : Bool
  cost : ℝ≥0

/-- Cheap talk: cost independent of truth -/
def isCheapTalk (s : Signal) : Prop :=
  s.costIfTrue = s.costIfFalse

/-- Costly signal: higher cost if false -/
def isCostlySignal (s : Signal) : Prop :=
  s.costIfFalse > s.costIfTrue
```

### Phase 2: Cheap Talk Bound (Theorem 3.1)
Formalize and prove:
```
theorem cheap_talk_bound (p q : ℝ) (hp : 0 < p ∧ p ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) :
  credibility p q ≤ p / (p + (1-p) * q) := ...
```
Maps to: `IntegrityCompetence.admissible_matrix_counts`

### Phase 3: Costly Signal Escape (Theorem 4.1)  
Formalize and prove:
```
theorem costly_signal_escape (p Δ : ℝ) (hΔ : Δ > 0) :
  credibility_with_cost p Δ → 1 as Δ → ∞ := ...
```
Maps to: `ClaimClosure.integrity_resource_bound` - integrity forces abstention, but costly signals escape

### Phase 4: Connection to Paper 4

Key bridge theorems to add to Paper 5:

1. **Integrity as Cheap Talk**
   ```
   theorem integrity_claims_are_cheap_talk (c : Claim) :
     isCheapTalk (make_signal "I act with integrity") := ...
   ```
   Connects to: Paper 4 `def:solver-integrity`

2. **Competence Demonstrations as Costly Signals**
   ```
   theorem competence_demonstration_is_costly_signal (c : Claim) (pf : Proof c) :
     isCostlySignal pf := ...
   ```
   Connects to: Paper 4 `def:competence-regime`

3. **Abstention as Rational Response**
   ```
   theorem abstention_under_integrity (R : Regime) (Q : CertifyingSolver) :
     CompetentOn R Q → (∃ x, Q.solve x = none) → 
       credibility (abstention_signal Q) ≤ cheap_talk_bound := ...
   ```
   Connects to: Paper 4 `prop:integrity_resource_bound`

### Phase 5: Fill Emphasis Penalty (Theorem 3.3)
This needs new formalization - not in Paper 4:
- Define suspicion function σ(n)
- Prove threshold exists
- Formalize the decreasing credibility claim

## Files to Create/Modify

1. `docs/papers/paper5_credibility/proofs/Credibility/Basic.lean` - definitions
2. `docs/papers/paper5_credibility/proofs/Credibility/CheapTalk.lean` - Theorems 3.1-3.3
3. `docs/papers/paper5_credibility/proofs/Credibility/CostlySignals.lean` - Theorem 4.1  
4. `docs/papers/paper5_credibility/proofs/Credibility/Impossibility.lean` - Theorem 5.1
5. `docs/papers/paper5_credibility/proofs/Credibility/Paper4Bridge.lean` - NEW: cross-paper connections

## Cross-Reference Matrix

| Paper 5 Theorem | Paper 4 Connection | Gap Status |
|-----------------|-------------------|------------|
| 3.1 Cheap Talk Bound | `IntegrityCompetence.admiisible_matrix_counts` | PROOF SKELETON ONLY |
| 3.2 Magnitude Penalty | `prop:attempted-competence-matrix` | PROOF SKELETON ONLY |
| 3.3 Emphasis Penalty | NONE | HAND-WAVY |
| 4.1 Costly Signal Escape | `ClaimClosure.integrity_resource_bound` | NOT FORMALIZED |
| 5.1 Text Credibility Bound | `ClaimClosure` | PROOF SKELETON ONLY |
| 6.1 Credibility Leverage | Paper 3 `Leverage` | NOT MAPPED |

## Priority

1. **HIGH**: Theorem 3.1 (cheap talk bound) - foundation of entire framework
2. **HIGH**: Theorem 4.1 (costly signal escape) - connects to Paper 4 integrity
3. **MEDIUM**: Theorem 5.1 (text bound) - impossibility result  
4. **LOW**: Theorem 3.2 (magnitude) - follows from 3.1
5. **LOW**: Theorem 3.3 (emphasis) - needs new formalization work
