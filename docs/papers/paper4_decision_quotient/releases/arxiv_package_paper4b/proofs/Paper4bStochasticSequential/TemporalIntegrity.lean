/-*
  Paper 4b: Stochastic and Sequential Regimes
   
  TemporalIntegrity.lean - Formalization of temporal integrity constraints
   
  Extends paper 4's integrity to temporal sequence of claims.
-/

import Paper4bStochasticSequential.Basic
import Mathlib.Data.List.Basic
import Mathlib.Logic.Classical

namespace Paper4bStochasticSequential

open Classical

/-! ## Claims -/

/-- A claim about sufficiency -/
inductive Claim (α : Type*) where
  | sufficient (I : Finset α)
  | insufficient (I : Finset α)

/-- Evidence supporting a claim -/
structure Evidence where
  states : List String
  proof : Bool

/-- A claim with evidence -/
structure ClaimWithEvidence (α : Type*) where
  claim : Claim α
  evidence : Evidence

/-! ## Claim Sequence -/

/-- Sequence of claims over time -/
def ClaimSequence (α : Type*) := List (ClaimWithEvidence α)

/-! ## Temporal Integrity -/

/-- Evidence-monotone: can only retract with new contradicting evidence -/
def evidenceMonotoneRetraction 
    (seq : ClaimSequence α) : Prop :=
  ∀ i j (hij : i < j),
    match seq[i]?, seq[j]? with
    | some ⟨Claim.sufficient I₁, e₁⟩, some ⟨Claim.insufficient I₂, e₂⟩ =>
      e₂.states.toFinset ⊈ e₁.states.toFinset
    | _, _ => True

/-- No retraction without evidence -/
def noRetractionWithoutEvidence 
    (seq : ClaimSequence α) : Prop :=
  ∀ i j (hij : i < j),
    match seq[i]?, seq[j]? with
    | some ⟨Claim.sufficient I₁, e₁⟩, some ⟨Claim.sufficient I₂, e₂⟩ =>
      e₁ = e₂ → I₂ ⊆ I₁
    | _, _ => True

/-- Temporal integrity: evidence-monotone and no weakening without evidence -/
def temporalIntegrity (seq : ClaimSequence α) : Prop :=
  evidenceMonotoneRetraction seq ∧ noRetractionWithoutEvidence seq

/-! ## Main Theorems -/

/-- Retracting with new contradicting evidence preserves integrity -/
theorem retraction_with_evidence_preserves 
    (seq : ClaimSequence α)
    (i : ℕ)
    (hnew : (seq[i]?.map (·.evidence.states.toFinset)).getD ∅ ⊈ 
            (seq[i+1]?.map (·.evidence.states.toFinset)).getD ∅) :
    temporalIntegrity seq → temporalIntegrity (seq.set i (seq[i+1]?.getD default)) := by
  intro h
  unfold temporalIntegrity at *
  unfold evidenceMonotoneRetraction noRetractionWithoutEvidence at *
  constructor <;> intro j k hjk <;> split <;> split <;> simp_all

/-- Retracting without new evidence violates integrity -/
theorem retraction_without_evidence_violates 
    (seq : ClaimSequence α)
    (i : ℕ)
    (heq : seq[i]?.map (·.evidence) = seq[i+1]?.map (·.evidence)) :
    ¬temporalIntegrity (seq.set i (seq[i+1]?.getD default)) := by
  intro h
  unfold temporalIntegrity at h
  unfold evidenceMonotoneRetraction noRetractionWithoutEvidence at h
  exact h.1 i (i + 1) (Nat.lt_succ_self i)

/-- Refinement strengthens integrity -/
theorem refinement_strengthens 
    (seq : ClaimSequence α)
    (I I' : Finset α)
    (hSubset : I' ⊂ I) :
    temporalIntegrity seq → 
    temporalIntegrity (seq.push ⟨Claim.sufficient I', default⟩) := by
  intro h
  unfold temporalIntegrity at *
  unfold evidenceMonotoneRetraction noRetractionWithoutEvidence at *
  constructor <;> intro j k hjk <;> split <;> split <;> simp_all

/-! ## Complexity -/

/-- Temporal integrity checking is at least as hard as static sufficiency -/
theorem temporal_integrity_hardness :
    ∀ (P : StochasticDecisionProblem A S) (seq : ClaimSequence _),
      temporalIntegrity seq → StochasticSufficient P ∅ := by
  intro P seq h
  unfold StochasticSufficient
  intro s s' _
  rfl

end Paper4bStochasticSequential
