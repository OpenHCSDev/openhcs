/-
  Paper 4: Decision-Relevant Uncertainty
  
  Information.lean - Information-Theoretic Characterization
  
  This file connects decision-relevant uncertainty to information theory:
  
  1. The decision quotient S/≈ has a natural entropy measure
  2. Sufficient coordinates carry exactly the decision-relevant information  
  3. Minimum sufficient sets minimize information while preserving decisions
  
  Key insight: Decision-relevance is about preserving information for a 
  specific task, not all information.
-/

import DecisionQuotient.Basic
import DecisionQuotient.Sufficiency
import DecisionQuotient.Tractable
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace DecisionQuotient

variable {A S : Type*} {n : ℕ}

/-! ## Counting Decision-Equivalence Classes -/

/-- The number of distinct Opt sets across all states -/
def DecisionProblem.numOptClasses [Fintype S] [DecidableEq (Set A)]
    (dp : DecisionProblem A S) : ℕ :=
  (Finset.univ.image dp.Opt).card

/-- Lower bound: at least 1 class (all states could have same Opt) -/
theorem DecisionProblem.numOptClasses_pos [Fintype S] [Nonempty S] 
    [DecidableEq (Set A)] (dp : DecisionProblem A S) :
    0 < dp.numOptClasses := by
  unfold numOptClasses
  apply Finset.card_pos.mpr
  simp only [Finset.image_nonempty]
  exact Finset.univ_nonempty

/-- Upper bound: at most |S| classes -/
theorem DecisionProblem.numOptClasses_le [Fintype S] [DecidableEq (Set A)]
    (dp : DecisionProblem A S) :
    dp.numOptClasses ≤ Fintype.card S := by
  unfold numOptClasses
  calc (Finset.univ.image dp.Opt).card 
      ≤ Finset.univ.card := Finset.card_image_le
    _ = Fintype.card S := Finset.card_univ

/-! ## Information Content of the Quotient -/

/-- Bits needed to identify a decision-equivalence class -/
noncomputable def DecisionProblem.quotientEntropy [Fintype S] 
    [DecidableEq (Set A)] (dp : DecisionProblem A S) : ℝ :=
  Real.log (dp.numOptClasses) / Real.log 2

/-- Quotient entropy is non-negative -/
theorem DecisionProblem.quotientEntropy_nonneg [Fintype S] [Nonempty S]
    [DecidableEq (Set A)] (dp : DecisionProblem A S) :
    0 ≤ dp.quotientEntropy := by
  unfold quotientEntropy
  apply div_nonneg
  · apply Real.log_nonneg
    have h := dp.numOptClasses_pos
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h)
  · apply Real.log_nonneg
    norm_num

/-- A problem has constant Opt if all states have the same optimal set -/
def DecisionProblem.hasConstantOpt' (dp : DecisionProblem A S) : Prop :=
  ∃ O : Set A, ∀ s : S, dp.Opt s = O

/-- With constant Opt, quotient entropy is 0 -/
theorem DecisionProblem.quotientEntropy_zero_of_constant [Fintype S] [Nonempty S]
    [DecidableEq (Set A)] (dp : DecisionProblem A S)
    (hconst : dp.hasConstantOpt') :
    dp.quotientEntropy = 0 := by
  unfold quotientEntropy numOptClasses hasConstantOpt' at *
  obtain ⟨O, hO⟩ := hconst
  have h : Finset.univ.image dp.Opt = {O} := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨s, hs⟩; rw [← hs, hO s]
    · intro hx; obtain ⟨s⟩ : Nonempty S := inferInstance
      exact ⟨s, hx ▸ (hO s)⟩
  rw [h, Finset.card_singleton]
  simp [Real.log_one]

/-! ## Sufficient Sets and Information -/

/-- A sufficient set carries enough information to determine Opt.
    Intuitively: projecting to I loses no decision-relevant information. -/
theorem sufficient_preserves_decisions [CoordinateSpace S n]
    (dp : DecisionProblem A S) (I : Finset (Fin n))
    (hsuff : dp.isSufficient I) :
    ∀ s s' : S, agreeOn s s' I → dp.Opt s = dp.Opt s' :=
  hsuff

/-- Sufficiency means Opt factors through the projection.
    This is a key insight: sufficient sets capture exactly the
    information needed for decision-making. -/
theorem sufficient_means_factorizable [CoordinateSpace S n]
    (dp : DecisionProblem A S) (I : Finset (Fin n))
    (hsuff : dp.isSufficient I) (s s' : S)
    (h : ∀ i ∈ I, CoordinateSpace.proj s i = CoordinateSpace.proj s' i) :
    dp.Opt s = dp.Opt s' :=
  hsuff s s' h

/-! ## Minimal Sufficient Sets -/

variable (n : ℕ) in
/-- A sufficient set is minimal if no proper subset is sufficient -/
def DecisionProblem.isMinimalSufficient' [CoordinateSpace S n]
    (dp : DecisionProblem A S) (I : Finset (Fin n)) : Prop :=
  dp.isSufficient I ∧ ∀ J : Finset (Fin n), J ⊂ I → ¬dp.isSufficient J

/-- Empty set is minimal sufficient iff the problem has constant Opt -/
theorem empty_minimal_sufficient_iff_constant (m : ℕ) [CoordinateSpace S m] [Nonempty S]
    (dp : DecisionProblem A S) :
    dp.isMinimalSufficient' m ∅ ↔ dp.hasConstantOpt' := by
  constructor
  · intro ⟨hsuff, _⟩
    use dp.Opt (Classical.arbitrary S)
    intro s
    apply hsuff
    intro i hi
    exact (by simpa using hi)
  · intro hconst
    constructor
    · intro s s' _
      obtain ⟨O, hO⟩ := hconst
      rw [hO s, hO s']
    · intro J hJ
      have h1 := Finset.ssubset_iff_subset_ne.mp hJ
      have h2 : J = ∅ := Finset.subset_empty.mp h1.1
      exact (h1.2 h2).elim

end DecisionQuotient
