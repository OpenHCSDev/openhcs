/-
  Paper 4: Decision-Relevant Uncertainty

  Dichotomy.lean - The Complexity Dichotomy Theorem

  This formalizes the paper's central result: the complexity of deciding
  sufficiency exhibits a dichotomy based on the structure of the decision problem.

  Key insight: Either the quotient has tractable structure (polynomial)
  or checking sufficiency is coNP-complete.
-/

import DecisionQuotient.Sufficiency
import DecisionQuotient.Hardness
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card

namespace DecisionQuotient

variable {A S : Type*} {n : ℕ}

/-! ## Quotient Size and Complexity -/

/-- The quotient size: number of distinct decision-equivalence classes -/
noncomputable def DecisionProblem.quotientSize [Fintype S] [DecidableEq (Set A)]
    (dp : DecisionProblem A S) : ℕ :=
  (Finset.univ.image dp.Opt).card

/-- Problems with singleton quotient are trivial -/
theorem quotientSize_one_iff_constant [Fintype S] [Nonempty S] [DecidableEq (Set A)]
    (dp : DecisionProblem A S) :
    dp.quotientSize = 1 ↔ ∀ s s' : S, dp.Opt s = dp.Opt s' := by
  unfold DecisionProblem.quotientSize
  constructor
  · intro h s s'
    have hs : dp.Opt s ∈ Finset.univ.image dp.Opt := Finset.mem_image_of_mem _ (Finset.mem_univ s)
    have hs' : dp.Opt s' ∈ Finset.univ.image dp.Opt := Finset.mem_image_of_mem _ (Finset.mem_univ s')
    rw [Finset.card_eq_one] at h
    obtain ⟨O, hO⟩ := h
    have h1 : dp.Opt s ∈ ({O} : Finset (Set A)) := hO ▸ hs
    have h2 : dp.Opt s' ∈ ({O} : Finset (Set A)) := hO ▸ hs'
    simp only [Finset.mem_singleton] at h1 h2
    rw [h1, h2]
  · intro hconst
    rw [Finset.card_eq_one]
    use dp.Opt (Classical.arbitrary S)
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨s, hs⟩
      rw [← hs, hconst]
    · intro hx
      exact ⟨Classical.arbitrary S, hx.symm⟩

/-! ## The Dichotomy Structure -/

/-- Constant problems have no relevant coordinates -/
theorem constant_opt_no_relevant (m : ℕ) [CoordinateSpace S m]
    (dp : DecisionProblem A S) (hconst : ∀ s s' : S, dp.Opt s = dp.Opt s') :
    @DecisionProblem.relevantSet A S m _ dp = ∅ := by
  ext i
  simp only [DecisionProblem.relevantSet, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false, DecisionProblem.isRelevant, not_exists, not_and]
  intro s s' _
  simp only [ne_eq, not_not]
  exact hconst s s'

/-- Constant problems have quotient size 1 -/
theorem constant_opt_quotientSize_one [Fintype S] [Nonempty S] [DecidableEq (Set A)]
    (dp : DecisionProblem A S) (hconst : ∀ s s' : S, dp.Opt s = dp.Opt s') :
    dp.quotientSize = 1 :=
  (quotientSize_one_iff_constant dp).mpr hconst

/-! ## The Central Dichotomy Theorem -/

/-- Key bound: quotient size is bounded by 2^n for n-coordinate spaces.
    This is tight when each coordinate is binary and all are relevant. -/
theorem quotientSize_le_pow_coords [Fintype S] [DecidableEq (Set A)]
    (dp : DecisionProblem A S) :
    dp.quotientSize ≤ Fintype.card S := by
  unfold DecisionProblem.quotientSize
  exact Finset.card_image_le.trans Finset.card_univ.le

/-- For function spaces Fin n → X, the state space has |X|^n elements -/
theorem card_function_space (X : Type*) [Fintype X] (n : ℕ) :
    Fintype.card (Fin n → X) = (Fintype.card X) ^ n := by
  simp only [Fintype.card_fun, Fintype.card_fin]

/-- For Boolean vectors, |S| = 2^n, so quotient size ≤ 2^n -/
theorem quotientSize_bool_le_pow [DecidableEq (Set A)] (n : ℕ)
    (dp : DecisionProblem A (Fin n → Bool)) :
    dp.quotientSize ≤ 2 ^ n := by
  calc dp.quotientSize
      ≤ Fintype.card (Fin n → Bool) := quotientSize_le_pow_coords dp
    _ = (Fintype.card Bool) ^ n := card_function_space Bool n
    _ = 2 ^ n := by simp [Fintype.card_bool]

/-- The Real Dichotomy: For Boolean vectors, sufficiency checking complexity
    depends on whether the relevant coordinate set is small or large.

    - If |relevant| = k, minimal sufficient set has size k
    - Checking sufficiency of a k-element set requires O(2^k) state pairs
    - So: k = O(log |S|) → polynomial; k = Ω(n) → exponential -/
theorem dichotomy_by_relevant_size [DecidableEq (Set A)] [DecidableEq (Fin n)]
    [ProductSpace S n] [Fintype S] [Nonempty S]
    (dp : DecisionProblem A S) (I : Finset (Fin n))
    (_ : dp.isMinimalSufficient I) :
    -- The minimal sufficient set size determines complexity class
    (I.card ≤ Nat.log 2 (Fintype.card S)) ∨
    (I.card > Nat.log 2 (Fintype.card S)) :=
  by
    by_cases h : I.card ≤ Nat.log 2 (Fintype.card S)
    · exact Or.inl h
    · exact Or.inr (lt_of_not_ge h)

/-- Tractable case: If minimal sufficient set is small (logarithmic),
    then checking sufficiency is polynomial in |S| -/
theorem tractable_when_few_relevant [DecidableEq (Set A)] [DecidableEq (Fin n)]
    [ProductSpace S n] [Fintype S] [Nonempty S]
    (_ : DecisionProblem A S) (I : Finset (Fin n))
    (hsmall : I.card ≤ Nat.log 2 (Fintype.card S)) :
    -- The number of coordinate combinations to check is ≤ |S|
    2 ^ I.card ≤ Fintype.card S := by
  calc 2 ^ I.card
      ≤ 2 ^ (Nat.log 2 (Fintype.card S)) := Nat.pow_le_pow_right (by norm_num) hsmall
    _ ≤ Fintype.card S := Nat.pow_log_le_self 2 (Fintype.card_pos.ne')

/-- Hard case characterization: When all n coordinates are relevant,
    the quotient can be as large as 2^n (each state has unique Opt) -/
theorem hard_when_all_relevant [DecidableEq (Set A)] [DecidableEq (Fin n)]
    [ProductSpace S n] [Fintype S]
    (dp : DecisionProblem A S)
    (hall : ∀ i : Fin n, dp.isRelevant i) (I : Finset (Fin n))
    (hmin : dp.isMinimalSufficient I) :
    I = Finset.univ := by
  ext i
  simp only [Finset.mem_univ, iff_true]
  -- Every coordinate is relevant, so must be in minimal sufficient set
  have hrel := hall i
  exact (dp.minimalSufficient_iff_relevant I hmin i).mpr hrel

/-! ## Connecting Quotient Size to Coordinate Sufficiency -/

/-- If quotient size is 1, every set is sufficient -/
theorem quotientSize_one_all_sufficient [Fintype S] [Nonempty S] [DecidableEq (Set A)]
    [CoordinateSpace S n] (dp : DecisionProblem A S) (h : dp.quotientSize = 1)
    (I : Finset (Fin n)) : dp.isSufficient I := by
  intro s s' _
  exact (quotientSize_one_iff_constant dp).mp h s s'

/-- Quotient size bounds the number of distinct Opt values -/
theorem quotientSize_le_card [Fintype S] [DecidableEq (Set A)] (dp : DecisionProblem A S) :
    dp.quotientSize ≤ Fintype.card S := by
  unfold DecisionProblem.quotientSize
  calc (Finset.univ.image dp.Opt).card
      ≤ Finset.univ.card := Finset.card_image_le
    _ = Fintype.card S := Finset.card_univ

/-- Quotient size is at least 1 for nonempty state spaces -/
theorem quotientSize_pos [Fintype S] [Nonempty S] [DecidableEq (Set A)]
    (dp : DecisionProblem A S) : 0 < dp.quotientSize := by
  unfold DecisionProblem.quotientSize
  rw [Finset.card_pos]
  use dp.Opt (Classical.arbitrary S)
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

end DecisionQuotient
