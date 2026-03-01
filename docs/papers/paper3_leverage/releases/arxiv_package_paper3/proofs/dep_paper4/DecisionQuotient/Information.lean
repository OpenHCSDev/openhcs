/-
  Paper 4: Decision-Relevant Uncertainty
  
  Information.lean - Information-Theoretic Characterization
  
  This file connects decision-relevant uncertainty to information theory:
  
  1. The decision quotient S/≈ has a natural entropy measure
  2. Sufficient coordinates carry exactly the decision-relevant information  
  3. Minimum sufficient sets minimize information while preserving decisions
  
  Key insight: Decision-relevance is about preserving information for a 
  specific task, not all information.

  ## Triviality Level
  TRIVIAL: This connects to information theory. The novelty is in the 
  sufficiency definitions (Sufficiency.lean), not in applying entropy.

  ## Dependencies
  - Chain: Basic.lean → Sufficiency.lean (core) → here
  - The nontrivial work is already in Sufficiency.lean definitions
-/

import DecisionQuotient.Sufficiency
import DecisionQuotient.Tractable
import DecisionQuotient.Tractability.StructuralRank
import DecisionQuotient.Instances
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
    simp at hi
  · intro hconst
    constructor
    · intro s s' _
      obtain ⟨O, hO⟩ := hconst
      rw [hO s, hO s']
    · intro J hJ
      have h2 : J = ∅ := Finset.subset_empty.mp hJ.subset
      exact absurd h2 hJ.ne

/-! ## Entropy-Rank Inequality for Binary Coordinate Spaces

We prove: quotientEntropy ≤ srank for binary coordinate spaces S = (Fin 2)^n.

Key steps:
1. The relevant set R is sufficient (erase irrelevant coords one by one)
2. Projection to R maps into 2^|R| values (each coord has 2 values)
3. Therefore numOptClasses ≤ 2^srank
-/

open Classical

/-- The relevant coordinate set is sufficient.
    Proof: Start with univ (sufficient if injective), erase irrelevant coords one by one. -/
theorem relevantSet_isSufficient [DecidableEq (Fin n)] [ProductSpace S n]
    (dp : DecisionProblem A S)
    (hinj : ∀ s s' : S, (∀ i : Fin n, CoordinateSpace.proj s i = CoordinateSpace.proj s' i) → s = s') :
    dp.isSufficient (Finset.univ.filter dp.isRelevant) := by
  let R := Finset.univ.filter dp.isRelevant
  let Irrelevant := Finset.univ.filter dp.isIrrelevant
  have hbase : dp.isSufficient Finset.univ := dp.univ_sufficient_of_injective hinj
  have hInd : ∀ (J : Finset (Fin n)), (∀ j ∈ J, dp.isIrrelevant j) →
      dp.isSufficient (Finset.univ \ J) := by
    intro J
    refine Finset.induction ?_ ?_ J
    · intro _; exact hbase
    · intro a s _ hInd' hIrrel
      have hIrrel_a := hIrrel a (Finset.mem_insert_self a s)
      have hIrrel_s : ∀ j ∈ s, dp.isIrrelevant j := fun j hj => hIrrel j (Finset.mem_insert_of_mem hj)
      have hSuff := hInd' hIrrel_s
      have hErase := dp.sufficient_erase_irrelevant' (Finset.univ \ s) a hSuff hIrrel_a
      convert hErase using 1
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, ne_eq, Finset.mem_univ, true_and]
      tauto
  have hall : ∀ j ∈ Irrelevant, dp.isIrrelevant j := fun j hj => (Finset.mem_filter.mp hj).2
  have hsuff := hInd Irrelevant hall
  have heqR : Finset.univ \ Irrelevant = R := by
    ext i
    simp only [R, Irrelevant, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_filter]
    -- Goal: ¬ dp.isIrrelevant i ↔ dp.isRelevant i
    -- Use: dp.irrelevant_iff_not_relevant i : dp.isIrrelevant i ↔ ¬ dp.isRelevant i
    rw [dp.irrelevant_iff_not_relevant i]
    by_cases h : dp.isRelevant i <;> simp [h]
  rw [heqR] at hsuff
  exact hsuff

/-! ## Cardinality Bounds for Binary Spaces -/

/-- A problem is nontrivial if it has more than one Opt-equivalence class.
    This means different states can have different optimal decisions. -/
def DecisionProblem.isNontrivial [Fintype S] [DecidableEq (Set A)]
    (dp : DecisionProblem A S) : Prop :=
    dp.numOptClasses > 1

/-- Nontrivial problems have at least one relevant coordinate.
    Proof: If no coordinate is relevant, all coords are irrelevant,
    which means changing any single coord never changes Opt.
    By iterating, no change to any coords changes Opt, so Opt is constant.

    This is the "DOF ≥ 1" theorem: distinguishability requires at least
    one degree of freedom. -/
theorem nontrivial_implies_srank_pos [DecidableEq (Fin n)] [ProductSpace S n]
    [Fintype S] [Nonempty S] [DecidableEq (Set A)] (dp : DecisionProblem A S)
    (hnontriv : dp.isNontrivial)
    (hinj : ∀ s s' : S, (∀ i : Fin n, CoordinateSpace.proj s i = CoordinateSpace.proj s' i) → s = s') :
    dp.srank ≥ 1 := by
  unfold DecisionProblem.isNontrivial DecisionProblem.numOptClasses at hnontriv
  by_contra hzero
  push_neg at hzero
  have hsrank_zero : dp.srank = 0 := by omega
  rw [dp.srank_zero_iff_constant] at hsrank_zero
  have hconst : ∀ i, dp.isIrrelevant i := hsrank_zero
  -- Build up sufficiency by removing irrelevant coordinates one at a time
  have hbase : dp.isSufficient (Finset.univ : Finset (Fin n)) := by
    intro s s' hagree
    have heq : s = s' := hinj s s' (fun i => hagree i (Finset.mem_univ i))
    rw [heq]
  have hInd : ∀ (J : Finset (Fin n)), (∀ j ∈ J, dp.isIrrelevant j) →
      dp.isSufficient (Finset.univ \ J) := by
    intro J
    refine Finset.induction ?_ ?_ J
    · intro _; exact hbase
    · intro a s _ hInd' hIrrel
      have hIrrel_a := hIrrel a (Finset.mem_insert_self a s)
      have hIrrel_s : ∀ j ∈ s, dp.isIrrelevant j := fun j hj => hIrrel j (Finset.mem_insert_of_mem hj)
      have hSuff := hInd' hIrrel_s
      have hErase := dp.sufficient_erase_irrelevant' (Finset.univ \ s) a hSuff hIrrel_a
      convert hErase using 1
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, ne_eq, Finset.mem_univ, true_and]
      tauto
  have hempty : dp.isSufficient (∅ : Finset (Fin n)) := by
    have hall : ∀ j ∈ (Finset.univ : Finset (Fin n)), dp.isIrrelevant j := fun j _ => hconst j
    have hsuff := hInd Finset.univ hall
    simpa using hsuff
  have hconst_opt : ∀ s s', dp.Opt s = dp.Opt s' := by
    intro s s'
    apply hempty
    intro i hi
    simp at hi
  have hone : (Finset.univ.image dp.Opt).card = 1 := by
    rw [Finset.card_eq_one]
    use dp.Opt (Classical.arbitrary S)
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨s, hs⟩; rw [← hs, hconst_opt s (Classical.arbitrary S)]
    · intro hx; exact ⟨Classical.arbitrary S, hx.symm⟩
  omega

/-- For boolean coordinate spaces (S = Fin n → Bool), the number of distinct
    Opt values is at most 2^srank, where srank is the number of relevant coordinates.

    This is the key combinatorial bound connecting srank to entropy.

    Proof:
    1. The relevant set R is sufficient (Opt depends only on R-coords)
    2. Two states with same R-restriction have same Opt
    3. There are at most 2^|R| distinct R-restrictions
    4. Therefore numOptClasses ≤ 2^|R| = 2^srank -/
theorem numOptClasses_le_pow_srank_binary [DecidableEq (Set A)]
    (dp : DecisionProblem A (Fin n → Bool)) :
    dp.numOptClasses ≤ 2 ^ dp.srank := by
  -- Define the relevant set R
  let R := Finset.univ.filter dp.isRelevant
  -- R is sufficient: states agreeing on R have the same Opt
  have hinj : ∀ s s' : Fin n → Bool,
      (∀ i : Fin n, CoordinateSpace.proj s i = CoordinateSpace.proj s' i) → s = s' := by
    intro s s' h
    funext i
    exact h i
  have hsuff : dp.isSufficient R := relevantSet_isSufficient dp hinj
  -- Define the restriction to R: pat(s) = s restricted to R
  let pat : (Fin n → Bool) → (R → Bool) := fun s => fun ⟨i, _⟩ => s i
  -- Key: if pat s = pat s', then agreeOn s s' R, so Opt s = Opt s'
  have hfactor : ∀ s s' : Fin n → Bool, pat s = pat s' → dp.Opt s = dp.Opt s' := by
    intro s s' hpat
    apply hsuff
    intro i hi
    have : pat s ⟨i, hi⟩ = pat s' ⟨i, hi⟩ := congrFun hpat ⟨i, hi⟩
    exact this
  -- The image of Opt factors through the image of pat
  -- So card(image Opt) ≤ card(image pat) ≤ card(R → Bool) = 2^|R|
  have hcard_pat : Fintype.card (R → Bool) = 2 ^ R.card := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  have hcard_R : R.card = dp.srank := rfl
  -- Define a function from R-patterns to Opt values
  let optFromPat : (R → Bool) → Set A := fun p =>
    dp.Opt (fun i => if h : i ∈ R then p ⟨i, h⟩ else false)
  -- The Opt image is contained in the optFromPat image
  have hsubset : Finset.univ.image dp.Opt ⊆ Finset.univ.image optFromPat := by
    intro optVal hoptVal
    rw [Finset.mem_image] at hoptVal ⊢
    obtain ⟨s, _, hs⟩ := hoptVal
    use pat s
    constructor
    · exact Finset.mem_univ _
    · -- Show optFromPat (pat s) = Opt s
      rw [← hs]
      apply hfactor
      funext ⟨i, hi⟩
      simp only [pat, dif_pos hi]
  -- numOptClasses = card(Opt image) ≤ card(optFromPat image) ≤ card(R → Bool)
  calc dp.numOptClasses
      = (Finset.univ.image dp.Opt).card := rfl
    _ ≤ (Finset.univ.image optFromPat).card := Finset.card_le_card hsubset
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = Fintype.card (R → Bool) := Finset.card_univ
    _ = 2 ^ R.card := hcard_pat
    _ = 2 ^ dp.srank := by rw [hcard_R]

/-- Minimum distinguishability theorem: For binary coordinate spaces (S = Fin n → Bool),
    a nontrivial decision problem has:
    - srank ≥ 1 (at least one relevant coordinate)
    - 2 ≤ numOptClasses ≤ 2^srank (at least 2 classes, at most 2^srank)

    The lower bound 2 comes from: 1 DOF with 2 binary values gives 2 patterns.
    This is the "first positive integer after 0" principle:
    0 DOF = constant = no distinguishability (false)
    1 DOF = 2 patterns = minimum distinguishability (first true) -/
theorem nontrivial_bounds_binary [DecidableEq (Set A)]
    (dp : DecisionProblem A (Fin n → Bool))
    (hnontriv : dp.isNontrivial) :
    1 ≤ dp.srank ∧ 2 ≤ dp.numOptClasses ∧ dp.numOptClasses ≤ 2 ^ dp.srank := by
  have hinj : ∀ s s' : Fin n → Bool,
      (∀ i : Fin n, CoordinateSpace.proj s i = CoordinateSpace.proj s' i) → s = s' := by
    intro s s' h; funext i; exact h i
  refine ⟨?_, ?_, ?_⟩
  · exact nontrivial_implies_srank_pos dp hnontriv hinj
  · unfold DecisionProblem.isNontrivial at hnontriv; exact hnontriv
  · exact numOptClasses_le_pow_srank_binary dp



/-- Entropy-Rank Inequality for binary coordinate spaces (S = Fin n → Bool).
    quotientEntropy = log₂(numOptClasses) ≤ log₂(2^srank) = srank

    This is the main information-theoretic result: the decision entropy
    is bounded by the structural rank. -/
theorem quotientEntropy_le_srank_binary [DecidableEq (Set A)]
    (dp : DecisionProblem A (Fin n → Bool)) :
    dp.quotientEntropy ≤ (dp.srank : ℝ) := by
  have hb := numOptClasses_le_pow_srank_binary dp
  have hpos : 0 < dp.numOptClasses := dp.numOptClasses_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold DecisionProblem.quotientEntropy
  rw [div_le_iff₀ hlog2, ← Real.log_pow]
  have hb' : (dp.numOptClasses : ℝ) ≤ 2 ^ dp.srank := by exact_mod_cast hb
  exact Real.log_le_log (by positivity) hb'

end DecisionQuotient
