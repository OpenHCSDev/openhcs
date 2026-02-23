/-
  Paper 4: Decision-Relevant Uncertainty

  Sufficiency.lean - Coordinate Sufficiency and Feature Selection

  When S = X₁ × ... × Xₙ (product of coordinate spaces), we can ask:
  Which coordinates are sufficient to determine the optimal decision?

  Key definitions:
  - Sufficient set I: knowing coordinates in I determines Opt
  - Minimal sufficient set: smallest such I
  - Relevant coordinate: a coordinate that can change Opt
-/

import DecisionQuotient.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Filter.Basic

namespace DecisionQuotient

/-! ## Product State Spaces -/

/-- A coordinate projection from a product state space.
    For S = X₁ × ... × Xₙ, proj I s returns the tuple (sᵢ)_{i ∈ I} -/
class CoordinateSpace (S : Type*) (n : ℕ) where
  /-- The i-th coordinate type -/
  Coord : Fin n → Type*
  /-- Project to coordinate i -/
  proj : S → (i : Fin n) → Coord i

/-- A coordinate space with the ability to construct hybrid states.
    This is the natural structure for product spaces S = X₁ × ... × Xₙ -/
class ProductSpace (S : Type*) (n : ℕ) extends CoordinateSpace S n where
  /-- Replace coordinate i in state s with value from state s' -/
  replace : S → (i : Fin n) → S → S
  /-- Replace preserves the replaced coordinate -/
  replace_proj_eq : ∀ s s' i, proj (replace s i s') i = proj s' i
  /-- Replace preserves other coordinates -/
  replace_proj_ne : ∀ s s' i j, j ≠ i → proj (replace s i s') j = proj s j

/-- Two states agree on a set of coordinates -/
def agreeOn {S : Type*} {n : ℕ} [CoordinateSpace S n]
    (s s' : S) (I : Finset (Fin n)) : Prop :=
  ∀ i ∈ I, CoordinateSpace.proj s i = CoordinateSpace.proj s' i

variable {A S : Type*} {n : ℕ} [CoordinateSpace S n]

/-! ## Sufficient Coordinate Sets -/

/-- A coordinate set I is sufficient for a decision problem if:
    Knowing the coordinates in I determines the optimal set.

    Formally: s_I = s'_I ⟹ Opt(s) = Opt(s') -/
def DecisionProblem.isSufficient (dp : DecisionProblem A S) (I : Finset (Fin n)) : Prop :=
  ∀ s s' : S, agreeOn s s' I → dp.Opt s = dp.Opt s'

/-- A deterministic selector extracts one action from an optimal-action set. -/
def DecisionProblem.SelectedAction (dp : DecisionProblem A S) (σ : Set A → A) (s : S) : A :=
  σ (dp.Opt s)

/-- Sufficiency relative to a fixed deterministic selector. -/
def DecisionProblem.isSelectorSufficient (dp : DecisionProblem A S)
    (σ : Set A → A) (I : Finset (Fin n)) : Prop :=
  ∀ s s' : S, agreeOn s s' I → dp.SelectedAction σ s = dp.SelectedAction σ s'

/-- Full optimal-set sufficiency implies selector-level sufficiency
    for every deterministic selector. -/
theorem DecisionProblem.sufficient_implies_selectorSufficient
    (dp : DecisionProblem A S) (I : Finset (Fin n))
    (hI : dp.isSufficient I) (σ : Set A → A) :
    dp.isSelectorSufficient σ I := by
  intro s s' hagree
  unfold DecisionProblem.SelectedAction
  exact congrArg σ (hI s s' hagree)

/-- The empty set is sufficient iff Opt is constant -/
theorem DecisionProblem.emptySet_sufficient_iff_constant (dp : DecisionProblem A S) :
    dp.isSufficient (∅ : Finset (Fin n)) ↔ ∀ s s' : S, dp.Opt s = dp.Opt s' := by
  constructor
  · intro h s s'
    apply h
    intro i hi
    exact (by simpa using hi)
  · intro h s s' _
    exact h s s'

/-- Generic non-sufficiency characterization:
    a set is not sufficient iff there exists an explicit counterexample pair
    that agrees on the queried coordinates but has different optimal sets. -/
theorem DecisionProblem.not_sufficient_iff_exists_counterexample
    (dp : DecisionProblem A S) (I : Finset (Fin n)) :
    ¬ dp.isSufficient I ↔
      ∃ s s' : S, agreeOn s s' I ∧ dp.Opt s ≠ dp.Opt s' := by
  unfold DecisionProblem.isSufficient
  push_neg
  constructor
  · intro h
    rcases h with ⟨s, hs⟩
    rcases hs with ⟨s', hs'⟩
    exact ⟨s, s', hs'.1, hs'.2⟩
  · intro h
    rcases h with ⟨s, s', hagree, hneq⟩
    exact ⟨s, s', hagree, hneq⟩

/-- Empty-set non-sufficiency is exactly non-constancy of the decision boundary:
    there exist two states with different optimal sets. -/
theorem DecisionProblem.emptySet_not_sufficient_iff_exists_opt_difference
    (dp : DecisionProblem A S) :
    ¬ dp.isSufficient (∅ : Finset (Fin n)) ↔
      ∃ s s' : S, dp.Opt s ≠ dp.Opt s' := by
  constructor
  · intro hNot
    rcases (DecisionProblem.not_sufficient_iff_exists_counterexample
      (dp := dp) (I := (∅ : Finset (Fin n)))).1 hNot with ⟨s, s', _hAgree, hNeq⟩
    exact ⟨s, s', hNeq⟩
  · intro hDiff
    rcases hDiff with ⟨s, s', hNeq⟩
    exact (DecisionProblem.not_sufficient_iff_exists_counterexample
      (dp := dp) (I := (∅ : Finset (Fin n)))).2 ⟨s, s', (by intro i hi; simpa using hi), hNeq⟩

/-! ## Minimal Sufficient Sets -/

/-- A sufficient set I is minimal if no proper subset is sufficient -/
def DecisionProblem.isMinimalSufficient (dp : DecisionProblem A S) (I : Finset (Fin n)) : Prop :=
  dp.isSufficient I ∧ ∀ J : Finset (Fin n), J ⊂ I → ¬dp.isSufficient J

/-! ## Relevant Coordinates -/

/-- A coordinate i is relevant if there exist states differing only in i
    with different optimal sets -/
def DecisionProblem.isRelevant (dp : DecisionProblem A S) (i : Fin n) : Prop :=
  ∃ s s' : S, (∀ j : Fin n, j ≠ i → CoordinateSpace.proj s j = CoordinateSpace.proj s' j)
    ∧ dp.Opt s ≠ dp.Opt s'

/-- A coordinate is irrelevant if it never affects the optimal set -/
def DecisionProblem.isIrrelevant (dp : DecisionProblem A S) (i : Fin n) : Prop :=
  ∀ s s' : S, (∀ j : Fin n, j ≠ i → CoordinateSpace.proj s j = CoordinateSpace.proj s' j)
    → dp.Opt s = dp.Opt s'

/-- Irrelevant ↔ ¬Relevant -/
theorem DecisionProblem.irrelevant_iff_not_relevant (dp : DecisionProblem A S) (i : Fin n) :
    dp.isIrrelevant i ↔ ¬dp.isRelevant i := by
  unfold DecisionProblem.isIrrelevant DecisionProblem.isRelevant
  push_neg
  rfl

/-! ## Key Theorems -/

/-- Any sufficient set must contain all relevant coordinates -/
theorem DecisionProblem.sufficient_contains_relevant (dp : DecisionProblem A S)
    (I : Finset (Fin n)) (hI : dp.isSufficient I) (i : Fin n) (hi : dp.isRelevant i) :
    i ∈ I := by
  by_contra h_not_in
  obtain ⟨s, s', hdiff, hopt⟩ := hi
  have hagree : agreeOn s s' I := fun j hj => hdiff j (fun heq => h_not_in (heq ▸ hj))
  exact hopt (hI s s' hagree)

/-- Monotonicity: supersets of sufficient sets are sufficient -/
theorem DecisionProblem.sufficient_superset (dp : DecisionProblem A S)
    (I J : Finset (Fin n)) (hI : dp.isSufficient I) (hIJ : I ⊆ J) :
    dp.isSufficient J := by
  intro s s' hagreeJ
  apply hI
  exact fun i hi => hagreeJ i (hIJ hi)

/-! ## Lattice Structure of Sufficient Sets -/

/-- The set of all sufficient coordinate sets -/
def DecisionProblem.sufficientSets (dp : DecisionProblem A S) : Set (Finset (Fin n)) :=
  { I | dp.isSufficient I }

/-- The full coordinate set is always sufficient when proj is injective -/
theorem DecisionProblem.univ_sufficient_of_injective (dp : DecisionProblem A S)
    (hinj : ∀ s s' : S, (∀ i : Fin n, CoordinateSpace.proj s i = CoordinateSpace.proj s' i) → s = s') :
    dp.isSufficient (Finset.univ : Finset (Fin n)) := by
  intro s s' hagree
  have heq : s = s' := hinj s s' (fun i => hagree i (Finset.mem_univ i))
  rw [heq]

/-- Sufficient sets form an upward-closed set (filter base) -/
theorem DecisionProblem.sufficientSets_upward_closed (dp : DecisionProblem A S)
    (I J : Finset (Fin n)) (hI : I ∈ dp.sufficientSets) (hIJ : I ⊆ J) :
    J ∈ dp.sufficientSets :=
  dp.sufficient_superset I J hI hIJ

/-! ## The Relevant Set -/

/-- The set of all relevant coordinates -/
def DecisionProblem.relevantSet (dp : DecisionProblem A S) : Set (Fin n) :=
  { i | dp.isRelevant i }

/-- If i is not in the sufficient set I, then erasing i changes nothing -/
theorem DecisionProblem.erase_of_not_mem [DecidableEq (Fin n)]
    (dp : DecisionProblem A S) (I : Finset (Fin n)) (i : Fin n)
    (hI : dp.isSufficient I) (hi : i ∉ I) :
    dp.isSufficient (I.erase i) := by
  have heq : I.erase i = I := by
    simpa [hi]
  rw [heq]
  exact hI

/-- Relevant coordinates are necessary: they must be in any sufficient set -/
theorem DecisionProblem.relevant_necessary
    (dp : DecisionProblem A S) (I : Finset (Fin n))
    (hI : dp.isSufficient I) (i : Fin n) (hrel : dp.isRelevant i) :
    i ∈ I :=
  dp.sufficient_contains_relevant I hI i hrel

/-! ## State Construction Theorems (using ProductSpace) -/

variable {S : Type*} {n : ℕ} [ProductSpace S n]

/-- In a ProductSpace, if coordinate i is irrelevant, then I \ {i} is sufficient
    whenever I is sufficient. This is the key structural theorem. -/
theorem DecisionProblem.sufficient_erase_irrelevant' [DecidableEq (Fin n)]
    {A : Type*} (dp : DecisionProblem A S) (I : Finset (Fin n)) (i : Fin n)
    (hI : dp.isSufficient I) (hirr : dp.isIrrelevant i) :
    dp.isSufficient (I.erase i) := by
  intro s s' hagree
  -- Construct hybrid state: s with coordinate i replaced by s'_i
  let hybrid := ProductSpace.replace s i s'
  -- Step 1: s and hybrid agree on all of I (they agree on I \ {i} from hagree,
  -- and on i because replace only changes i)
  have h_s_hybrid : dp.Opt s = dp.Opt hybrid := by
    -- s and hybrid differ only in coordinate i
    apply hirr s hybrid
    intro j hj
    -- For j ≠ i, hybrid has the same coordinate as s
    exact (ProductSpace.replace_proj_ne s s' i j hj).symm
  -- Step 2: hybrid and s' agree on all of I
  have h_hybrid_s' : dp.Opt hybrid = dp.Opt s' := by
    apply hI hybrid s'
    intro j hj
    by_cases hji : j = i
    · -- j = i: hybrid has s'_i by construction
      rw [hji]
      exact ProductSpace.replace_proj_eq s s' i
    · -- j ≠ i and j ∈ I, so j ∈ I.erase i
      have hj_erase : j ∈ I.erase i := Finset.mem_erase.mpr ⟨hji, hj⟩
      -- hybrid_j = s_j (by replace_proj_ne) = s'_j (by hagree)
      rw [ProductSpace.replace_proj_ne s s' i j hji]
      exact hagree j hj_erase
  -- Combine: Opt s = Opt hybrid = Opt s'
  exact h_s_hybrid.trans h_hybrid_s'

/-- Corollary: In a ProductSpace, a minimal sufficient set contains exactly
    the relevant coordinates -/
theorem DecisionProblem.minimalSufficient_iff_relevant [DecidableEq (Fin n)]
    {A : Type*} (dp : DecisionProblem A S) (I : Finset (Fin n))
    (hmin : dp.isMinimalSufficient I) :
    ∀ i : Fin n, i ∈ I ↔ dp.isRelevant i := by
  intro i
  constructor
  · -- If i ∈ I, then i is relevant (by minimality)
    intro hi
    by_contra h_not_rel
    -- i is irrelevant
    have hirr : dp.isIrrelevant i := (dp.irrelevant_iff_not_relevant i).mpr h_not_rel
    -- So I.erase i is sufficient
    have hsuff : dp.isSufficient (I.erase i) := dp.sufficient_erase_irrelevant' I i hmin.1 hirr
    -- But I.erase i ⊂ I, contradicting minimality
    have hsub : I.erase i ⊂ I := Finset.erase_ssubset hi
    exact hmin.2 (I.erase i) hsub hsuff
  · -- If i is relevant, then i ∈ I (by sufficiency)
    exact dp.sufficient_contains_relevant I hmin.1 i

/-- The set of relevant coordinates is the unique minimal sufficient set
    (when it's finite and forms a sufficient set) -/
theorem DecisionProblem.relevantSet_is_minimal [DecidableEq (Fin n)]
    {A : Type*} (dp : DecisionProblem A S) (I : Finset (Fin n))
    (hmin : dp.isMinimalSufficient I) (J : Finset (Fin n))
    (hmin' : dp.isMinimalSufficient J) :
    I = J := by
  ext i
  rw [dp.minimalSufficient_iff_relevant I hmin i, dp.minimalSufficient_iff_relevant J hmin' i]

/-! ## Lattice Structure of Sufficient Sets -/

variable {A : Type*} {S : Type*} {n : ℕ} [CoordinateSpace S n]

/-- Sufficient sets are closed under supersets (upward closed) -/
theorem DecisionProblem.sufficientSets_upward
    (dp : DecisionProblem A S) (I J : Finset (Fin n))
    (hI : I ∈ dp.sufficientSets) (hIJ : I ⊆ J) :
    J ∈ dp.sufficientSets :=
  dp.sufficientSets_upward_closed I J hI hIJ

/-- A sufficient set contains all relevant coordinates -/
theorem DecisionProblem.sufficient_contains_all_relevant
    (dp : DecisionProblem A S) (I : Finset (Fin n))
    (hI : dp.isSufficient I) :
    ∀ i : Fin n, dp.isRelevant i → i ∈ I :=
  fun i hrel => dp.sufficient_contains_relevant I hI i hrel

end DecisionQuotient

/-! ## Principal Filter Structure (requires ProductSpace) -/

namespace DecisionQuotient

variable {A : Type*} {S : Type*} {n : ℕ} [ProductSpace S n] [DecidableEq (Fin n)]

/-- Sufficient sets form a principal filter when there's a minimal element -/
theorem DecisionProblem.sufficientSets_principal'
    (dp : DecisionProblem A S) (I : Finset (Fin n))
    (hmin : dp.isMinimalSufficient I) :
    dp.sufficientSets = { J | I ⊆ J } := by
  ext J
  constructor
  · -- If J is sufficient, then I ⊆ J
    intro hJ i hi
    -- i ∈ I means i is relevant (by minimalSufficient_iff_relevant)
    have hrel : dp.isRelevant i := (dp.minimalSufficient_iff_relevant I hmin i).mp hi
    -- relevant coordinates must be in any sufficient set
    exact dp.sufficient_contains_relevant J hJ i hrel
  · -- If I ⊆ J, then J is sufficient
    intro hIJ
    exact dp.sufficientSets_upward I J hmin.1 hIJ

/-- The minimal sufficient set contains exactly the relevant coordinates -/
theorem DecisionProblem.minimalSufficient_eq_relevant'
    (dp : DecisionProblem A S) (I : Finset (Fin n))
    (hmin : dp.isMinimalSufficient I) :
    ∀ i : Fin n, i ∈ I ↔ dp.isRelevant i :=
  dp.minimalSufficient_iff_relevant I hmin

/-- The minimal sufficient set has cardinality equal to the number of relevant coords in I -/
theorem DecisionProblem.minimalSufficient_all_relevant'
    (dp : DecisionProblem A S) (I : Finset (Fin n))
    (hmin : dp.isMinimalSufficient I) :
    ∀ i ∈ I, dp.isRelevant i := fun i hi =>
  (dp.minimalSufficient_iff_relevant I hmin i).mp hi

end DecisionQuotient
