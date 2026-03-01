/-
  Paper 4: Decision-Relevant Uncertainty

  Tractability/Dimensional.lean - Orbit Type Theory for Dimensional State Spaces

  This file formalizes the orbit type characterization of coordinate-permutation
  symmetry in dimensional state spaces (d-tuples over a finite alphabet).

  ## Key Theorems

  1. **orbitType_eq_iff**: Two states have the same orbit type (value histogram)
     iff they lie in the same permutation orbit. Proved via fiber bundle
     equivalences (Equiv.sigmaCongrRight).

  2. **symmetric_utility_opt_constant_on_orbitType**: Under symmetric utility,
     optimal actions depend only on orbit type. This justifies reducing the
     effective state space from k^d to (d+k-1 choose k-1) equivalence classes.

  ## Dependencies
  - DecisionQuotient.Finite (decision problem interface)
  - DecisionQuotient.Sufficiency (core sufficiency definition)
-/

import DecisionQuotient.Finite
import DecisionQuotient.Sufficiency
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Tactic

namespace DecisionQuotient

open Classical

variable {A S : Type*} [DecidableEq A] [DecidableEq S]

/-! ## Dimensional State Space Structure -/

/-- A dimensional state space where states are d-tuples over a finite alphabet -/
@[ext]
structure DimensionalStateSpace (k d : ℕ) where
  /-- States are functions from coordinates to values -/
  state : Fin d → Fin k
  deriving DecidableEq

/-- Equivalence between DimensionalStateSpace and function space -/
def DimensionalStateSpace.equiv (k d : ℕ) : DimensionalStateSpace k d ≃ (Fin d → Fin k) where
  toFun := DimensionalStateSpace.state
  invFun := DimensionalStateSpace.mk
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance {k d : ℕ} : Fintype (DimensionalStateSpace k d) :=
  Fintype.ofEquiv _ (DimensionalStateSpace.equiv k d).symm

instance {k d : ℕ} : CoeFun (DimensionalStateSpace k d) (fun _ => Fin d → Fin k) where
  coe := DimensionalStateSpace.state

/-- Coordinate projection for dimensional state space -/
def DimensionalStateSpace.project (k d : ℕ) (I : Finset (Fin d))
    (s : DimensionalStateSpace k d) : (i : {x : Fin d // x ∈ I}) → Fin k :=
  fun i => s.state i

/-- Two states agree on a coordinate set -/
def DimensionalStateSpace.agreeOn (k d : ℕ) (I : Finset (Fin d))
    (s s' : DimensionalStateSpace k d) : Prop :=
  ∀ i ∈ I, s.state i = s'.state i

/-- CoordinateSpace instance for DimensionalStateSpace -/
instance DimensionalStateSpace.coordinateSpace {k d : ℕ} :
    CoordinateSpace (DimensionalStateSpace k d) d where
  Coord := fun _ => Fin k
  proj := fun s i => s.state i

/-- Decidability of agreeOn for DimensionalStateSpace -/
instance DimensionalStateSpace.decidableAgreeOn {k d : ℕ}
  (s s' : DimensionalStateSpace k d) (I : Finset (Fin d)) :
  Decidable (DimensionalStateSpace.agreeOn (k := k) (d := d) I s s') :=
  by
    have : DecidablePred (fun i : Fin d => i ∈ I → s.state i = s'.state i) :=
      fun i => inferInstance
    exact Fintype.decidableForallFintype

/-- Cardinality of dimensional state space -/
theorem DimensionalStateSpace.card (k d : ℕ) :
    Fintype.card (DimensionalStateSpace k d) = k ^ d := by
  rw [Fintype.card_congr (DimensionalStateSpace.equiv k d)]
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-! ## Symmetry Reduction -/

/-- A permutation on coordinates -/
abbrev CoordinatePermutation (d : ℕ) := Equiv.Perm (Fin d)

/-- Apply a permutation to a state -/
def DimensionalStateSpace.permute {k d : ℕ}
    (σ : CoordinatePermutation d) (s : DimensionalStateSpace k d) : DimensionalStateSpace k d where
  state := fun i => s.state (σ.symm i)

/-- A utility is symmetric if permuting coordinates doesn't change it -/
def SymmetricUtility {A : Type*} {k d : ℕ}
    (utility : A → DimensionalStateSpace k d → ℤ) : Prop :=
  ∀ (σ : CoordinatePermutation d) a s, utility a s = utility a (s.permute σ)

/-- The orbit of a state under coordinate permutations -/
def DimensionalStateSpace.orbit {k d : ℕ} (s : DimensionalStateSpace k d) :
    Set (DimensionalStateSpace k d) :=
  {s' | ∃ σ : CoordinatePermutation d, s' = s.permute σ}

/-- Orbit type: the multiset of coordinate values (ignoring order) -/
def DimensionalStateSpace.orbitType {k d : ℕ} (s : DimensionalStateSpace k d) :
    Finset (Fin k × ℕ) := by
  -- Count how many times each value appears
  exact Finset.image (fun v : Fin k => (v, Finset.card (Finset.filter (fun i => s.state i = v) Finset.univ))) Finset.univ

/-- Multiset representation of a state as a symmetric tuple of length `d`. -/
noncomputable def DimensionalStateSpace.toSym {k d : ℕ}
    (s : DimensionalStateSpace k d) : Sym (Fin k) d :=
  (List.Vector.ofFn s.state : List.Vector (Fin k) d)

/-- Coordinate permutations preserve the multiset representation. -/
theorem DimensionalStateSpace.toSym_permute {k d : ℕ}
    (s : DimensionalStateSpace k d) (σ : CoordinatePermutation d) :
    (s.permute σ).toSym = s.toSym := by
  apply Sym.ext
  change (((List.Vector.ofFn (fun i : Fin d => s.state (σ.symm i)) : List.Vector (Fin k) d).toList : Multiset (Fin k))
      = ((List.Vector.ofFn s.state : List.Vector (Fin k) d).toList : Multiset (Fin k)))
  refine Quot.sound ?_
  simpa [List.Vector.toList_ofFn, Function.comp] using
    (Equiv.Perm.ofFn_comp_perm (σ := σ.symm) (f := s.state))

/-- Permuting coordinates preserves the orbit type (value histogram) -/
theorem orbitType_permute {k d : ℕ} (s : DimensionalStateSpace k d)
    (σ : CoordinatePermutation d) :
    (s.permute σ).orbitType = s.orbitType := by
  unfold DimensionalStateSpace.orbitType DimensionalStateSpace.permute
  -- For each value `v`, the two fibers have the same cardinality because `σ` is a bijection on indices.
  have hcard : ∀ v : Fin k,
      (Finset.filter (fun i => s.state (σ.symm i) = v) Finset.univ).card =
      (Finset.filter (fun i => s.state i = v) Finset.univ).card := by
    intro v
    have hfilter : Finset.filter (fun i => s.state (σ.symm i) = v) Finset.univ =
      Finset.image σ (Finset.filter (fun i => s.state i = v) Finset.univ) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hj
        exact ⟨σ.symm j, hj, σ.apply_symm_apply j⟩
      · intro ⟨i, hi, heq⟩
        simp only [← heq, Equiv.symm_apply_apply]
        exact hi
    rw [hfilter]
    exact Finset.card_image_of_injective _ σ.injective
  apply Finset.image_congr
  intro v _
  simp only []
  rw [hcard]

/-- Fiber bundle: pair of value and index with that value -/
def FiberSigma {k d : ℕ} (s : DimensionalStateSpace k d) :=
  Σ v : Fin k, { i : Fin d // s.state i = v }

/-- Equivalence between Fin d and the fiber bundle -/
def toFiberSigma {k d : ℕ} (s : DimensionalStateSpace k d) : Fin d ≃ FiberSigma s where
  toFun i := ⟨s.state i, ⟨i, rfl⟩⟩
  invFun := fun ⟨_, ⟨i, _⟩⟩ => i
  left_inv := fun _ => rfl
  right_inv := fun ⟨v, ⟨i, hi⟩⟩ => by cases hi; rfl

/-- Helper: Fintype.card of a fiber equals Finset.card of the filter -/
private theorem fiber_card_eq_filter {k d : ℕ} (s : DimensionalStateSpace k d) (v : Fin k) :
    Fintype.card {i : Fin d // s.state i = v} =
    (Finset.filter (fun i => s.state i = v) Finset.univ).card := by
  classical
  rw [Fintype.card_subtype (fun i => s.state i = v)]

/-- Equivalence between two fiber bundles with same fiber cardinalities -/
noncomputable def fiberSigmaEquiv {k d : ℕ} (s s' : DimensionalStateSpace k d)
    (hcard : ∀ v : Fin k,
        (Finset.filter (fun i => s.state i = v) Finset.univ).card =
        (Finset.filter (fun i => s'.state i = v) Finset.univ).card) :
    FiberSigma s ≃ FiberSigma s' :=
  Equiv.sigmaCongrRight (fun v => Fintype.equivOfCardEq (by
    rw [fiber_card_eq_filter s v, fiber_card_eq_filter s' v]
    exact hcard v))

/-- Two states have the same orbit type iff they're in the same orbit -/
theorem orbitType_eq_iff {k d : ℕ} (s s' : DimensionalStateSpace k d) :
    s.orbitType = s'.orbitType ↔ ∃ σ : CoordinatePermutation d, s' = s.permute σ := by
  constructor
  · intro h
    classical
    -- Extract cardinality equality from orbit type equality
    have hcard : ∀ v : Fin k,
        (Finset.filter (fun i => s.state i = v) Finset.univ).card =
        (Finset.filter (fun i => s'.state i = v) Finset.univ).card := by
      intro v
      -- (v, count_v) ∈ s.orbitType
      have hmem : (v, (Finset.filter (fun i => s.state i = v) Finset.univ).card) ∈ s.orbitType := by
        unfold DimensionalStateSpace.orbitType
        exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
      -- By h, this is also in s'.orbitType
      rw [h] at hmem
      unfold DimensionalStateSpace.orbitType at hmem
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hmem
      obtain ⟨v', heq⟩ := hmem
      -- heq : (v', count_v') = (v, count_v)
      have hv : v' = v := (Prod.ext_iff.mp heq).1
      have hc : (Finset.filter (fun i => s'.state i = v') Finset.univ).card =
                (Finset.filter (fun i => s.state i = v) Finset.univ).card :=
        (Prod.ext_iff.mp heq).2
      rw [hv] at hc
      exact hc.symm
    -- Build the permutation via fiber bundle equivalence
    let sigmaEquiv : FiberSigma s ≃ FiberSigma s' := fiberSigmaEquiv s s' hcard
    let σ : CoordinatePermutation d :=
      (toFiberSigma s).trans (sigmaEquiv.trans (toFiberSigma s').symm)
    use σ
    -- Show s' = s.permute σ by showing s'.state i = s.state (σ.symm i) for all i
    have hval : ∀ j, s'.state (σ j) = s.state j := by
      intro j
      -- σ j = (toFiberSigma s').symm (sigmaEquiv (toFiberSigma s j))
      -- The key facts:
      -- 1. sigmaCongrRight preserves the first component (the value)
      -- 2. The fiber element's property gives us the state value
      have h_fst : (sigmaEquiv (toFiberSigma s j)).1 = s.state j := rfl
      have h_prop : s'.state (sigmaEquiv (toFiberSigma s j)).2.val =
                    (sigmaEquiv (toFiberSigma s j)).1 :=
        (sigmaEquiv (toFiberSigma s j)).2.property
      have h_sigma : σ j = (sigmaEquiv (toFiberSigma s j)).2.val := rfl
      rw [h_sigma, h_prop, h_fst]
    -- Apply hval to show the ext goal
    apply DimensionalStateSpace.ext
    funext i
    -- Goal: s'.state i = (s.permute σ).state i = s.state (σ.symm i)
    simp only [DimensionalStateSpace.permute]
    have := hval (σ.symm i)
    rwa [Equiv.apply_symm_apply] at this
  · intro ⟨σ, hσ⟩
    rw [hσ]
    exact (orbitType_permute s σ).symm

/-! ## Symmetric Utility Invariance -/

/-- Key structural lemma: under symmetric utility, optimal actions are
    invariant under coordinate permutations. Since utility a s = utility a (s.permute σ)
    for all actions a, the argmax set is the same. -/
theorem symmetric_utility_opt_constant_on_permute
    {k d : ℕ} {A : Type*} [DecidableEq A]
    (dp : FiniteDecisionProblem (A := A) (S := DimensionalStateSpace k d))
    (hsym : SymmetricUtility dp.utility)
    (σ : CoordinatePermutation d) (s : DimensionalStateSpace k d) :
    dp.optimalActions s = dp.optimalActions (s.permute σ) := by
  unfold FiniteDecisionProblem.optimalActions
  ext a
  simp only [Finset.mem_filter]
  constructor
  · intro ⟨ha, hopt⟩
    exact ⟨ha, fun a' ha' => by rw [← hsym σ a' s, ← hsym σ a s]; exact hopt a' ha'⟩
  · intro ⟨ha, hopt⟩
    exact ⟨ha, fun a' ha' => by rw [hsym σ a' s, hsym σ a s]; exact hopt a' ha'⟩

/-- Corollary: states in the same orbit have the same optimal actions. -/
theorem symmetric_utility_opt_constant_on_orbit
    {k d : ℕ} {A : Type*} [DecidableEq A]
    (dp : FiniteDecisionProblem (A := A) (S := DimensionalStateSpace k d))
    (hsym : SymmetricUtility dp.utility)
    (s s' : DimensionalStateSpace k d)
    (horbit : ∃ σ : CoordinatePermutation d, s' = s.permute σ) :
    dp.optimalActions s = dp.optimalActions s' := by
  obtain ⟨σ, hσ⟩ := horbit
  rw [hσ]
  exact symmetric_utility_opt_constant_on_permute dp hsym σ s

/-- Under symmetric utility, states with the same orbit type have the same
    optimal actions. Combines orbitType_eq_iff with opt_constant_on_orbit. -/
theorem symmetric_utility_opt_constant_on_orbitType
    {k d : ℕ} {A : Type*} [DecidableEq A]
    (dp : FiniteDecisionProblem (A := A) (S := DimensionalStateSpace k d))
    (hsym : SymmetricUtility dp.utility)
    (s s' : DimensionalStateSpace k d)
    (htype : s.orbitType = s'.orbitType) :
    dp.optimalActions s = dp.optimalActions s' := by
  have horbit := (orbitType_eq_iff s s').mp htype
  exact symmetric_utility_opt_constant_on_orbit dp hsym s s' horbit

/-! ## Reduction to Standard Results -/

/-- The orbit-type setoid: states are equivalent iff they induce the same
    multiset of coordinate values (symmetric tuple representation). -/
def orbitTypeSetoid (k d : ℕ) : Setoid (DimensionalStateSpace k d) where
  r := fun s s' => s.toSym = s'.toSym
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- The quotient space of orbit types. -/
def OrbitTypeQuotient (k d : ℕ) := Quotient (orbitTypeSetoid k d)

/-- OrbitTypeQuotient is finite (inherits from DimensionalStateSpace). -/
noncomputable instance {k d : ℕ} : Fintype (OrbitTypeQuotient k d) :=
  Quotient.fintype (orbitTypeSetoid k d)

/-- Canonical map from orbit-type quotient classes to symmetric tuples. -/
noncomputable def orbitTypeQuotientToSym (k d : ℕ) :
    OrbitTypeQuotient k d → Sym (Fin k) d :=
  Quotient.lift (fun s : DimensionalStateSpace k d => s.toSym) (by
    intro s s' h
    simpa [orbitTypeSetoid] using h)

/-- The quotient-to-symmetric-tuple map is injective by construction. -/
theorem orbitTypeQuotientToSym_injective (k d : ℕ) :
    Function.Injective (orbitTypeQuotientToSym k d) := by
  intro q q' hq
  revert hq
  refine Quotient.inductionOn₂ q q' ?_
  intro s s' hs
  exact Quotient.sound hs

/-- The number of distinct orbit types is bounded by the stars-and-bars formula.

    We inject orbit classes into `Sym (Fin k) d` and apply
    `Sym.card_sym_eq_choose` plus `Nat.choose_symm`. -/
theorem orbitType_count_bound (k d : ℕ) (hk : 0 < k) :
    Fintype.card (OrbitTypeQuotient k d) ≤ Nat.choose (d + k - 1) (k - 1) := by
  have hInj := orbitTypeQuotientToSym_injective k d
  have hCard :
      Fintype.card (OrbitTypeQuotient k d) ≤ Fintype.card (Sym (Fin k) d) :=
    Fintype.card_le_of_injective (orbitTypeQuotientToSym k d) hInj
  have hSym :
      Fintype.card (Sym (Fin k) d) = Nat.choose (d + k - 1) d := by
    simpa [Nat.add_comm, Fintype.card_fin] using (Sym.card_sym_eq_choose (α := Fin k) d)
  have hChoose :
      Nat.choose (d + k - 1) d = Nat.choose (d + k - 1) (k - 1) := by
    have hle : d ≤ d + k - 1 := by omega
    have hsub : d + k - 1 - d = k - 1 := by omega
    rw [← Nat.choose_symm hle, hsub]
  calc
    Fintype.card (OrbitTypeQuotient k d) ≤ Fintype.card (Sym (Fin k) d) := hCard
    _ = Nat.choose (d + k - 1) d := hSym
    _ = Nat.choose (d + k - 1) (k - 1) := hChoose

/-- **Key Reduction Lemma**: Under symmetric utility, if two states have the
    same orbit type, then optimalActions is identical.

    This is the core of the reduction: we only need to check across orbit types,
    not within them. -/
theorem symmetric_optimalActions_orbit_invariant
    {A : Type*} [DecidableEq A] {k d : ℕ}
    (dp : FiniteDecisionProblem (A := A) (S := DimensionalStateSpace k d))
    (hsym : SymmetricUtility dp.utility)
    (s s' : DimensionalStateSpace k d)
    (htype : s.orbitType = s'.orbitType) :
    dp.optimalActions s = dp.optimalActions s' :=
  symmetric_utility_opt_constant_on_orbitType dp hsym s s' htype

/-- **Reduction Theorem**: Under symmetric utility, sufficiency checking
    reduces to checking pairs with DIFFERENT orbit types.

    Pairs with the same orbit type automatically have equal optimalActions
    (by `symmetric_optimalActions_orbit_invariant`), so we only need to verify
    that I-agreement across different orbit types preserves optimalActions.

    This is the paper-specific reduction that enables tractability:
    we pick one representative per orbit type and check O(|OrbitTypeQuotient|²) pairs
    instead of O(|S|²) pairs. -/
theorem sufficiency_reduces_to_cross_orbit_check
    {A : Type*} [DecidableEq A] {k d : ℕ}
    (dp : FiniteDecisionProblem (A := A) (S := DimensionalStateSpace k d))
    (hsym : SymmetricUtility dp.utility)
    (I : Finset (Fin d))
    -- Hypothesis: I-agreement across different orbit types preserves optimalActions
    (hcross : ∀ s ∈ dp.states, ∀ s' ∈ dp.states,
      s.orbitType ≠ s'.orbitType →
      DimensionalStateSpace.agreeOn k d I s s' →
      dp.optimalActions s = dp.optimalActions s') :
    -- Conclusion: I is sufficient on the full state space
    ∀ s ∈ dp.states, ∀ s' ∈ dp.states,
      DimensionalStateSpace.agreeOn k d I s s' →
      dp.optimalActions s = dp.optimalActions s' := by
  intro s hs s' hs' hagree
  by_cases htype : s.orbitType = s'.orbitType
  · -- Same orbit type: optimalActions is automatically equal
    exact symmetric_optimalActions_orbit_invariant dp hsym s s' htype
  · -- Different orbit types: use the cross-orbit hypothesis
    exact hcross s hs s' hs' htype hagree

/-- **Complexity Implication**: The number of cross-orbit checks is bounded.

    Since `sufficiency_reduces_to_cross_orbit_check` reduces sufficiency checking
    to cross-orbit pairs, and the number of orbit types is bounded by
    `orbitType_count_bound`, the total number of checks is O(|OrbitTypeQuotient|²).

    For each orbit type pair (τ₁, τ₂), we check if any s ∈ τ₁ and s' ∈ τ₂ agree on I,
    and if so, verify that their optimalActions match. Since optimalActions is
    constant on orbit types, we can use any representative.

    This gives polynomial complexity in d for fixed k. -/
theorem symmetric_sufficiency_complexity_bound {k d : ℕ} (hk : 0 < k) :
    -- The number of orbit type pairs to check is polynomial
    Fintype.card (OrbitTypeQuotient k d) * Fintype.card (OrbitTypeQuotient k d)
      ≤ Nat.choose (d + k - 1) (k - 1) * Nat.choose (d + k - 1) (k - 1) := by
  have h := orbitType_count_bound k d hk
  exact Nat.mul_le_mul h h

/-- **Tractability Statement**: Under symmetric utility with bounded k,
    SUFFICIENCY-CHECK is solvable in time polynomial in d.

    Proof structure (citing standard results):
    1. By `symmetric_sufficiency_reduces_to_orbitTypes`, we only check orbit type reps
    2. By `orbitType_count_bound`, there are O(d^(k-1)) orbit types
    3. By standard enumeration, checking each pair is O(|A|)
    4. Total: O(d^(2k-2) · |A|) which is polynomial for fixed k

    This is stated as a proposition backed by the reduction + standard algorithms,
    not a formal complexity proof. -/
theorem symmetric_tractability_statement {A : Type*} [DecidableEq A] {k d : ℕ}
    (dp : FiniteDecisionProblem (A := A) (S := DimensionalStateSpace k d))
    (hsym : SymmetricUtility dp.utility) (hk : 0 < k) :
    -- The effective state space has polynomial size
    Fintype.card (OrbitTypeQuotient k d) ≤ Nat.choose (d + k - 1) (k - 1) := by
  -- hsym justifies that we only need to check orbit type representatives
  -- (see symmetric_optimalActions_orbit_invariant)
  have _ := hsym  -- Mark as used for documentation
  exact orbitType_count_bound k d hk

end DecisionQuotient
