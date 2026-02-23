/-
  Reduction_AllCoords.lean - Strengthened reduction: many-coordinate gadget

  Construct a decision problem with n coordinates so that if the input
  Boolean formula φ is not a tautology then every coordinate is relevant.

  This gives a mechanized witness that hard instances can force k* = Ω(n).
-/

import DecisionQuotient.Reduction
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith

namespace DecisionQuotient

variable {n : ℕ}

open ReductionAction ReductionState

/-- Utility for the many-coordinate gadget.  We make `accept` globally
    optimal iff every coordinate contributes `1` (i.e. no coordinate is
    falsifying). Otherwise `accept` and `reject` tie. -/
noncomputable def reductionUtilityMany (φ : Formula n) : ReductionAction → (Fin n → ReductionState n) → ℝ
  | accept, s => if ∀ j, reductionUtility φ accept (s j) = 1 then 1 else 0
  | reject, _ => 0

/-- The many-coordinate decision problem built from φ. States are vectors
    of the base reduction states (one component per coordinate). -/
noncomputable def reductionProblemMany (φ : Formula n) : DecisionProblem ReductionAction (Fin n → ReductionState n) where
  utility := reductionUtilityMany φ

/-- The product state space (vectors of `ReductionState n`) has n coordinates. -/
instance : CoordinateSpace (Fin n → ReductionState n) n where
  Coord := fun _ => ReductionState n
  proj := fun s i => s i

instance : ProductSpace (Fin n → ReductionState n) n where
  Coord := fun _ => ReductionState n
  proj := fun s i => s i
  replace := fun s i s' => Function.update s i (s' i)
  replace_proj_eq := by
    intros s s' i
    simp [Function.update]
  replace_proj_ne := by
    intros s s' i j hne
    dsimp [Function.update]
    by_cases h : j = i
    · contradiction
    · simp [h]

/-! ## Optimal-set lemmas for the many-coordinate gadget -/

theorem opt_reference_many (φ : Formula n) :
    (reductionProblemMany φ).Opt (fun _ => ReductionState.reference) = {accept} := by
  let s : Fin n → ReductionState n := fun _ => ReductionState.reference
  have cond : ∀ j, reductionUtility φ accept (s j) = 1 := by
    intro j
    dsimp [s]
    simp [reductionUtility]

  ext a
  simp only [DecisionProblem.Opt, DecisionProblem.isOptimal, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    cases a with
    | accept => rfl
    | reject =>
      exfalso
      -- If `reject` were optimal, we'd have `utility accept ≤ utility reject`, i.e. `1 ≤ 0`.
      have h1 := h accept
      have : (1 : ℝ) ≤ 0 := by
        simpa [reductionProblemMany, reductionUtilityMany, reductionUtility, cond] using h1
      linarith
  · intro h
    subst h
    intro a'
    cases a' with
    | accept => simp [reductionProblemMany, reductionUtilityMany, reductionUtility]
    | reject =>
      simp [reductionProblemMany, reductionUtilityMany, reductionUtility, cond]

theorem opt_falsifying_many (φ : Formula n) (k : Fin n) (a_assn : Assignment n)
    (hfalse : Formula.eval a_assn φ = false) :
    (reductionProblemMany φ).Opt
      (Function.update (fun _ => ReductionState.reference) k (ReductionState.assignment a_assn))
      = {accept, reject} := by
  let s : Fin n → ReductionState n :=
    Function.update (fun _ => ReductionState.reference) k (ReductionState.assignment a_assn)

  ext x
  simp only [DecisionProblem.Opt, DecisionProblem.isOptimal, Set.mem_setOf_eq,
             Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro _
    -- `x` is either `accept` or `reject`.
    cases x <;> simp

  · intro _hx
    -- The special coordinate `k` forces the global condition to fail, hence `utility accept = 0`.
    have hcoord : reductionUtility φ accept (s k) = 0 := by
      dsimp [s]
      simp [reductionUtility, hfalse]
    have hnotall : ¬ (∀ j, reductionUtility φ accept (s j) = 1) := by
      intro H
      have hk := H k
      -- `hk : reductionUtility φ accept (s k) = 1`, but `hcoord : ... = 0`.
      simp [hcoord] at hk

    -- Therefore every action's utility is ≤ `utility x`.
    intro a'
    cases x <;> cases a'
    · -- accept vs accept
      exact le_rfl
    · -- accept vs reject
      -- `hnotall` forces `utility accept = 0`, so `0 ≤ 0`.
      simp [reductionProblemMany, reductionUtilityMany, hnotall, s]
    · -- reject vs accept
      -- `hnotall` forces `utility accept = 0`, so `0 ≤ 0`.
      simp [reductionProblemMany, reductionUtilityMany, hnotall, s]
    · -- reject vs reject
      exact le_rfl

/-! ## Correctness: tautology ↔ emptiness sufficient (many-coordinates) -/

theorem opt_tautology_many (φ : Formula n) (htaut : φ.isTautology) :
    ∀ s : Fin n → ReductionState n, (reductionProblemMany φ).Opt s = {accept} := by
  intro s
  have hall : ∀ j, reductionUtility φ accept (s j) = 1 := by
    intro j
    cases hsj : s j with
    | reference =>
        simp [reductionUtility]
    | assignment a =>
        -- tautology gives eval a φ = true
        have : Formula.eval a φ = true := htaut a
        simp [reductionUtility, this]
  ext a
  simp only [DecisionProblem.Opt, DecisionProblem.isOptimal, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    cases a with
    | accept => rfl
    | reject =>
      exfalso
      have h1 := h accept
      have : (1 : ℝ) ≤ 0 := by
        -- Keep `reductionUtility` opaque so `hall` rewrites the global condition.
        simpa [reductionProblemMany, reductionUtilityMany, hall] using h1
      linarith
  · intro h
    subst h
    intro a'
    cases a' <;> simp [reductionProblemMany, reductionUtilityMany, hall]

theorem tautology_implies_sufficient_many (φ : Formula n) (htaut : φ.isTautology) :
    (reductionProblemMany φ).isSufficient (∅ : Finset (Fin n)) := by
  intro s s' _
  have hs  := opt_tautology_many φ htaut s
  have hs' := opt_tautology_many φ htaut s'
  simp [hs, hs']

theorem sufficient_implies_tautology_many (φ : Formula n) (hn : 0 < n)
    (hsuff : (reductionProblemMany φ).isSufficient (∅ : Finset (Fin n))) :
    φ.isTautology := by
  classical
  by_contra htaut

  -- Extract a falsifying assignment from ¬tautology
  have hnotall : ¬ ∀ a, Formula.eval a φ = true := by
    simpa [Formula.isTautology] using htaut
  rcases not_forall.mp hnotall with ⟨a0, ha0⟩
  cases hval : Formula.eval a0 φ with
  | true =>
      exact (ha0 hval).elim
  | false =>
      -- build the two witness states
      let s_ref : Fin n → ReductionState n := fun _ => ReductionState.reference
      let k : Fin n := ⟨0, hn⟩
      let s' : Fin n → ReductionState n :=
        Function.update s_ref k (ReductionState.assignment a0)

      have heq : (reductionProblemMany φ).Opt s_ref = (reductionProblemMany φ).Opt s' :=
        hsuff s_ref s' (by intro i hi; cases hi)

      have href : (reductionProblemMany φ).Opt s_ref = {accept} :=
        opt_reference_many (n := n) φ
      have hs' : (reductionProblemMany φ).Opt s' = {accept, reject} :=
        opt_falsifying_many (φ := φ) (k := k) (a_assn := a0) (hfalse := hval)

      have eq_sets : ({accept} : Set ReductionAction) = {accept, reject} := by
        simpa [href, hs'] using heq

      have H2 : reject ∉ ({accept} : Set ReductionAction) := by
        simp [Set.mem_singleton_iff]
      have hmem : reject ∈ ({accept} : Set ReductionAction) := by
        simp [eq_sets]
      exact H2 hmem

theorem tautology_iff_sufficient_many {n : ℕ} (φ : Formula n) (hn : 0 < n) :
  φ.isTautology ↔ (reductionProblemMany φ).isSufficient (∅ : Finset (Fin n)) :=
  ⟨tautology_implies_sufficient_many φ, sufficient_implies_tautology_many φ hn⟩

/-! ## All coordinates become relevant when φ is not a tautology -/

theorem all_coords_relevant_of_not_tautology (φ : Formula n) (h : ¬φ.isTautology) :
    ∀ i : Fin n, (reductionProblemMany φ).isRelevant i := by
  -- Pick a falsifying assignment and for each coordinate produce the witness states.
  classical
  -- extract a falsifying assignment from ¬tautology
  have hnot : ¬ ∀ a, Formula.eval a φ = true := by
    simpa [Formula.isTautology] using h
  rcases not_forall.mp hnot with ⟨a0, ha0⟩
  intro i
  -- s = all-reference, s' = s with coordinate i set to assignment a0
  let s : Fin n → ReductionState n := fun _ => ReductionState.reference
  let s' := Function.update s i (ReductionState.assignment a0)
  use s, s'
  constructor
  · intro j hj
    -- For j ≠ i, s and s' agree; reduce `Function.update` and use `hj` to simplify.
    dsimp [CoordinateSpace.proj, s, s', Function.update]
    simp [hj]
  · -- Opts differ: reference has {accept} while s' has {accept, reject}
    have hs : (reductionProblemMany φ).Opt s = {accept} := opt_reference_many (n := n) φ
    -- obtain a concrete equality `Formula.eval a0 φ = false` from the ¬tautology witness
    cases hval : Formula.eval a0 φ with
    | true => exact (ha0 hval).elim
    | false =>
      have hs' : (reductionProblemMany φ).Opt s' = {accept, reject} :=
        opt_falsifying_many (φ := φ) (k := i) (a_assn := a0) (hfalse := hval)

      intro heq
      -- heq: Opt s = Opt s' so {accept} = {accept, reject}
      have eq_sets : ({accept} : Set ReductionAction) = {accept, reject} := by
        simpa [hs, hs'] using heq
      -- contradiction: `reject ∈ {accept, reject}` but `reject ∉ {accept}`
      have H2 : reject ∉ ({accept} : Set ReductionAction) := by
        simp [Set.mem_singleton_iff]
      have hmem : reject ∈ ({accept} : Set ReductionAction) := by
        simp [eq_sets]
      exact H2 hmem

end DecisionQuotient
