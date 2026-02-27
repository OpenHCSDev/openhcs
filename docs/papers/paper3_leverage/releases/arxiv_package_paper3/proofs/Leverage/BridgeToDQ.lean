/-
  Paper 3: Leverage-Driven Software Architecture

  Leverage/BridgeToDQ.lean - Correspondence between DOF and Structural Rank

  Mechanizes the bridge between Paper 3's degrees of freedom and Paper 4's
  structural rank. The central theorem:

      Architecture.dof = (canonicalDP n).srank

  Combined with Paper 2's result (coherence ↔ DOF = 1):

      SSOT (DOF = 1) ↔ srank = 1 ↔ tractable sufficiency checking
      Incoherent (DOF > 1) → srank > 1 → coNP-hard sufficiency checking

  The canonical encoding:
    State  : Fin n → Bool   (n binary coordinates)
    Action : Fin n ⊕ Unit  (query coordinate i, or default fallback)
    Utility: (Sum.inl i, s) ↦ if s i then 2 else 0
             (Sum.inr _,  _) ↦ 1

  Witness for isRelevant i:
    s  = Function.update (fun _ => false) i true  -- only coord i is true
    s' = fun _ => false                           -- all false
    These agree on every j ≠ i, but:
      Opt(s)  = {Sum.inl i}   (utility 2, beats everything)
      Opt(s') = {Sum.inr ()}  (utility 1, beats all Sum.inl j at 0)
    So Opt(s) ≠ Opt(s'), witnessing relevance of i.
-/

import Leverage.Foundations
import DecisionQuotient.Tractability.StructuralRank

namespace Leverage

open Classical DecisionQuotient

/-! ## CoordinateSpace instance for Fin n → Bool -/

/-- Boolean vectors form a coordinate space: n coordinates each of type Bool -/
instance boolVecCoord (n : ℕ) : CoordinateSpace (Fin n → Bool) n where
  Coord _ := Bool
  proj s i := s i

/-! ## Canonical Decision Problem -/

/-- The canonical decision problem for DOF = n.
    Action Sum.inl i: utility 2 if coordinate i is true, 0 if false.
    Action Sum.inr (): fallback with constant utility 1.
    Every coordinate is relevant by construction. -/
noncomputable def canonicalDP (n : ℕ) :
    DecisionProblem (Fin n ⊕ Unit) (Fin n → Bool) where
  utility a s :=
    match a with
    | Sum.inl i => if s i then (2 : ℝ) else 0
    | Sum.inr _ => 1

/-! ## Every Coordinate is Relevant -/

/-- In the canonical problem, every coordinate i is relevant.
    Witness: s = all-false except i (true), s' = all-false.
    Then Opt(s) = {Sum.inl i} ≠ {Sum.inr ()} = Opt(s'). -/
theorem canonical_all_relevant (n : ℕ) (i : Fin n) :
    (canonicalDP n).isRelevant i := by
  -- Pin dp at universe 0: A = Fin n ⊕ Unit : Type 0, S = Fin n → Bool : Type 0.
  -- This eliminates the u_1 vs 0 cumulativity drift that breaks Eq.mp / cast / ▸.
  -- With dp pinned, dp.Opt s has concrete type Set.{0}, so heq ▸ hmem works.
  let dp : DecisionProblem (Fin n ⊕ Unit) (Fin n → Bool) := canonicalDP n
  show dp.isRelevant i
  let s  : Fin n → Bool := Function.update (fun _ => false) i true
  let s' : Fin n → Bool := fun _ => false
  refine ⟨s, s', ?_agree, ?_opt⟩
  · -- s and s' agree on all j ≠ i
    intro j hji
    show s j = s' j
    simp only [s, s', Function.update_apply, if_neg hji]
  · -- dp.Opt s ≠ dp.Opt s'
    intro heq
    have hs_i : s i = true := by simp [s]
    -- Sum.inl i ∈ dp.Opt s: hmem stated at Set level so heq ▸ can find dp.Opt s
    have hmem : Sum.inl i ∈ dp.Opt s := by
      show dp.isOptimal (Sum.inl i) s
      intro a'
      cases a' with
      | inl j =>
        simp only [dp, canonicalDP, hs_i, if_true]
        split_ifs <;> norm_num
      | inr _ =>
        simp only [dp, canonicalDP, hs_i, if_true]
        norm_num
    -- Sum.inl i ∉ dp.Opt s': utility 0, beaten by Sum.inr () at 1
    have hnotmem : Sum.inl i ∉ dp.Opt s' := by
      show ¬dp.isOptimal (Sum.inl i) s'
      intro hopt
      have h := hopt (Sum.inr ())
      simp only [dp, canonicalDP, s'] at h
      norm_num at h
    -- heq : dp.Opt s = dp.Opt s'; dp.Opt s appears in hmem's type, so ▸ works
    exact hnotmem (heq ▸ hmem)

/-! ## Structural Rank Equals DOF -/

/-- The canonical problem on n coordinates has structural rank exactly n -/
theorem canonical_srank_eq_n (n : ℕ) :
    (canonicalDP n).srank = n := by
  have hall : ∀ i : Fin n, (canonicalDP n).isRelevant i := canonical_all_relevant n
  unfold DecisionProblem.srank
  rw [Finset.filter_true_of_mem (fun i _ => hall i)]
  simp

/-! ## Bridge Theorems -/

/-- **Bridge Theorem**: Architecture DOF equals structural rank of the canonical encoding.
    This identifies Paper 3's degrees of freedom with Paper 4's interaction
    dimensionality: the number of independent state axes equals the number of
    coordinates the decision boundary genuinely depends on. -/
theorem dof_eq_srank (a : Architecture) :
    (canonicalDP a.dof).srank = a.dof :=
  canonical_srank_eq_n a.dof

/-- SSOT (DOF = 1) implies srank = 1: minimal interaction dimensionality.
    Under Paper 4's complexity results, srank = 1 means SUFFICIENCY-CHECK
    is tractable for this architecture's decision structure. -/
theorem ssot_srank_one (a : Architecture) (h : a.is_ssot) :
    (canonicalDP a.dof).srank = 1 := by
  rw [dof_eq_srank, h]

/-- Incoherent (DOF > 1) implies srank > 1: the full coNP-hard regime.
    Under Paper 4's coNP-hardness result, incoherent architectures pay the
    complexity tax on sufficiency checking. -/
theorem incoherent_srank_gt_one (a : Architecture) (h : a.dof > 1) :
    (canonicalDP a.dof).srank > 1 := by
  rw [dof_eq_srank]; exact h

/-- **Physical Necessity Chain**: Maximum coherence forces tractability.

    If no architecture with the same capabilities beats `a` in leverage,
    then `a` must have DOF = 1 (max_leverage_forces_dof_one), hence srank = 1,
    hence sufficiency-checking is tractable.

    The chain: max leverage → DOF = 1 → srank = 1 → tractable.
    Physical optimality and computational tractability coincide at DOF = 1. -/
theorem max_coherence_forces_tractability (a : Architecture)
    (h_caps : a.capabilities > 0)
    (h_max : ∀ a' : Architecture, a'.capabilities = a.capabilities → ¬ a'.higher_leverage a) :
    (canonicalDP a.dof).srank = 1 :=
  ssot_srank_one a (max_leverage_forces_dof_one a h_caps h_max)

end Leverage
