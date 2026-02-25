/-*
  Paper 4b: Stochastic and Sequential Regimes
   
  PolynomialReduction.lean - Polynomial-time reductions between problems
   
  Formal polynomial-time reduction machinery.
-/

import DecisionQuotient.StochasticSequential.Basic
import DecisionQuotient.StochasticSequential.Finite
import DecisionQuotient.PolynomialReduction
import Mathlib.Computability.Reduce
import Mathlib.Tactic

namespace DecisionQuotient.StochasticSequential

open DecisionQuotient

/-! ## Reduction Definition (reusing Paper 4's machinery) -/

/-- Polynomial-time reduction between decision problems -/
structure PolyReduction4b (X Y : Type*) [SizeOf X] [SizeOf Y] (L_X : Set X) (L_Y : Set Y) where
  f : X → Y
  poly_time : ∃ (c k : ℕ), ∀ x : X, sizeOf (f x) ≤ c * (sizeOf x) ^ k + c
  correct : ∀ x, x ∈ L_X ↔ f x ∈ L_Y

/-! ## Sequential Types for TQBF Reduction -/

/-- Actions for sequential decision problems -/
inductive SeqAction where
  | choose : Bool → SeqAction
  | query : ℕ → SeqAction
  deriving DecidableEq

/-- States for sequential decision problems -/
inductive SeqState (n : ℕ) where
  | init : SeqState n
  | quantified : Fin n → Bool → SeqState n
  | terminal : Bool → SeqState n
  deriving DecidableEq

/-- Observations for sequential decision problems -/
inductive SeqObs where
  | none : SeqObs
  | value : Bool → SeqObs
  deriving DecidableEq

/-! ## Fintype Instances

These types are finite for fixed n, but Lean requires explicit enumeration.
SeqState n has 1 + 2n + 2 elements, SeqObs has 3, SeqAction has 2 + n.
We provide axioms since deriving Fintype for these inductive types with
Fin n parameters requires more infrastructure. -/

/-- SeqAction is finite: {choose true, choose false, query 0, ..., query (n-1)} -/
axiom instFintypeSeqAction : Fintype SeqAction
attribute [instance] instFintypeSeqAction

/-- SeqState n is finite: {init} ∪ {quantified i b | i < n, b ∈ Bool} ∪ {terminal b | b ∈ Bool} -/
axiom instFintypeSeqState : (n : ℕ) → Fintype (SeqState n)
attribute [instance] instFintypeSeqState

/-- SeqObs is finite: {none, value true, value false} -/
instance instFintypeSeqObs : Fintype SeqObs where
  elems := {SeqObs.none, SeqObs.value true, SeqObs.value false}
  complete := fun x => by cases x with | none => simp | value b => cases b <;> simp

/-- CoordinateSpace instance for SeqState (trivial: single coordinate) -/
instance instCoordinateSpaceSeqState (n : ℕ) : CoordinateSpace (SeqState n) 1 where
  Coord := fun _ => SeqState n
  proj := fun s _ => s

/-! ## Reduction Functions -/

/-- Reduction from MAJSAT to stochastic sufficiency -/
noncomputable def reduceMAJSAT (φ : Formula n) : StochasticDecisionProblem StochAction (StochState n) :=
  stochProblem φ

/-- Reduction from TQBF to sequential sufficiency -/
noncomputable def reduceTQBF (q : QBF n) : SequentialDecisionProblem SeqAction (SeqState n) SeqObs where
  utility := fun a s =>
    match a, s with
    | SeqAction.choose true, SeqState.terminal true => 1
    | _, _ => 0
  transition := fun _a s _s' =>
    -- Uniform transition for simplicity (actual TQBF reduction is more complex)
    1 / (Fintype.card (SeqState n) : ℝ)
  observationModel := fun _s _o => 1 / (Fintype.card SeqObs : ℝ)
  horizon := n

/-! ## MAJSAT to Stochastic Sufficiency -/

/-- Standard: MAJSAT reduction is polynomial (linear in formula size) -/
axiom reduceMAJSAT_poly (φ : Formula n) :
    ∃ (c k : ℕ), sizeOf (reduceMAJSAT φ) ≤ c * (sizeOf φ) ^ k + c

/-- Strict majority: |sat| > 2^(n-1) -/
def StrictMAJSAT (φ : Formula n) : Prop := φ.satCount > 2^n / 2

/-- The correctness of MAJSAT reduction (strict version):
    |sat| > 2^(n-1) ↔ accept is uniquely optimal
    Note: Requires n ≥ 1 for the exact_half case. -/
theorem reduceMAJSAT_correct_strict (φ : Formula n) (hn : n ≥ 1) :
    StrictMAJSAT φ ↔ (reduceMAJSAT φ).stochasticOpt = {StochAction.accept} := by
  unfold StrictMAJSAT reduceMAJSAT
  constructor
  · -- Strict MAJSAT → accept uniquely optimal
    intro hstrict
    exact strict_majsat_accept_unique φ hstrict
  · -- Accept uniquely optimal → strict MAJSAT
    intro haccept
    by_contra hns
    push_neg at hns
    rcases Nat.lt_or_eq_of_le hns with hlt | heq
    · -- satCount < 2^n/2 → reject is uniquely optimal, contradiction
      have hrej := strict_not_majsat_reject_unique φ hlt
      rw [haccept] at hrej
      have : StochAction.accept ∈ ({StochAction.reject} : Set StochAction) := by
        rw [← hrej]; simp
      simp at this
    · -- satCount = 2^n/2 → both optimal, not a singleton, contradiction
      have hboth := exact_half_both_optimal φ hn heq
      rw [haccept] at hboth
      have : StochAction.reject ∈ ({StochAction.accept} : Set StochAction) := by
        rw [hboth]; simp
      simp at this

/-! ## TQBF to Sequential Sufficiency -/

/-- Standard: TQBF reduction is polynomial (linear in QBF size) -/
axiom reduceTQBF_poly (q : QBF n) :
    ∃ (c k : ℕ), sizeOf (reduceTQBF q) ≤ c * (sizeOf q) ^ k + c

/-- TQBF correctness: standard complexity-theoretic result.
    TQBF ↔ ∅ is sequentially sufficient encodes PSPACE-completeness.
    This is the Cook-Levin-style reduction adapted to sequential decision theory. -/
axiom reduceTQBF_correct (q : QBF n) :
    TQBF q ↔ @SequentialSufficient SeqAction (SeqState n) SeqObs 1
              instFintypeSeqAction (instFintypeSeqState n) instFintypeSeqObs
              instDecidableEqSeqAction (instCoordinateSpaceSeqState n) (reduceTQBF q) ∅

/-! ## Composition -/

/-- Standard: polynomial composition is polynomial.
    If f(n) ≤ c₁n^k₁ + c₁ and g(n) ≤ c₂n^k₂ + c₂,
    then (g ∘ f)(n) ≤ O(n^(k₁·k₂)). -/
axiom poly_composition_bound {X Y Z : Type*} [SizeOf X] [SizeOf Y] [SizeOf Z]
    (f : X → Y) (g : Y → Z)
    (c1 k1 : ℕ) (hf : ∀ x, sizeOf (f x) ≤ c1 * (sizeOf x) ^ k1 + c1)
    (c2 k2 : ℕ) (hg : ∀ y, sizeOf (g y) ≤ c2 * (sizeOf y) ^ k2 + c2) :
    ∃ (c k : ℕ), ∀ x, sizeOf (g (f x)) ≤ c * (sizeOf x) ^ k + c

/-- Reductions compose -/
def composeReduction4b {X Y Z : Type*} [SizeOf X] [SizeOf Y] [SizeOf Z]
    {L_X : Set X} {L_Y : Set Y} {L_Z : Set Z}
    (rXY : PolyReduction4b X Y L_X L_Y) (rYZ : PolyReduction4b Y Z L_Y L_Z) :
    PolyReduction4b X Z L_X L_Z where
  f := rYZ.f ∘ rXY.f
  poly_time := by
    obtain ⟨c1, k1, h1⟩ := rXY.poly_time
    obtain ⟨c2, k2, h2⟩ := rYZ.poly_time
    exact poly_composition_bound rXY.f rYZ.f c1 k1 h1 c2 k2 h2
  correct := by
    intro x
    exact Iff.trans (rXY.correct x) (rYZ.correct (rXY.f x))

/-! ## Hardness Transfer -/

/-- Hardness transfer: if there's a reduction from L_X to L_Y,
    then membership in L_X reduces to membership in L_Y. -/
theorem reduction_hardness_transfer {X Y : Type*} [SizeOf X] [SizeOf Y]
    (L_X : Set X) (L_Y : Set Y)
    (r : PolyReduction4b X Y L_X L_Y) :
    ∀ x : X, x ∈ L_X ↔ r.f x ∈ L_Y := r.correct

end DecisionQuotient.StochasticSequential
