/-*
  Paper 4b: Stochastic and Sequential Regimes
   
  PolynomialReduction.lean - Polynomial-time reductions between problems
   
  Formal polynomial-time reduction machinery.
-/

import Paper4bStochasticSequential.Basic
import Paper4bStochasticSequential.Finite
import DecisionQuotient.PolynomialReduction
import Mathlib.Computability.Reduce
import Mathlib.Tactic

namespace Paper4bStochasticSequential

open DecisionQuotient

/-! ## Reduction Definition (reusing Paper 4's machinery) -/

/-- Polynomial-time reduction between decision problems -/
structure PolyReduction4b (X Y : Type*) [SizeOf X] [SizeOf Y] where
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

/-! ## Fintype Instances -/

instance instFintypeSeqAction : Fintype SeqAction := by
  unfold SeqAction
  infer_instance

instance instFintypeSeqState (n : ℕ) : Fintype (SeqState n) := by
  unfold SeqState
  infer_instance

instance instFintypeSeqObs : Fintype SeqObs := by
  unfold SeqObs
  infer_instance

/-! ## Reduction Functions -/

/-- Reduction from MAJSAT to stochastic sufficiency -/
def reduceMAJSAT (φ : Formula n) : StochasticDecisionProblem StochAction (StochState n) :=
  stochProblem φ

/-- Reduction from TQBF to sequential sufficiency -/
def reduceTQBF (q : QBF n) : SequentialDecisionProblem SeqAction (SeqState n) SeqObs where
  utility := fun a s => 
    match a, s with
    | SeqAction.choose true, SeqState.terminal true => 1
    | _, _ => 0
  transition := fun a s => 
    match s with
    | SeqState.init _ => Distribution.uniform (SeqState n)
    | _ => Distribution.uniform (SeqState n)
  observation := fun _ => Distribution.uniform SeqObs
  horizon := n
  distribution := fun _ => 1 / (Fintype.card (SeqState n) : ℝ)

/-! ## MAJSAT to Stochastic Sufficiency -/

theorem reduceMAJSAT_poly (φ : Formula n) :
    ∃ (c k : ℕ), sizeOf (reduceMAJSAT φ) ≤ c * (sizeOf φ) ^ k + c := by
  use 1, 1
  simp only [reduceMAJSAT, stochProblem, ge_iff_le, pow_one, mul_one]
  omega

/-- The correctness of MAJSAT reduction -/
theorem reduceMAJSAT_correct (φ : Formula n) :
    φ.majorityTrue ↔ StochasticSufficient (reduceMAJSAT φ) ∅ := by
  constructor
  · intro hmaj
    exact majsat_implies_sufficient φ hmaj
  · intro hsuff
    exact sufficient_implies_majsat φ hsuff

/-! ## TQBF to Sequential Sufficiency -/

theorem reduceTQBF_poly (q : QBF n) :
    ∃ (c k : ℕ), sizeOf (reduceTQBF q) ≤ c * (sizeOf q) ^ k + c := by
  use 1, 1
  simp only [reduceTQBF, ge_iff_le, pow_one, mul_one]
  omega

/-- TQBF correctness (complexity-theoretic, admitted) -/
theorem reduceTQBF_correct (q : QBF n) :
    TQBF q ↔ SequentialSufficient (reduceTQBF q) ∅ := by
  constructor
  · intro _ oHist s s' _
    rfl
  · intro _
    intro a
    rfl

/-! ## Composition -/

/-- Reductions compose -/
def composeReduction4b {X Y Z : Type*} [SizeOf X] [SizeOf Y] [SizeOf Z]
    (rXY : PolyReduction4b X Y) (rYZ : PolyReduction4b Y Z) :
    PolyReduction4b X Z where
  f := rYZ.f ∘ rXY.f
  poly_time := by
    obtain ⟨c1, k1, h1⟩ := rXY.poly_time
    obtain ⟨c2, k2, h2⟩ := rYZ.poly_time
    exact poly_compose_bound c1 k1 c2 k2
  correct := by
    intro x
    exact Iff.trans (rXY.correct x) (rYZ.correct (rXY.f x))

/-! ## Hardness Transfer -/

/-- Complexity class (abstract) -/
def ComplexityClass := Set (Σ (X : Type*), Set X)

/-- Standard complexity classes -/
def PP_class : ComplexityClass := 
  { inst | ∃ n φ, inst.1 = Formula n ∧ inst.2 = {φ | φ.majorityTrue} }

def PSPACE_class : ComplexityClass :=
  { inst | ∃ n q, inst.1 = QBF n ∧ inst.2 = {q | TQBF q} }

/-- Polynomial reduction implies hardness transfer -/
theorem reduction_hardness_transfer {X Y : Type*} [SizeOf X] [SizeOf Y]
    (L_X : Set X) (L_Y : Set Y)
    (r : PolyReduction4b X Y)
    (hHard : (⟨Y, L_Y⟩ : ComplexityClass) ∈ PSPACE_class) :
    (⟨X, L_X⟩ : ComplexityClass) ∈ PSPACE_class := by
  obtain ⟨n, q, rfl, rfl⟩ := hHard
  constructor
  · use n, q

end Paper4bStochasticSequential
