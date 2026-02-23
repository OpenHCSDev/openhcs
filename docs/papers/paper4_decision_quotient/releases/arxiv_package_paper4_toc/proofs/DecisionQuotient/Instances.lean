/-
  Paper 4: Decision-Relevant Uncertainty
  
  Instances.lean - Concrete ProductSpace Instances
  
  This file provides concrete instantiations of the ProductSpace class,
  proving the abstraction is not vacuous and can be applied to real types.
-/

import DecisionQuotient.Sufficiency
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Function.Basic

namespace DecisionQuotient

/-! ## Boolean Vector Space: (Fin n → Bool) -/

/-- The canonical CoordinateSpace on function types -/
instance functionCoordinateSpace (X : Type*) (n : ℕ) : CoordinateSpace (Fin n → X) n where
  Coord := fun _ => X
  proj := fun f i => f i

/-- The canonical ProductSpace on function types.
    This is the key concrete instance that shows our abstraction works. -/
instance functionProductSpace (X : Type*) (n : ℕ) [DecidableEq (Fin n)] : 
    ProductSpace (Fin n → X) n where
  Coord := fun _ => X
  proj := fun f i => f i
  replace := fun f i g => fun j => if j = i then g i else f j
  replace_proj_eq := by
    intro f g i
    simp only [ite_true]
  replace_proj_ne := by
    intro f g i j hne
    simp only [hne, ite_false]

/-- Specialization: Boolean vectors form a ProductSpace -/
example (n : ℕ) : ProductSpace (Fin n → Bool) n := inferInstance

/-- Specialization: Rational vectors form a ProductSpace -/
example (n : ℕ) : ProductSpace (Fin n → ℚ) n := inferInstance

/-! ## Product Types: A × B (same type for simplicity) -/

/-- Binary product of same type as a CoordinateSpace with 2 coordinates -/
instance prodCoordinateSpace (X : Type*) : CoordinateSpace (X × X) 2 where
  Coord := fun _ => X
  proj := fun p i => if i = 0 then p.1 else p.2

/-- Binary product of same type as a ProductSpace -/
instance prodProductSpace (X : Type*) : ProductSpace (X × X) 2 where
  Coord := fun _ => X
  proj := fun p i => if i = 0 then p.1 else p.2
  replace := fun p i q =>
    if i = 0 then (q.1, p.2) else (p.1, q.2)
  replace_proj_eq := by
    intro p q i
    by_cases h : i = 0 <;> simp [h]
  replace_proj_ne := by
    intro p q i j hne
    split_ifs with h1 h2
    · -- j = 0, i = 0: contradiction with hne
      omega
    · -- j = 0, i ≠ 0
      rfl
    · -- j ≠ 0, i = 0
      rfl
    · -- j ≠ 0, i ≠ 0: contradiction (both must be 1)
      omega

/-! ## Verification: The state construction works -/

/-- Demonstrate that replace actually swaps coordinates correctly -/
example : (functionProductSpace Bool 3).replace 
    (fun _ => true) 1 (fun i => i = 1) = 
    (fun i => if i = 1 then true else true) := by
  funext i
  simp only [functionProductSpace]
  split_ifs with h
  · simp [h]
  · rfl

/-- Key property: replacing then projecting gives the replacement value -/
theorem replace_proj_self {X : Type*} {n : ℕ} [DecidableEq (Fin n)]
    (f g : Fin n → X) (i : Fin n) :
    (functionProductSpace X n).proj ((functionProductSpace X n).replace f i g) i = g i := 
  (functionProductSpace X n).replace_proj_eq f g i

/-- Key property: replacing preserves other coordinates -/
theorem replace_proj_other {X : Type*} {n : ℕ} [DecidableEq (Fin n)]
    (f g : Fin n → X) (i j : Fin n) (hne : j ≠ i) :
    (functionProductSpace X n).proj ((functionProductSpace X n).replace f i g) j = f j := 
  (functionProductSpace X n).replace_proj_ne f g i j hne

/-! ## Application: Sufficiency on Boolean vectors -/

/-- On Boolean vectors, the state construction theorem applies directly -/
theorem bool_sufficient_erase_irrelevant {A : Type*} {n : ℕ} [DecidableEq (Fin n)]
    (dp : DecisionProblem A (Fin n → Bool)) (I : Finset (Fin n)) (i : Fin n)
    (hI : dp.isSufficient I) (hirr : dp.isIrrelevant i) :
    dp.isSufficient (I.erase i) :=
  dp.sufficient_erase_irrelevant' I i hI hirr

/-- On Boolean vectors, minimal sufficient sets are unique -/
theorem bool_minimalSufficient_unique {A : Type*} {n : ℕ} [DecidableEq (Fin n)]
    (dp : DecisionProblem A (Fin n → Bool)) (I J : Finset (Fin n))
    (hI : dp.isMinimalSufficient I) (hJ : dp.isMinimalSufficient J) :
    I = J :=
  dp.relevantSet_is_minimal I hI J hJ

end DecisionQuotient
