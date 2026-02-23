/-*
  Paper 4b: Stochastic and Sequential Regimes
  
  TemporalLearning.lean - Learning structure across problem sequences
  
  Formalizes Bayesian learning of structure classes.
-/

import Paper4bStochasticSequential.Basic
import Mathlib.Data.Real.Basic

namespace Paper4bStochasticSequential

/-! ## Structure Classes -/

/-- A structure class represents a tractable subcase -/
structure StructureClass where
  name : String
  tractable : Prop

/-- Prior distribution over structure classes -/
def StructurePrior (C : Type*) := C → ℝ

/-! ## Bayesian Learning -/

/-- Posterior after observing evidence -/
def posterior {C : Type*} 
    (prior : StructurePrior C)
    (likelihood : C → ℝ) 
    (evidence : ℝ) : 
    C → ℝ :=
  fun c => prior c * likelihood c / evidence

/-- Bayesian update: posterior ∝ prior × likelihood -/
theorem bayesian_update {C : Type*}
    (prior : StructurePrior C)
    (c : C)
    (likelihood : C → ℝ)
    (evidence : ℝ)
    (hPos : evidence = ∑ c', prior c' * likelihood c') :
    posterior prior likelihood evidence c = prior c * likelihood c / evidence := rfl

/-! ## Convergence -/

/-- Structure classes are identifiable if distinct -/
structure Identifiable (C : Type*) (likelihood : C → ℝ → Prop) : Prop where
  distinct : ∀ c₁ c₂ : C, (∀ e, likelihood c₁ e = likelihood c₂ e) → c₁ = c₂

/-- Posterior is proportional to likelihood under uniform prior -/
theorem posterior_uniform_prior {C : Type*} [Fintype C] [Nonempty C]
    (likelihood : C → ℝ)
    (c₀ : C)
    (hLike : likelihood c₀ > 0)
    (hLike_other : ∀ c, c ≠ c₀ → likelihood c = 0) :
    let prior : StructurePrior C := fun _ => 1 / (Fintype.card C : ℝ)
    let ev := ∑ c, prior c * likelihood c
    posterior prior likelihood ev c₀ = 1 := by
  intro prior ev
  simp only [posterior]
  have hcard : (Fintype.card C : ℝ) ≠ 0 := by positivity
  have h_ev : ev = prior c₀ * likelihood c₀ := by
    simp only [Finset.sum_eq_single c₀]
    · simp [prior, hLike_other]
    · intro c _ hne; exact hLike_other c hne
    · exact Finset.mem_univ c₀
  rw [h_ev]
  simp [prior, hLike, hcard]
  field_simp [hLike]
  ring

/-! ## Abstention Reduction -/

/-- Abstention set shrinks as agent learns -/
def abstentionSet {C : Type*} 
    (k : ℕ) 
    (posterior : C → ℝ)
    (threshold : ℝ) : 
    Set C :=
  { c | posterior c < threshold }

/-- Abstention reduces over time -/
theorem abstention_decreases {C : Type*}
    (posterior₁ posterior₂ : C → ℝ)
    (h : ∀ c, posterior₂ c ≥ posterior₁ c)
    (threshold : ℝ) :
    abstentionSet k₂ posterior₂ threshold ⊆ 
    abstentionSet k₁ posterior₁ threshold := by
  intro c hc
  unfold abstentionSet at *
  specialize h c
  linarith

end Paper4bStochasticSequential
