/-
  Paper 4: Decision-Relevant Uncertainty

  ThermodynamicLift.lean

  Conditional complexity-to-thermodynamics bridge:
  - lifts bit-operation lower bounds to energy/carbon lower bounds
  - composes with integrity-resource closure assumptions

  Scope discipline: these are conditional theorems over declared conversion
  constants and lower-bound hypotheses, not unconditional physical laws.

  ## Triviality Level
  TRIVIAL: This is derivation of physical consequences from complexity bounds.
  The nontrivial work is in the complexity proofs.

  ## Dependencies
  - Chain: ClaimClosure.lean (hardness) → IntegrityCompetence.lean → here
-/

import DecisionQuotient.IntegrityCompetence
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace DecisionQuotient
namespace ThermodynamicLift

open DecisionQuotient.IntegrityCompetence

/-- Declared thermodynamic conversion model (discrete lower-bound form). -/
structure ThermoModel where
  /-- Lower-bound energy cost per irreversible bit-operation unit. -/
  joulesPerBit : ℕ
  /-- Lower-bound carbon cost per joule (e.g., grams-CO2e per joule unit). -/
  carbonPerJoule : ℕ

/-- Energy lower bound induced by a lower bound on irreversible bit operations. -/
def energyLowerBound (M : ThermoModel) (bitOpsLB : ℕ) : ℕ :=
  M.joulesPerBit * bitOpsLB

/-- Landauer per-bit conversion in real units: `k_B * T * ln 2`. -/
noncomputable def landauerJoulesPerBit (kB T : ℝ) : ℝ :=
  kB * T * Real.log 2

/-- Positivity of the Landauer conversion for positive Boltzmann constant and temperature. -/
theorem landauerJoulesPerBit_pos {kB T : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) :
    0 < landauerJoulesPerBit kB T := by
  unfold landauerJoulesPerBit
  have hlog2 : 0 < Real.log 2 := by
    exact Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hkT : 0 < kB * T := mul_pos hkB hT
  exact mul_pos hkT hlog2

/-- If a discrete thermodynamic model is calibrated to Landauer conversion,
    positivity of `joulesPerBit` is derived, not postulated. -/
theorem joulesPerBit_pos_of_landauer_calibration
    (M : ThermoModel) {kB T : ℝ}
    (hkB : 0 < kB) (hT : 0 < T)
    (hCal : (M.joulesPerBit : ℝ) = landauerJoulesPerBit kB T) :
    0 < M.joulesPerBit := by
  have hLandauer : 0 < landauerJoulesPerBit kB T := landauerJoulesPerBit_pos hkB hT
  have hCast : 0 < (M.joulesPerBit : ℝ) := by simpa [hCal] using hLandauer
  exact_mod_cast hCast

/-- Carbon lower bound induced by the same bit-operation lower bound. -/
def carbonLowerBound (M : ThermoModel) (bitOpsLB : ℕ) : ℕ :=
  M.carbonPerJoule * energyLowerBound M bitOpsLB

/-- Mandatory cost (energy): under positive per-bit conversion and positive
lower-bounded irreversible work, energy lower bound is strictly positive. -/
theorem energy_lower_mandatory
    (M : ThermoModel) {b : ℕ}
    (hJ : 0 < M.joulesPerBit) (hb : 0 < b) :
    0 < energyLowerBound M b := by
  unfold energyLowerBound
  exact Nat.mul_pos hJ hb

/-- Mandatory energy lower bound derived from Landauer calibration and positive
    physical constants (`k_B > 0`, `T > 0`). -/
theorem energy_lower_mandatory_of_landauer_calibration
    (M : ThermoModel) {kB T : ℝ} {b : ℕ}
    (hkB : 0 < kB) (hT : 0 < T)
    (hCal : (M.joulesPerBit : ℝ) = landauerJoulesPerBit kB T)
    (hb : 0 < b) :
    0 < energyLowerBound M b := by
  exact energy_lower_mandatory M (joulesPerBit_pos_of_landauer_calibration M hkB hT hCal) hb

/-- Mandatory cost (carbon): under positive per-joule conversion and positive
energy lower bound, carbon lower bound is strictly positive. -/
theorem carbon_lower_mandatory
    (M : ThermoModel) {b : ℕ}
    (hρ : 0 < M.carbonPerJoule)
    (hEnergy : 0 < energyLowerBound M b) :
    0 < carbonLowerBound M b := by
  unfold carbonLowerBound
  exact Nat.mul_pos hρ hEnergy

/-- Mandatory cost bundle directly from positive conversion constants and
positive lower-bounded irreversible work. -/
theorem mandatory_cost_bundle
    (M : ThermoModel) {b : ℕ}
    (hJ : 0 < M.joulesPerBit)
    (hC : 0 < M.carbonPerJoule)
    (hb : 0 < b) :
    0 < energyLowerBound M b ∧ 0 < carbonLowerBound M b := by
  refine ⟨energy_lower_mandatory M hJ hb, ?_⟩
  exact carbon_lower_mandatory M hC (energy_lower_mandatory M hJ hb)

/-- Additive conservation in the declared linear model (energy). -/
theorem energy_lower_additive
    (M : ThermoModel) (b₁ b₂ : ℕ) :
    energyLowerBound M (b₁ + b₂) =
      energyLowerBound M b₁ + energyLowerBound M b₂ := by
  unfold energyLowerBound
  exact Nat.mul_add M.joulesPerBit b₁ b₂

/-- Additive conservation in the declared linear model (carbon). -/
theorem carbon_lower_additive
    (M : ThermoModel) (b₁ b₂ : ℕ) :
    carbonLowerBound M (b₁ + b₂) =
      carbonLowerBound M b₁ + carbonLowerBound M b₂ := by
  unfold carbonLowerBound
  rw [energy_lower_additive]
  exact Nat.mul_add M.carbonPerJoule
    (energyLowerBound M b₁) (energyLowerBound M b₂)

/-- Monotone lift: bit-operation lower bounds imply energy lower bounds. -/
theorem energy_lower_from_bits_lower
    (M : ThermoModel) {b₁ b₂ : ℕ} (hBits : b₁ ≤ b₂) :
    energyLowerBound M b₁ ≤ energyLowerBound M b₂ := by
  exact Nat.mul_le_mul_left M.joulesPerBit hBits

/-- Monotone lift: bit-operation lower bounds imply carbon lower bounds. -/
theorem carbon_lower_from_bits_lower
    (M : ThermoModel) {b₁ b₂ : ℕ} (hBits : b₁ ≤ b₂) :
    carbonLowerBound M b₁ ≤ carbonLowerBound M b₂ := by
  unfold carbonLowerBound
  exact Nat.mul_le_mul_left M.carbonPerJoule
    (energy_lower_from_bits_lower M hBits)

/-- Eventual family lift: asymptotic bit lower bounds transfer to energy/carbon. -/
theorem eventual_thermo_lift
    (M : ThermoModel) (bitLB bitUsed : ℕ → ℕ) (n0 : ℕ)
    (hBits : ∀ n, n ≥ n0 → bitLB n ≤ bitUsed n) :
    (∀ n, n ≥ n0 → energyLowerBound M (bitLB n) ≤ energyLowerBound M (bitUsed n)) ∧
    (∀ n, n ≥ n0 → carbonLowerBound M (bitLB n) ≤ carbonLowerBound M (bitUsed n)) := by
  constructor
  · intro n hn
    exact energy_lower_from_bits_lower M (hBits n hn)
  · intro n hn
    exact carbon_lower_from_bits_lower M (hBits n hn)

/-- Conditional bundle with hardness-closure:
    if exact competence collapses complexity classes, then under non-collapse
    exact competence is impossible; with any declared bit lower bound this
    simultaneously yields energy and carbon lower bounds. -/
theorem hardness_thermo_bundle_conditional
    {P_eq_coNP ExactCertificationCompetence : Prop}
    (hNeq : ¬ P_eq_coNP)
    (hCollapse : ExactCertificationCompetence → P_eq_coNP)
    (M : ThermoModel)
    {bitLB bitUsed : ℕ} (hBits : bitLB ≤ bitUsed) :
    ¬ ExactCertificationCompetence ∧
      energyLowerBound M bitLB ≤ energyLowerBound M bitUsed ∧
      carbonLowerBound M bitLB ≤ carbonLowerBound M bitUsed := by
  refine ⟨?_, energy_lower_from_bits_lower M hBits, carbon_lower_from_bits_lower M hBits⟩
  exact integrity_resource_bound (P_eq_coNP := P_eq_coNP)
    (PolytimeUniversalCompetence := ExactCertificationCompetence) hNeq hCollapse

/-- Conditional mandatory+conserved bundle in the declared linear model. -/
theorem mandatory_conserved_bundle_conditional
    (M : ThermoModel)
    {b : ℕ}
    (hJ : 0 < M.joulesPerBit)
    (hC : 0 < M.carbonPerJoule)
    (hb : 0 < b)
    (b₁ b₂ : ℕ) :
    0 < energyLowerBound M b ∧
      0 < carbonLowerBound M b ∧
      energyLowerBound M (b₁ + b₂) =
        energyLowerBound M b₁ + energyLowerBound M b₂ ∧
      carbonLowerBound M (b₁ + b₂) =
        carbonLowerBound M b₁ + carbonLowerBound M b₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact energy_lower_mandatory M hJ hb
  · exact carbon_lower_mandatory M hC (energy_lower_mandatory M hJ hb)
  · exact energy_lower_additive M b₁ b₂
  · exact carbon_lower_additive M b₁ b₂

/-! ### Neukart–Vinokur Thermodynamic Duality as Special Case

Neukart and Vinokur (2025) propose dU = T·dS - p·dV + λ·dC where C is a
"complexity coordinate." Under our declared model, this follows as a
specialization: let C = bitLB from query obstruction, then dU ≥ λ·dC
with λ = joulesPerBit > 0 declared per Landauer.

The derivation is trivial given our framework: their λ·dC is exactly
our energyLowerBound when C is identified with bit-operation count.
-/

/-- Neukart–Vinokur complexity coordinate: identified with bit-operation lower bound. -/
abbrev complexityCoordinate := ℕ

/-- Neukart–Vinokur λ parameter: identified with joules-per-bit conversion constant. -/
def nvLambda (M : ThermoModel) : ℕ := M.joulesPerBit

/-- Neukart–Vinokur thermodynamic duality: dU ≥ λ·dC.
    This is exactly the energy lower bound from Proposition thermo-lift. -/
theorem neukart_vinokur_duality
    (M : ThermoModel) (C : complexityCoordinate) :
    energyLowerBound M C = nvLambda M * C := by
  rfl

/-- Neukart–Vinokur mandatory positive cost: λ > 0 ∧ dC > 0 → dU > 0. -/
theorem neukart_vinokur_mandatory
    (M : ThermoModel) {C : complexityCoordinate}
    (hLam : 0 < nvLambda M) (hC : 0 < C) :
    0 < energyLowerBound M C := by
  exact energy_lower_mandatory M hLam hC

/-- Neukart–Vinokur monotonicity: C₁ ≤ C₂ → λ·C₁ ≤ λ·C₂. -/
theorem neukart_vinokur_monotone
    (M : ThermoModel) {C₁ C₂ : complexityCoordinate} (hC : C₁ ≤ C₂) :
    energyLowerBound M C₁ ≤ energyLowerBound M C₂ := by
  exact energy_lower_from_bits_lower M hC

/-- Neukart–Vinokur additivity: λ·(C₁ + C₂) = λ·C₁ + λ·C₂. -/
theorem neukart_vinokur_additive
    (M : ThermoModel) (C₁ C₂ : complexityCoordinate) :
    energyLowerBound M (C₁ + C₂) =
      energyLowerBound M C₁ + energyLowerBound M C₂ := by
  exact energy_lower_additive M C₁ C₂

/-- Full Neukart–Vinokur bundle: under positive λ and positive complexity work,
    the thermodynamic duality holds with mandatory, monotone, and additive properties. -/
theorem neukart_vinokur_bundle
    (M : ThermoModel) {C : complexityCoordinate}
    (hLam : 0 < nvLambda M) (hC : 0 < C)
    (C₁ C₂ : complexityCoordinate) (hMono : C₁ ≤ C₂) :
    energyLowerBound M C = nvLambda M * C ∧
    0 < energyLowerBound M C ∧
    energyLowerBound M C₁ ≤ energyLowerBound M C₂ ∧
    energyLowerBound M (C₁ + C₂) = energyLowerBound M C₁ + energyLowerBound M C₂ := by
  exact ⟨neukart_vinokur_duality M C,
         neukart_vinokur_mandatory M hLam hC,
         neukart_vinokur_monotone M hMono,
         neukart_vinokur_additive M C₁ C₂⟩

end ThermodynamicLift
end DecisionQuotient
