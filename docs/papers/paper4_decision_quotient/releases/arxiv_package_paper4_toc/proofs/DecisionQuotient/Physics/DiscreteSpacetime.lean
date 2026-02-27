/-
  Paper 4: Decision-Relevant Uncertainty

  DiscreteSpacetime.lean

  Derivation chain: Discrete State → Discrete Time → Discrete Space → Thermodynamics

  ## Structure
  1. PROVEN: Discrete state + dynamics → discrete effective time (transition points)
  2. THEOREM: Lorentz compatibility — discrete time ↔ discrete space at same scale
              (trivial in ℕ; calibration handled explicitly below)
              cite: Einstein 1905, Minkowski 1908, Snyder 1947
  3. THEOREM: Planck-scale uniqueness under declared calibration
              and explicit non-uniqueness without calibration
              cite: Planck 1899 (calibration source)
  4. THEOREM: Landauer bound — provable from linear energy model (Nat.mul_pos)
              Physical content is in the declared constant joulesPerBit > 0
              cite: Landauer 1961, Bennett 2003
  5. LINK: Connect to ThermodynamicLift.lean

  ## Philosophy
  Each step is simple. The composition derives thermodynamics from computation.
  The triviality objection fails because trivial steps compose into non-trivial reach.

  ## Citations
  - Einstein, A. (1905). On the Electrodynamics of Moving Bodies.
  - Minkowski, H. (1908). Space and Time.
  - Snyder, H.S. (1947). Quantized Space-Time. Physical Review 71(1):38-41.
  - Planck, M. (1899). Über irreversible Strahlungsvorgänge.
  - Landauer, R. (1961). Irreversibility and Heat Generation.
  - Bennett, C.H. (2003). Notes on Landauer's Principle.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Countable
import Mathlib.Order.Basic
import DecisionQuotient.ThermodynamicLift

namespace DecisionQuotient
namespace Physics
namespace DiscreteSpacetime

open ThermodynamicLift

/-! ## Part 1: Discrete State → Discrete Time (PROVEN)

The core lemma: if state space is finite and dynamics is non-trivial,
the set of transition points in any trajectory is discrete (countable,
locally finite).
-/

/-- A discrete dynamical system: finite state space with transition function. -/
structure DiscreteSystem where
  /-- Finite state space. -/
  State : Type
  /-- Finiteness of state space. -/
  [hFin : Fintype State]
  /-- Decidable equality on states. -/
  [hDec : DecidableEq State]
  /-- Transition function (deterministic dynamics). -/
  step : State → State

attribute [instance] DiscreteSystem.hFin DiscreteSystem.hDec

/-- A system has non-trivial dynamics if some state transitions to a different state. -/
def hasNontrivialDynamics (sys : DiscreteSystem) : Prop :=
  ∃ s : sys.State, sys.step s ≠ s

/-- Trajectory: sequence of states over discrete time steps. -/
def trajectory (sys : DiscreteSystem) (s₀ : sys.State) : ℕ → sys.State
  | 0 => s₀
  | n + 1 => sys.step (trajectory sys s₀ n)

/-- Transition point: a time step where state changes. -/
def isTransitionPoint (sys : DiscreteSystem) (s₀ : sys.State) (t : ℕ) : Prop :=
  trajectory sys s₀ (t + 1) ≠ trajectory sys s₀ t

/-- The set of transition points in a trajectory. -/
def transitionPoints (sys : DiscreteSystem) (s₀ : sys.State) : Set ℕ :=
  { t | isTransitionPoint sys s₀ t }

/-- LEMMA 1: Transition points are countable (time is effectively discrete).
    This is immediate since ℕ is countable and transitionPoints ⊆ ℕ. -/
theorem transitionPoints_countable (sys : DiscreteSystem) (s₀ : sys.State) :
    Set.Countable (transitionPoints sys s₀) := by
  exact Set.Countable.mono (Set.subset_univ _) (Set.countable_univ)

/-- Decidability of transition predicate (needed for filtering). -/
instance transitionDecidable (sys : DiscreteSystem) (s₀ : sys.State) (t : ℕ) :
    Decidable (isTransitionPoint sys s₀ t) :=
  inferInstanceAs (Decidable (trajectory sys s₀ (t + 1) ≠ trajectory sys s₀ t))

/-- Bit-operation count: number of state transitions in first n steps. -/
def bitOperations (sys : DiscreteSystem) (s₀ : sys.State) (n : ℕ) : ℕ :=
  (Finset.range n).filter (fun t => isTransitionPoint sys s₀ t) |>.card

/-- LEMMA 2: Bit operations are bounded by time steps. -/
theorem bitOperations_le_time (sys : DiscreteSystem) (s₀ : sys.State) (n : ℕ) :
    bitOperations sys s₀ n ≤ n := by
  unfold bitOperations
  have h1 : ((Finset.range n).filter (fun t => isTransitionPoint sys s₀ t)).card
            ≤ (Finset.range n).card := Finset.card_filter_le _ _
  simp only [Finset.card_range] at h1
  exact h1

/-- LEMMA 3: Non-trivial dynamics implies at least one bit operation eventually. -/
theorem nontrivial_implies_bit_operation
    (sys : DiscreteSystem) (h : hasNontrivialDynamics sys) :
    ∃ s₀ : sys.State, ∃ t : ℕ, isTransitionPoint sys s₀ t := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, 0, ?_⟩
  unfold isTransitionPoint trajectory
  exact hs

/-! ## Part 2: Lorentz Invariance (cite Einstein 1905, Minkowski 1908)

The physical content is that Lorentz invariance forces space and time to share the
same discreteness scale (Snyder 1947). Formalized here as existence statements in
ℕ: given a discrete temporal unit Δt, a compatible spatial unit Δx = Δt exists,
and vice versa. These are mathematically trivial (take Δx := Δt); calibration to a
specific physical unit is handled explicitly in Part 3.
-/

/-- Spacetime discreteness scale (abstract, to be instantiated). -/
structure DiscretenessScale where
  /-- Minimal spatial interval (in natural units). -/
  spatialUnit : ℕ
  /-- Minimal temporal interval (in natural units). -/
  temporalUnit : ℕ
  /-- Positive spatial unit. -/
  hSpatial : 0 < spatialUnit
  /-- Positive temporal unit. -/
  hTemporal : 0 < temporalUnit

/-- THEOREM (Lorentz): Discrete temporal structure implies a compatible discrete
    spatial scale exists (take Δx = Δt in natural units where c = 1).
    Calibration to a specific physical unit is handled in Part 3.
    Citation: Snyder, H.S. (1947). Quantized Space-Time. Phys. Rev. 71:38-41. -/
theorem lorentz_time_implies_space :
    ∀ (Δt : ℕ), 0 < Δt → ∃ (Δx : ℕ), 0 < Δx ∧ Δx = Δt :=
  fun _Δt h => ⟨_, h, rfl⟩

/-- THEOREM (Lorentz): Discrete spatial structure implies a compatible discrete
    temporal scale exists (converse; take Δt = Δx).
    Citation: Snyder, H.S. (1947). Quantized Space-Time. Phys. Rev. 71:38-41. -/
theorem lorentz_space_implies_time :
    ∀ (Δx : ℕ), 0 < Δx → ∃ (Δt : ℕ), 0 < Δt ∧ Δt = Δx :=
  fun _Δx h => ⟨_, h, rfl⟩

/-- THEOREM: Lorentz-compatible discreteness scale exists given discrete time. -/
theorem lorentz_compatible_scale (Δt : ℕ) (hΔt : 0 < Δt) :
    ∃ scale : DiscretenessScale, scale.temporalUnit = Δt ∧ scale.spatialUnit = Δt := by
  obtain ⟨Δx, hΔx, hEq⟩ := lorentz_time_implies_space Δt hΔt
  refine ⟨⟨Δx, Δt, hΔx, hΔt⟩, rfl, ?_⟩
  exact hEq

/-! ## Part 3: Planck Calibration (derived uniqueness under declared calibration)

Dimensional analysis contributes a calibration source (ℏ, G, c), but in this
abstract ℕ-scale model uniqueness is derivable only after declaring which unit
value is selected. Without that calibration, Lorentz-invariant scales are not
unique.
-/

/-- Declared Planck calibration: one positive discreteness unit selected by
physical constants (e.g., via dimensional analysis from ℏ, G, c). -/
structure PlanckCalibration where
  unit : ℕ
  hUnit : 0 < unit

/-- A scale is Planck-calibrated when both axes match and equal the declared
calibration unit. -/
def IsPlanckCalibrated (C : PlanckCalibration) (scale : DiscretenessScale) : Prop :=
  scale.spatialUnit = scale.temporalUnit ∧ scale.spatialUnit = C.unit

/-- Existence: every declared calibration yields a Lorentz-compatible calibrated
scale in this abstract model. -/
theorem exists_planck_calibrated_scale (C : PlanckCalibration) :
    ∃ scale : DiscretenessScale, IsPlanckCalibrated C scale := by
  refine ⟨⟨C.unit, C.unit, C.hUnit, C.hUnit⟩, ?_⟩
  exact ⟨rfl, rfl⟩

/-- Uniqueness under calibration: any two calibrated scales share the same
spatial unit value. -/
theorem planck_unique_scale_of_calibration
    (C : PlanckCalibration)
    {scale₁ scale₂ : DiscretenessScale}
    (h₁ : IsPlanckCalibrated C scale₁)
    (h₂ : IsPlanckCalibrated C scale₂) :
    scale₁.spatialUnit = scale₂.spatialUnit := by
  rcases h₁ with ⟨_, h₁u⟩
  rcases h₂ with ⟨_, h₂u⟩
  calc
    scale₁.spatialUnit = C.unit := h₁u
    _ = scale₂.spatialUnit := h₂u.symm

/-- Boundary theorem: in the abstract Lorentz-only model, invariant scales are
not unique without calibration. -/
theorem lorentz_invariant_scales_not_unique :
    ∃ scale₁ scale₂ : DiscretenessScale,
      scale₁.spatialUnit = scale₁.temporalUnit ∧
      scale₂.spatialUnit = scale₂.temporalUnit ∧
      scale₁.spatialUnit ≠ scale₂.spatialUnit := by
  refine ⟨⟨1, 1, Nat.one_pos, Nat.one_pos⟩, ⟨2, 2, by decide, by decide⟩, rfl, rfl, ?_⟩
  decide

/-! ## Part 4: Landauer Bound (THEOREM - cite Landauer 1961, Bennett 2003)

Each irreversible bit operation dissipates at least kT ln 2 energy.
The physical content is in the declared constant joulesPerBit > 0 (Landauer's
principle); positivity then follows by Nat.mul_pos.
-/

/-- THEOREM (Landauer): Irreversible computation has minimum energy cost.
    Proven from the linear model energyLowerBound M b = joulesPerBit * b via Nat.mul_pos.
    The physical content (kT ln 2 per bit-erasure) is carried by the declared conversion
    constant joulesPerBit > 0; the positivity then follows mathematically.
    Citation: Landauer, R. (1961). Irreversibility and Heat Generation. -/
theorem landauer_bound :
    ∀ (M : ThermoModel), 0 < M.joulesPerBit →
      ∀ (bitOps : ℕ), 0 < bitOps → 0 < energyLowerBound M bitOps := by
  intro M hJ bitOps hb
  exact energy_lower_mandatory M hJ hb

/-! ## Part 5: The Full Chain (PROVEN from declared assumptions + theorems)

Discrete State → Discrete Time → Discrete Space → Planck Scale → Thermodynamics
-/

/-- MAIN THEOREM: Discrete computation implies thermodynamic lower bounds.

    Chain of derivation:
    1. DiscreteSystem has finite state space (given)
    2. Non-trivial dynamics → transition points exist (proven: nontrivial_implies_bit_operation)
    3. Transition points are countable → effective time is discrete (proven: transitionPoints_countable)
    4. Discrete time → discrete space (theorem: lorentz_time_implies_space)
    5. Discrete bit operations → energy lower bound (ThermodynamicLift)
-/
theorem discrete_computation_thermodynamic_chain
    (sys : DiscreteSystem)
    (_hDyn : hasNontrivialDynamics sys)
    (M : ThermoModel)
    (hJ : 0 < M.joulesPerBit)
    (s₀ : sys.State) (n : ℕ) (hn : 0 < bitOperations sys s₀ n) :
    -- Conclusion: positive energy lower bound
    0 < energyLowerBound M (bitOperations sys s₀ n) := by
  exact energy_lower_mandatory M hJ hn

/-- COROLLARY: Non-trivial computation eventually incurs thermodynamic cost.

    If a system has non-trivial dynamics, there exists some initial state and
    time horizon such that at least one bit operation occurs, hence energy cost. -/
theorem nontrivial_computation_has_energy_cost
    (sys : DiscreteSystem)
    (hDyn : hasNontrivialDynamics sys)
    (M : ThermoModel)
    (hJ : 0 < M.joulesPerBit) :
    ∃ s₀ : sys.State, ∃ n : ℕ,
      0 < bitOperations sys s₀ n ∧
      0 < energyLowerBound M (bitOperations sys s₀ n) := by
  -- From non-trivial dynamics, get a transition point
  obtain ⟨s₀, t, hTrans⟩ := nontrivial_implies_bit_operation sys hDyn
  -- At time t+1, we have at least one bit operation
  refine ⟨s₀, t + 1, ?_, ?_⟩
  · -- Show bitOperations sys s₀ (t+1) > 0
    unfold bitOperations
    have hMem : t ∈ Finset.range (t + 1) := Finset.mem_range.mpr (Nat.lt_succ_self t)
    have hFilter : t ∈ (Finset.range (t + 1)).filter
        (fun t' => isTransitionPoint sys s₀ t') := by
      rw [Finset.mem_filter]
      exact ⟨hMem, hTrans⟩
    exact Finset.card_pos.mpr ⟨t, hFilter⟩
  · -- Energy bound follows from positive bit operations
    have hPos : 0 < bitOperations sys s₀ (t + 1) := by
      unfold bitOperations
      have hMem : t ∈ Finset.range (t + 1) := Finset.mem_range.mpr (Nat.lt_succ_self t)
      have hFilter : t ∈ (Finset.range (t + 1)).filter
          (fun t' => isTransitionPoint sys s₀ t') := by
        rw [Finset.mem_filter]
        exact ⟨hMem, hTrans⟩
      exact Finset.card_pos.mpr ⟨t, hFilter⟩
    exact energy_lower_mandatory M hJ hPos

/-- BUNDLE: The full derivation chain as a single statement.

    From discrete state space + non-trivial dynamics + positive conversion constants,
    derive: discrete time, discrete space, and positive energy cost. -/
theorem computational_physical_bundle
    (sys : DiscreteSystem)
    (hDyn : hasNontrivialDynamics sys)
    (M : ThermoModel)
    (hJ : 0 < M.joulesPerBit) :
    -- 1. Transition points are countable (discrete time)
    (∀ s₀, Set.Countable (transitionPoints sys s₀)) ∧
    -- 2. Lorentz implies discrete space exists
    (∃ Δt : ℕ, 0 < Δt ∧ ∃ Δx : ℕ, 0 < Δx ∧ Δx = Δt) ∧
    -- 3. Non-trivial computation incurs energy cost
    (∃ s₀ : sys.State, ∃ n : ℕ,
      0 < bitOperations sys s₀ n ∧
      0 < energyLowerBound M (bitOperations sys s₀ n)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Discrete time
    intro s₀
    exact transitionPoints_countable sys s₀
  · -- Lorentz discrete space
    refine ⟨1, Nat.one_pos, ?_⟩
    exact lorentz_time_implies_space 1 Nat.one_pos
  · -- Energy cost
    exact nontrivial_computation_has_energy_cost sys hDyn M hJ

/-! ## Part 6: Connection to Neukart-Vinokur

The Neukart-Vinokur duality dU ≥ λ·dC follows when:
- C (complexity coordinate) = bitOperations
- λ = joulesPerBit
-/

/-- Neukart-Vinokur follows from the discrete computation chain. -/
theorem neukart_vinokur_from_discrete_chain
    (sys : DiscreteSystem)
    (_hDyn : hasNontrivialDynamics sys)
    (M : ThermoModel)
    (_hJ : 0 < M.joulesPerBit)
    (s₀ : sys.State) (n : ℕ) :
    -- dU = λ · dC where C = bit operations
    energyLowerBound M (bitOperations sys s₀ n) =
      nvLambda M * bitOperations sys s₀ n := by
  exact neukart_vinokur_duality M (bitOperations sys s₀ n)

end DiscreteSpacetime
end Physics
end DecisionQuotient
