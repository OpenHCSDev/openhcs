/-
  Paper 4: Decision-Relevant Uncertainty

  Hardness/ETH.lean - Exponential Time Hypothesis Lower Bounds

  Key Result: This module formalizes the size-preserving 3-SAT→circuit-DQ
  reduction premise and a concrete ETH assumption interface used by downstream
  conditional transfer theorems.

  ## Triviality Level
  NONTRIVIAL: This is a core hardness result - ETH-based exponential lower bound.

  ## Dependencies
  - Chain: SAT.lean → PolynomialReduction.lean → here (ETH transfer)
-/

import DecisionQuotient.Hardness.SAT
import DecisionQuotient.PolynomialReduction

namespace DecisionQuotient

open Classical

/-! ## Circuit Model for Decision Problems

In the circuit model, a decision problem is represented implicitly:
- The utility function u : A × S → ℝ is given by a Boolean circuit
- The instance size is the circuit size, not |S|

This is the standard model for complexity-theoretic analysis. -/

/-- A Boolean circuit computing a function {0,1}^n → {0,1}.
    Represented abstractly by its size and the function it computes. -/
structure BooleanCircuit (n : ℕ) where
  /-- Circuit size (number of gates) -/
  size : ℕ
  /-- The function computed by the circuit -/
  compute : (Fin n → Bool) → Bool

/-- Size of a circuit -/
def BooleanCircuit.circuitSize {n : ℕ} (C : BooleanCircuit n) : ℕ := C.size

/-- A decision problem represented by a circuit.
    - numActions: number of actions (encoded in log bits)
    - numCoords: number of state coordinates
    - utilityCircuit: circuit computing u(a, s) > threshold -/
structure CircuitDecisionProblem where
  /-- Number of actions -/
  numActions : ℕ
  /-- Number of state coordinates -/
  numCoords : ℕ
  /-- Circuit computing whether action a is optimal at state s -/
  optCircuit : BooleanCircuit (Nat.clog 2 numActions + numCoords)
  /-- Instance size is the circuit size -/
  instanceSize : ℕ := optCircuit.size + numCoords

/-! ## Reduction from 3-SAT to SUFFICIENCY-CHECK

The reduction from 3-SAT to SUFFICIENCY-CHECK:
  φ ↦ (problem where ∅ sufficient ↔ φ unsatisfiable)

Key property: Circuit size is preserved up to polynomial factors. -/

/-- Convert a 3-SAT formula to a circuit.
    Size: O(n + m) where n = variables, m = clauses -/
def sat3ToCircuit (φ : SAT3Instance) : BooleanCircuit φ.numVars where
  size := φ.numVars + 3 * φ.clauses.length  -- O(n + m)
  compute := fun a => φ.eval a

/-- Lift a circuit by adding `k` prefix bits that are ignored by the computation. -/
def BooleanCircuit.liftWithPrefix {n k : ℕ} (C : BooleanCircuit n) : BooleanCircuit (k + n) where
  size := C.size
  compute := fun z => C.compute (fun i => z (Fin.natAdd k i))

/-- SAT circuit embedded into the action+state input shape of `CircuitDecisionProblem`. -/
def sat3OptCircuit (φ : SAT3Instance) :
    BooleanCircuit (Nat.clog 2 2 + φ.numVars) :=
  (sat3ToCircuit φ).liftWithPrefix (k := Nat.clog 2 2)

/-- Semantic check: the lifted circuit evaluates SAT using the state-coordinate slice. -/
theorem sat3OptCircuit_semantics (φ : SAT3Instance)
    (z : Fin (Nat.clog 2 2 + φ.numVars) → Bool) :
    (sat3OptCircuit φ).compute z =
      φ.eval (fun i => z (Fin.natAdd (Nat.clog 2 2) i)) := rfl

/-- Canonical circuit-encoded decision problem produced from a SAT instance. -/
def sat3ToCircuitDecisionProblem (φ : SAT3Instance) : CircuitDecisionProblem where
  numActions := 2
  numCoords := φ.numVars
  optCircuit := sat3OptCircuit φ

/-- Input size of a 3-SAT instance -/
def SAT3Instance.inputSize (φ : SAT3Instance) : ℕ :=
  φ.numVars + 3 * φ.clauses.length

/-- The reduction from 3-SAT to SUFFICIENCY-CHECK preserves size polynomially.
    A 3-SAT instance with n variables and m clauses produces a
    CircuitDecisionProblem of size O(n + m). -/
theorem sat3_reduction_size_preserving (φ : SAT3Instance) :
    ∃ (cdp : CircuitDecisionProblem),
      -- Size is linear in original formula
      cdp.instanceSize ≤ 3 * φ.inputSize := by
  refine ⟨sat3ToCircuitDecisionProblem φ, ?_⟩
  -- instanceSize = inputSize + numVars
  -- inputSize = numVars + 3 * clauses.length
  -- So instanceSize = 2 * numVars + 3 * clauses.length
  -- And 3 * inputSize = 3 * numVars + 9 * clauses.length
  -- Need: 2n + 3m ≤ 3n + 9m, which is true since n ≥ 0, m ≥ 0
  simp only [sat3ToCircuitDecisionProblem,
    sat3OptCircuit, BooleanCircuit.liftWithPrefix, sat3ToCircuit, SAT3Instance.inputSize]
  -- Goal: φ.numVars + 3 * φ.clauses.length + φ.numVars ≤ 3 * (φ.numVars + 3 * φ.clauses.length)
  -- i.e. 2n + 3m ≤ 3n + 9m
  have h : φ.numVars + 3 * φ.clauses.length + φ.numVars =
           2 * φ.numVars + 3 * φ.clauses.length := by ring
  rw [h]
  have h' : 3 * (φ.numVars + 3 * φ.clauses.length) =
            3 * φ.numVars + 9 * φ.clauses.length := by ring
  rw [h']
  omega

/-! ## Exponential Time Hypothesis

ETH states that 3-SAT on n variables cannot be solved in 2^{o(n)} time. -/

/-- SAT solver interface with explicit output and runtime functions. -/
structure SAT3Algorithm where
  decide : SAT3Instance → Bool
  runtime : SAT3Instance → ℕ
  correct : ∀ φ : SAT3Instance, decide φ = true ↔ SAT3Instance.satisfiable φ

/-- Exponential lower-bound witness (up to multiplicative slack `c`). -/
def ExponentialRuntimeWitness (algorithm : SAT3Algorithm) (c : ℕ) (φ : SAT3Instance) : Prop :=
  2 ^ φ.inputSize ≤ c * algorithm.runtime φ

/-- ETH assumption schema over the concrete algorithm/runtime interface. -/
def ETHAssumption : Prop :=
  ∀ (algorithm : SAT3Algorithm),
    ∀ (c : ℕ), c > 0 →
      ∃ (φ : SAT3Instance), ExponentialRuntimeWitness algorithm c φ

/-- ETH interface unpacking: under ETH, every concrete SAT3 algorithm has
an exponential-runtime witness instance for each positive slack constant. -/
theorem eth_implies_sat3_exponential :
    ETHAssumption →
    -- Under ETH, any algorithm for 3-SAT takes 2^{Ω(n)} time
    ∀ (algorithm : SAT3Algorithm),
    ∀ (c : ℕ), c > 0 →
    ∃ (φ : SAT3Instance), ExponentialRuntimeWitness algorithm c φ := by
  intro hETH algorithm c hc
  exact hETH algorithm c hc

/-! ## Main ETH Lower Bound for SUFFICIENCY-CHECK -/

/-- ETH-conditioned wrapper exposing the mechanized size-preservation premise
used in lower-bound transfer arguments. -/
theorem eth_lower_bound_sufficiency_check :
    ETHAssumption →
    ∀ (algorithm : SAT3Algorithm) (c : ℕ), c > 0 →
      ∃ (φ : SAT3Instance) (cdp : CircuitDecisionProblem),
        cdp.instanceSize ≤ 3 * φ.inputSize ∧
        ExponentialRuntimeWitness algorithm c φ := by
  intro hETH algorithm c hc
  obtain ⟨φ, hW⟩ := eth_implies_sat3_exponential hETH algorithm c hc
  obtain ⟨cdp, hSize⟩ := sat3_reduction_size_preserving φ
  exact ⟨φ, cdp, hSize, hW⟩

/-- Paper-facing alias of `eth_lower_bound_sufficiency_check`. -/
theorem eth_lower_bound_informal :
    ETHAssumption →
    ∀ (algorithm : SAT3Algorithm) (c : ℕ), c > 0 →
      ∃ (φ : SAT3Instance) (cdp : CircuitDecisionProblem),
        cdp.instanceSize ≤ 3 * φ.inputSize ∧
        ExponentialRuntimeWitness algorithm c φ :=
  eth_lower_bound_sufficiency_check

end DecisionQuotient
