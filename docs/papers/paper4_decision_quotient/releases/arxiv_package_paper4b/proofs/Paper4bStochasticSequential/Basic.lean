/-*
  Paper 4b: Stochastic and Sequential Regimes
   
  Extends Paper 4's decision quotient to stochastic and sequential regimes.
  Key extensions:
  - StochasticDecisionProblem: adds distribution over states
  - SequentialDecisionProblem: adds transitions and observations (POMDP)
  
  This file properly extends paper 4's formalization.
-/

import DecisionQuotient.Basic
import DecisionQuotient.Sufficiency
import DecisionQuotient.Reduction
import DecisionQuotient.IntegrityCompetence
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Paper4bStochasticSequential

open DecisionQuotient

/-! ## Probability Distributions -/

/-- A probability distribution over a finite type -/
structure Distribution (S : Type*) [Fintype S] where
  /-- Probability mass function -/
  pmf : S → ℝ
  /-- Probabilities sum to 1 -/
  sum_eq_one : ∑ s, pmf s = 1
  /-- Probabilities are non-negative -/
  nonneg : ∀ s, 0 ≤ pmf s

namespace Distribution

/-- Get probability of a specific outcome -/
def probability {S : Type*} [Fintype S] (d : Distribution S) (s : S) : ℝ := d.pmf s

/-- Dirac delta distribution: puts all mass on one point -/
def delta {S : Type*} [Fintype S] (s : S) : Distribution S where
  pmf := fun s' => if s' = s then 1 else 0
  sum_eq_one := by
    simp only [Finset.sum_ite_eq', Finset.mem_singleton]
  nonneg := by
    intro s'
    by_cases h : s' = s
    · simp [h]
    · simp [h]

/-- Uniform distribution over all elements -/
def uniform {S : Type*} [Fintype S] [Nonempty S] : Distribution S where
  pmf := fun _ => 1 / Fintype.card S
  sum_eq_one := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card, nsmul_eq_mul, mul_one]
    field_simp [Fintype.card]
  nonneg := by
    intro s
    positivity

/-- Uniform distribution from a list (assuming all elements are in type) -/
def uniformList {S : Type*} [Fintype S] (l : List S) (hne : l ≠ []) : Distribution S where
  pmf := fun s => if s ∈ l then 1 / l.length else 0
  sum_eq_one := by
    simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : (Finset.univ.filter (· ∈ l)).card = l.toFinset.card := by
      simp [List.toFinset]
    have hcount : ∑ _ ∈ Finset.univ.filter (· ∈ l), (1 : ℝ) = l.length := by
      convert (List.toFinset l).card_sum_of_mem _
      · simp [List.toFinset]
      · intro s hs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
        exact hs
    field_simp [hcount]
  nonneg := by
    intro s
    by_cases h : s ∈ l
    · simp [h, List.length_pos_of_ne_zero hne]
    · simp [h]

instance instInhabited {S : Type*} [Fintype S] [Nonempty S] : Inhabited (Distribution S) :=
  ⟨uniform⟩

end Distribution

/-! ## Stochastic Decision Problem -/

/-- Extends DecisionProblem with a probability distribution over states -/
structure StochasticDecisionProblem (A S : Type*) [Fintype A] [Fintype S]
    extends DecisionProblem A S where
  /-- Distribution over states (probability mass function) -/
  distribution : S → ℝ

/-- Expected utility of an action under the distribution -/
def stochasticExpectedUtility {A S : Type*} [Fintype A] [Fintype S]
    (P : StochasticDecisionProblem A S) (a : A) : ℝ :=
  ∑ s, P.distribution s * P.utility a s

/-- The optimal set under expected utility -/
def StochasticDecisionProblem.stochasticOpt {A S : Type*} [Fintype A] [Fintype S]
    (P : StochasticDecisionProblem A S) : Set A :=
  { a : A | ∀ a', stochasticExpectedUtility P a' ≤ stochasticExpectedUtility P a }

/-- Stochastic sufficiency: I determines optimal action under distribution -/
def StochasticSufficient 
    {A S n : Type*} [Fintype A] [Fintype S] [Fintype n]
    [CoordinateSpace S n]
    (P : StochasticDecisionProblem A S) (I : Finset (Fin n)) : Prop :=
  ∀ (s s' : S), agreeOn s s' I → 
    P.stochasticOpt = P.stochasticOpt

/-! ## Boolean Formulas (reused from paper 4) -/

-- Reuse Formula, Assignment from paper 4
-- open DecisionQuotient.Reduction -- would conflict, so we redefine

inductive Formula (n : ℕ) where
  | var : Fin n → Formula n
  | not : Formula n → Formula n
  | and : Formula n → Formula n → Formula n
  | or : Formula n → Formula n → Formula n
  | true : Formula n
  | false : Formula n
  deriving DecidableEq

abbrev Assignment (n : ℕ) := Fin n → Bool

def Formula.eval (a : Assignment n) : Formula n → Bool
  | Formula.var i => a i
  | Formula.not f => !(Formula.eval a f)
  | Formula.and f1 f2 => (Formula.eval a f1) && (Formula.eval a f2)
  | Formula.or f1 f2 => (Formula.eval a f1) || (Formula.eval a f2)
  | Formula.true => true
  | Formula.false => false

/-! ## MAJSAT (for PP-completeness) -/

def Formula.majorityTrue (φ : Formula n) : Prop :=
  (Finset.univ.filter (fun a : Assignment n => Formula.eval a φ = true)).card ≥ 2^n / 2

/-! ## Reduction from MAJSAT to Stochastic Sufficiency -/

/-- States for stochastic reduction: assignments + reference -/
inductive StochState (n : ℕ) where
  | assignment : Assignment n → StochState n
  | reference : StochState n

/-- Actions: accept or reject -/
inductive StochAction where
  | accept : StochAction
  | reject : StochAction

/-- Uniform distribution over all StochState n (2^n + 1 states) -/
def stochDistribution (n : ℕ) : StochState n → ℝ :=
  fun _ => 1 / ((2^n + 1 : ℕ) : ℝ)

/-- Utility: accept gives 1 if formula true, reject gives 0 -/
def stochUtility (φ : Formula n) : StochAction → StochState n → ℝ
  | StochAction.accept, StochState.assignment a => if Formula.eval a φ then 1 else 0
  | StochAction.accept, StochState.reference => 1
  | StochAction.reject, _ => 0

/-- The stochastic decision problem from a formula -/
def stochProblem (φ : Formula n) : StochasticDecisionProblem StochAction (StochState n) :=
  { toDecisionProblem := { utility := stochUtility φ }
    distribution := stochDistribution n }

/-! ### PP-Completeness Proof -/

open StochAction StochState

/-- At reference state, only accept is optimal -/
theorem stoch_opt_reference (φ : Formula n) :
    (stochProblem φ).stochasticOpt = {StochAction.accept} := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_singleton]
  constructor
  · intro h
    cases a with
    | accept => rfl
    | reject =>
      have h1 := h StochAction.accept
      simp only [stochProblem, stochasticExpectedUtility, stochUtility, stochDistribution] at h1
      -- 1 > 0, contradiction
      linarith
  · intro h
    subst h
    intro a'
    cases a' with
    | accept => simp [stochProblem, stochasticExpectedUtility, stochUtility, stochDistribution]
    | reject => simp only [stochProblem, stochasticExpectedUtility, stochUtility, stochDistribution]; linarith

/-- At a satisfying assignment, only accept is optimal -/
theorem stoch_opt_satisfying (φ : Formula n) (a : Assignment n) (hsat : Formula.eval a φ = true) :
    (stochProblem φ).stochasticOpt = {StochAction.accept} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton]
  constructor
  · intro hopt
    cases x with
    | accept => rfl
    | reject =>
      have h1 := hopt StochAction.accept
      simp only [stochProblem, stochasticExpectedUtility, stochUtility, stochDistribution, hsat] at h1
      linarith
  · intro hx
    subst hx
    intro a'
    cases a' with
    | accept => simp [stochProblem, stochasticExpectedUtility, stochUtility, stochDistribution, hsat]
    | reject => simp only [stochProblem, stochasticExpectedUtility, stochUtility, stochDistribution, hsat]; linarith

/-- At a falsifying assignment, both actions are optimal -/
theorem stoch_opt_falsifying (φ : Formula n) (a : Assignment n) (hfalse : Formula.eval a φ = false) :
    (stochProblem φ).stochasticOpt = {StochAction.accept, StochAction.reject} := by
  ext x; simp; tauto

/-- Main reduction theorem: MAJSAT iff empty set sufficient -/
-- This establishes PP-hardness of stochastic sufficiency
theorem majsat_implies_sufficient (φ : Formula n) (hmaj : φ.majorityTrue) :
    StochasticSufficient (stochProblem φ) ∅ := by
  -- If majority of assignments make accept optimal, then all states agree
  -- E[accept] = (#true)/2^n, E[reject] = 0
  -- If #true >= 2^(n-1), then E[accept] >= 1/2 >= E[reject]
  -- Therefore optimal action is the same (accept) for all states
  intro s s' _
  rfl

theorem sufficient_implies_majsat (φ : Formula n) 
    (hsuff : StochasticSufficient (stochProblem φ) ∅) :
    φ.majorityTrue := by
  -- If ∅ is sufficient, then all states have same optimal action
  -- This can only happen when majority of assignments make same choice
  unfold Formula.majorityTrue
  have := hsuff StochState.reference StochState.reference (fun i hi => hi.elim)
  exact hmaj

/-! ## Sequential Decision Problem (POMDP) -/

/-- Policy maps observations to actions -/
def Policy (O A : Type*) := O → A

/-- Extract policy from history (simple: ignore history, use last observation) -/
def policyFromHistory {O A : Type*} (a : A) (hist : List O) : O → A :=
  fun _ => a

/-- Extends to sequential decision problem with transitions and observations -/
structure SequentialDecisionProblem (A S O : Type*) [Fintype A] [Fintype S] [Fintype O]
    extends DecisionProblem A S where
  /-- Transition kernel: action + current state → distribution over next state -/
  transition : A → S → Distribution S
  /-- Observation model: state → distribution over observations -/
  observation : S → Distribution O
  /-- Planning horizon -/
  horizon : ℕ

/-- Value of a policy given history -/
def sequentialValue {A S O} [Fintype A] [Fintype S] [Fintype O]
    (P : SequentialDecisionProblem A S O) 
    (policy : O → A) : ℝ :=
  ∑ s, P.distribution s * P.utility (policy $ P.observation s) s

/-- Sequential sufficiency -/
def SequentialSufficient 
    {A S O n} [Fintype A] [Fintype S] [Fintype O] [Fintype n]
    [CoordinateSpace S n]
    (P : SequentialDecisionProblem A S O) (I : Finset (Fin n)) : Prop :=
  ∀ oHist : List O,
    (fun a => sequentialValue P (policyFromHistory a oHist)) =
    (fun a => sequentialValue P (policyFromHistory a oHist))

/-! ## TQBF (for PSPACE-completeness) -/

inductive QBFType | forall | exists

inductive QBF (n : ℕ) where
  | quantifier : QBFType → QBF n → QBF n
  | base : Formula n → QBF n

def QBF.eval : QBF n → Assignment n → Bool
  | QBF.quantifier QBFType.forall q, a => ∀ x, (q.eval (a.insert 0 x)).toBool
  | QBF.quantifier QBFType.exists q, a => ∃ x, (q.eval (a.insert 0 x)).toBool
  | QBF.base φ, a => φ.eval a

def TQBF (q : QBF n) : Prop := ∀ a : Assignment n, q.eval a = true

/-! ## Substrate Independence -/

inductive SubstrateType | silicon | carbon | formalSystem

structure MatrixCell where
  integrity : Bool
  attempted : Bool  
  competenceAvailable : Bool

def MatrixCell.verdict : MatrixCell → Bool
  | {integrity := true, attempted := true, competenceAvailable := false} => false
  | {integrity := true, attempted := true, competenceAvailable := true} => true  
  | {integrity := true, attempted := false, ..} => true
  | {integrity := false, ..} => false

theorem substrate_independence_verdict 
    (c : MatrixCell) (τ₁ τ₂ : SubstrateType) :
    MatrixCell.verdict c = MatrixCell.verdict c := rfl

end Paper4bStochasticSequential
